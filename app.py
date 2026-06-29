from flask import Flask, render_template, request, jsonify
import requests
import re
import time
import sqlite3
import smtplib
import os
import uuid
import json
import xml.etree.ElementTree as ET
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
from dotenv import load_dotenv

load_dotenv()

app = Flask(__name__)

DB_PATH = 'tracker.db'
CACHE_TTL = 3600
price_cache = {}

HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120.0'
}


# ── Database ──────────────────────────────────────────────────────────────────

def init_db():
    conn = sqlite3.connect(DB_PATH)
    conn.execute('''
        CREATE TABLE IF NOT EXISTS alerts (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            email TEXT NOT NULL,
            market_hash_name TEXT NOT NULL,
            skin_name TEXT NOT NULL,
            threshold_price REAL NOT NULL,
            current_price REAL DEFAULT 0,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP,
            last_checked TEXT,
            triggered INTEGER DEFAULT 0
        )
    ''')
    conn.execute('''
        CREATE TABLE IF NOT EXISTS snapshots (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            steam_id TEXT NOT NULL,
            total_value REAL NOT NULL,
            item_count INTEGER NOT NULL,
            recorded_at TEXT DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    conn.execute('''
        CREATE TABLE IF NOT EXISTS shares (
            id TEXT PRIMARY KEY,
            steam_id TEXT NOT NULL,
            total_value REAL NOT NULL,
            item_count INTEGER NOT NULL,
            items_json TEXT NOT NULL,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP
        )
    ''')
    conn.execute('''
        CREATE TABLE IF NOT EXISTS wishlist (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            email TEXT NOT NULL,
            market_hash_name TEXT NOT NULL,
            skin_name TEXT NOT NULL,
            target_price REAL NOT NULL,
            current_price REAL DEFAULT 0,
            created_at TEXT DEFAULT CURRENT_TIMESTAMP,
            last_checked TEXT,
            triggered INTEGER DEFAULT 0
        )
    ''')
    conn.commit()
    conn.close()

init_db()


# ── Steam helpers ─────────────────────────────────────────────────────────────

def resolve_vanity_url(username):
    for url in [
        f"https://steamcommunity.com/id/{username}/?xml=1",
        f"https://steamcommunity.com/id/{username.lower()}/?xml=1",
    ]:
        try:
            r = requests.get(url, headers=HEADERS, timeout=10)
            if r.status_code == 200 and '<steamID64>' in r.text:
                root = ET.fromstring(r.text)
                steam_id = root.findtext('steamID64')
                if steam_id and steam_id.isdigit():
                    return steam_id
        except Exception:
            pass
    return None


def extract_steam_id(user_input):
    user_input = user_input.strip().rstrip('/')

    if re.fullmatch(r'\d{17}', user_input):
        return user_input, None

    match = re.search(r'/profiles/(\d{17})', user_input)
    if match:
        return match.group(1), None

    match = re.search(r'steamcommunity\.com/id/([^/?#]+)', user_input)
    if match:
        steam_id = resolve_vanity_url(match.group(1))
        if steam_id:
            return steam_id, None
        return None, f"Could not resolve that Steam username. Try your numeric profile URL: steamcommunity.com/profiles/YOUR_ID"

    if re.fullmatch(r'[a-zA-Z0-9_-]+', user_input) and len(user_input) >= 2:
        steam_id = resolve_vanity_url(user_input)
        if steam_id:
            return steam_id, None

    return None, "Invalid Steam URL. Paste your Steam profile URL — e.g. steamcommunity.com/profiles/76561198..."


def fetch_inventory(steam_id):
    all_assets = []
    all_descriptions = {}
    last_assetid = None

    for _ in range(20):
        params = {'l': 'english'}
        if last_assetid:
            params['start_assetid'] = last_assetid

        try:
            r = requests.get(
                f"https://steamcommunity.com/inventory/{steam_id}/730/2",
                params=params, headers=HEADERS, timeout=15
            )
        except Exception as e:
            return None, f"Request failed: {e}"

        if r.status_code == 403:
            return None, "Inventory is private. Go to Steam → Edit Profile → Privacy Settings → set Inventory to Public."
        if r.status_code == 401:
            return None, "Inventory is private."
        if r.status_code != 200:
            return None, f"Steam returned HTTP {r.status_code}. Try again in a moment."

        try:
            data = r.json()
        except Exception:
            return None, "Steam returned an unreadable response. Try again."

        if not data or not data.get('success'):
            err = data.get('Error', '') if data else ''
            if 'private' in err.lower():
                return None, "Inventory is private. Go to Steam → Edit Profile → Privacy Settings → set Inventory to Public."
            return None, f"Steam could not load this inventory. ({err or 'unknown reason'})"

        all_assets.extend(data.get('assets', []))
        for desc in data.get('descriptions', []):
            key = f"{desc['classid']}_{desc['instanceid']}"
            all_descriptions[key] = desc

        if not data.get('more_items'):
            break
        last_assetid = data.get('last_assetid')
        time.sleep(0.5)

    return {'success': 1, 'assets': all_assets, 'descriptions': list(all_descriptions.values())}, None


def fetch_price(market_hash_name):
    now = time.time()
    cached = price_cache.get(market_hash_name)
    if cached and now - cached['ts'] < CACHE_TTL:
        return market_hash_name, cached['price']

    url = "https://steamcommunity.com/market/priceoverview/"
    params = {'currency': 1, 'appid': 730, 'market_hash_name': market_hash_name}

    for attempt in range(3):
        try:
            r = requests.get(url, params=params, headers=HEADERS, timeout=8)
            if r.status_code == 429:
                time.sleep(2 * (attempt + 1))
                continue
            if r.status_code == 200:
                data = r.json()
                if data.get('success'):
                    raw = data.get('lowest_price') or data.get('median_price') or '$0.00'
                    price = float(re.sub(r'[^\d.]', '', raw) or '0')
                    price_cache[market_hash_name] = {'price': price, 'ts': now}
                    return market_hash_name, price
                break
        except Exception:
            pass
        time.sleep(0.3)

    return market_hash_name, 0.0


def parse_items(inv_data):
    descriptions = {
        f"{d['classid']}_{d['instanceid']}": d
        for d in inv_data.get('descriptions', [])
    }
    seen = {}
    for asset in inv_data.get('assets', []):
        key = f"{asset['classid']}_{asset['instanceid']}"
        desc = descriptions.get(key, {})
        if not desc.get('marketable'):
            continue
        mhn = desc.get('market_hash_name', '')
        if not mhn:
            continue

        rarity_color = '#b0c3d9'
        wear = ''
        for tag in desc.get('tags', []):
            cat = tag.get('category', '')
            if cat == 'Rarity':
                rarity_color = f"#{tag.get('color', 'b0c3d9')}"
            elif cat == 'Exterior':
                wear = tag.get('localized_tag_name', '')

        icon = ''
        if desc.get('icon_url'):
            icon = f"https://steamcommunity-a.akamaihd.net/economy/image/{desc['icon_url']}/128x128"

        if mhn in seen:
            seen[mhn]['amount'] += 1
        else:
            seen[mhn] = {
                'name': desc.get('name', 'Unknown'),
                'market_hash_name': mhn,
                'icon': icon,
                'rarity_color': rarity_color,
                'wear': wear,
                'amount': 1,
                'price': 0.0,
                'total': 0.0,
            }
    return list(seen.values())


def search_steam_market(query):
    """Search Steam market, return (market_hash_name, current_price)."""
    url = "https://steamcommunity.com/market/search/render/"
    params = {'query': query, 'appid': 730, 'norender': 1, 'count': 5, 'currency': 1}
    try:
        r = requests.get(url, params=params, headers=HEADERS, timeout=10)
        if r.status_code == 200:
            data = r.json()
            results = data.get('results', [])
            if results:
                top = results[0]
                mhn = top.get('asset_description', {}).get('market_hash_name', '')
                price_str = top.get('sell_price_text', '$0.00')
                price = float(re.sub(r'[^\d.]', '', price_str) or '0')
                return mhn, price
    except Exception:
        pass
    return None, 0.0


def save_snapshot(steam_id, total, count):
    conn = sqlite3.connect(DB_PATH)
    today = datetime.now().strftime('%Y-%m-%d')
    last = conn.execute(
        "SELECT recorded_at FROM snapshots WHERE steam_id=? ORDER BY recorded_at DESC LIMIT 1",
        (steam_id,)
    ).fetchone()
    if not last or last[0][:10] != today:
        conn.execute(
            "INSERT INTO snapshots (steam_id, total_value, item_count) VALUES (?,?,?)",
            (steam_id, total, count)
        )
        conn.commit()
    conn.close()


# ── Email ─────────────────────────────────────────────────────────────────────

def send_alert_email(to_email, skin_name, threshold, current_price):
    gmail_user = os.getenv('GMAIL_USER')
    gmail_pass = os.getenv('GMAIL_APP_PASSWORD')
    if not gmail_user or not gmail_pass:
        print('[alerts] Email not configured — set GMAIL_USER and GMAIL_APP_PASSWORD in .env')
        return False

    market_url = f"https://steamcommunity.com/market/listings/730/{requests.utils.quote(skin_name)}"
    html = f"""
    <div style="font-family:Inter,sans-serif;background:#080c18;color:#e2e8f0;padding:40px;max-width:520px;margin:0 auto;border-radius:16px;">
      <h2 style="color:#f97316;margin:0 0 4px;">CS2 Price Alert</h2>
      <p style="color:#6b7280;margin:0 0 28px;font-size:14px;">Your tracked item hit your target price</p>
      <div style="background:#111827;border:1px solid #1e2d3d;border-top:3px solid #f97316;border-radius:12px;padding:24px;margin-bottom:24px;">
        <p style="font-size:17px;font-weight:700;margin:0 0 8px;color:#fff;">{skin_name}</p>
        <p style="font-size:28px;font-weight:900;color:#34d399;margin:0;">${current_price:.2f}</p>
        <p style="color:#4b5563;font-size:13px;margin:8px 0 0;">Your alert threshold: ${threshold:.2f}</p>
      </div>
      <a href="{market_url}" style="display:inline-block;background:#f97316;color:#fff;padding:14px 28px;border-radius:10px;text-decoration:none;font-weight:700;font-size:14px;">View on Steam Market →</a>
      <p style="color:#374151;font-size:11px;margin-top:28px;">CS2 Tracker · This alert has been deactivated after firing.</p>
    </div>
    """
    msg = MIMEMultipart('alternative')
    msg['Subject'] = f"[CS2 Tracker] {skin_name} dropped to ${current_price:.2f}"
    msg['From'] = gmail_user
    msg['To'] = to_email
    msg.attach(MIMEText(html, 'html'))
    try:
        with smtplib.SMTP_SSL('smtp.gmail.com', 465) as smtp:
            smtp.login(gmail_user, gmail_pass)
            smtp.sendmail(gmail_user, to_email, msg.as_string())
        return True
    except Exception as e:
        print(f'[alerts] Email failed: {e}')
        return False


# ── Routes ────────────────────────────────────────────────────────────────────

@app.route('/')
def index():
    return render_template('index.html')


@app.route('/track', methods=['POST'])
def track():
    profile = request.form.get('profile', '').strip()
    steam_id, err = extract_steam_id(profile)
    if not steam_id:
        return render_template('index.html', error=err)

    inv_data, err = fetch_inventory(steam_id)
    if not inv_data:
        return render_template('index.html', error=err)

    items = parse_items(inv_data)
    if not items:
        return render_template('index.html',
            error="No marketable CS2 items found. Your inventory may be empty or everything is untradable.")

    unique_names = list({item['market_hash_name'] for item in items})
    prices = {}
    with ThreadPoolExecutor(max_workers=4) as executor:
        futures = {executor.submit(fetch_price, name): name for name in unique_names}
        for future in as_completed(futures):
            name, price = future.result()
            prices[name] = price

    total = 0.0
    for item in items:
        p = prices.get(item['market_hash_name'], 0.0)
        item['price'] = p
        item['total'] = round(p * item['amount'], 2)
        total += item['total']

    items.sort(key=lambda x: x['total'], reverse=True)
    total = round(total, 2)

    save_snapshot(steam_id, total, len(items))

    conn = sqlite3.connect(DB_PATH)
    history = conn.execute(
        "SELECT total_value, recorded_at FROM snapshots WHERE steam_id=? ORDER BY recorded_at ASC",
        (steam_id,)
    ).fetchall()
    conn.close()

    return render_template('dashboard.html',
        items=items,
        total=total,
        steam_id=steam_id,
        count=len(items),
        top_item=items[0] if items else None,
        history=history)


# ── Share ─────────────────────────────────────────────────────────────────────

@app.route('/share/create', methods=['POST'])
def create_share():
    data = request.get_json()
    share_id = str(uuid.uuid4())[:8]
    items_to_store = [
        {k: v for k, v in item.items() if k != 'market_hash_name'}
        for item in (data.get('items') or [])
    ]
    conn = sqlite3.connect(DB_PATH)
    conn.execute(
        "INSERT INTO shares (id, steam_id, total_value, item_count, items_json) VALUES (?,?,?,?,?)",
        (share_id, data.get('steam_id', ''), data.get('total_value', 0),
         data.get('item_count', 0), json.dumps(items_to_store))
    )
    conn.commit()
    conn.close()
    return jsonify({'share_id': share_id})


@app.route('/share/<share_id>')
def view_share(share_id):
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    share = conn.execute("SELECT * FROM shares WHERE id=?", (share_id,)).fetchone()
    conn.close()
    if not share:
        return render_template('index.html', error="Share link not found or expired.")
    items = json.loads(share['items_json'])
    return render_template('share.html', share=share, items=items)


# ── Portfolio history ─────────────────────────────────────────────────────────

@app.route('/api/history/<steam_id>')
def get_history(steam_id):
    conn = sqlite3.connect(DB_PATH)
    rows = conn.execute(
        "SELECT total_value, item_count, recorded_at FROM snapshots WHERE steam_id=? ORDER BY recorded_at ASC",
        (steam_id,)
    ).fetchall()
    conn.close()
    return jsonify([{'value': r[0], 'count': r[1], 'date': r[2][:10]} for r in rows])


# ── Wishlist ──────────────────────────────────────────────────────────────────

@app.route('/wishlist')
def wishlist():
    email = request.args.get('email', '').strip()
    items = []
    if email:
        conn = sqlite3.connect(DB_PATH)
        conn.row_factory = sqlite3.Row
        items = conn.execute(
            "SELECT * FROM wishlist WHERE email=? ORDER BY created_at DESC",
            (email,)
        ).fetchall()
        conn.close()
    return render_template('wishlist.html', items=items, email=email)


@app.route('/api/market/search')
def market_search():
    q = request.args.get('q', '').strip()
    if len(q) < 3:
        return jsonify([])
    url = "https://steamcommunity.com/market/search/render/"
    params = {'query': q, 'appid': 730, 'norender': 1, 'count': 8, 'currency': 1}
    try:
        r = requests.get(url, params=params, headers=HEADERS, timeout=8)
        if r.status_code == 200:
            results = r.json().get('results', [])
            return jsonify([{
                'name': res.get('name', ''),
                'mhn': res.get('asset_description', {}).get('market_hash_name', ''),
                'price': res.get('sell_price_text', ''),
                'icon': 'https://steamcommunity-a.akamaihd.net/economy/image/' +
                        res.get('asset_description', {}).get('icon_url', '') + '/64x64'
                        if res.get('asset_description', {}).get('icon_url') else ''
            } for res in results if res.get('asset_description', {}).get('market_hash_name')])
    except Exception:
        pass
    return jsonify([])


@app.route('/wishlist/add', methods=['POST'])
def add_wishlist():
    data = request.get_json()
    email = (data.get('email') or '').strip()
    mhn = (data.get('mhn') or '').strip()
    skin_name = (data.get('skin_name') or '').strip()
    target_price = data.get('target_price')
    current_price = data.get('current_price', 0)

    if not all([email, mhn, skin_name, target_price]):
        return jsonify({'success': False, 'error': 'Missing fields'}), 400
    if '@' not in email:
        return jsonify({'success': False, 'error': 'Invalid email'}), 400
    try:
        target_price = float(target_price)
    except (ValueError, TypeError):
        return jsonify({'success': False, 'error': 'Invalid price'}), 400

    conn = sqlite3.connect(DB_PATH)
    conn.execute(
        "INSERT INTO wishlist (email, market_hash_name, skin_name, target_price, current_price, created_at) VALUES (?,?,?,?,?,?)",
        (email, mhn, skin_name, target_price, float(current_price), datetime.now().isoformat())
    )
    conn.commit()
    conn.close()
    return jsonify({'success': True})


@app.route('/wishlist/delete/<int:item_id>', methods=['POST'])
def delete_wishlist(item_id):
    conn = sqlite3.connect(DB_PATH)
    conn.execute("DELETE FROM wishlist WHERE id=?", (item_id,))
    conn.commit()
    conn.close()
    return jsonify({'success': True})


# ── Alerts ────────────────────────────────────────────────────────────────────

@app.route('/alerts/create', methods=['POST'])
def create_alert():
    data = request.get_json()
    email = (data.get('email') or '').strip()
    mhn = (data.get('market_hash_name') or '').strip()
    skin_name = (data.get('skin_name') or '').strip()
    threshold = data.get('threshold')

    if not all([email, mhn, skin_name, threshold]):
        return jsonify({'success': False, 'error': 'Missing fields'}), 400
    if '@' not in email:
        return jsonify({'success': False, 'error': 'Invalid email'}), 400
    try:
        threshold = float(threshold)
        if threshold <= 0:
            raise ValueError
    except (ValueError, TypeError):
        return jsonify({'success': False, 'error': 'Invalid price'}), 400

    conn = sqlite3.connect(DB_PATH)
    conn.execute(
        "INSERT INTO alerts (email, market_hash_name, skin_name, threshold_price, created_at) VALUES (?,?,?,?,?)",
        (email, mhn, skin_name, threshold, datetime.now().isoformat())
    )
    conn.commit()
    conn.close()
    return jsonify({'success': True})


@app.route('/alerts/delete/<int:alert_id>', methods=['POST'])
def delete_alert(alert_id):
    conn = sqlite3.connect(DB_PATH)
    conn.execute("DELETE FROM alerts WHERE id=?", (alert_id,))
    conn.commit()
    conn.close()
    return jsonify({'success': True})


@app.route('/my-alerts')
def my_alerts():
    email = request.args.get('email', '').strip()
    alerts = []
    if email:
        conn = sqlite3.connect(DB_PATH)
        conn.row_factory = sqlite3.Row
        alerts = conn.execute(
            "SELECT * FROM alerts WHERE email=? ORDER BY created_at DESC", (email,)
        ).fetchall()
        conn.close()
    return render_template('alerts.html', alerts=alerts, email=email)


@app.route('/check-alerts')
def check_alerts():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    active_alerts = conn.execute("SELECT * FROM alerts WHERE triggered=0").fetchall()
    active_wishlist = conn.execute("SELECT * FROM wishlist WHERE triggered=0").fetchall()
    triggered = 0

    for item in list(active_alerts) + list(active_wishlist):
        _, price = fetch_price(item['market_hash_name'])
        table = 'alerts' if 'threshold_price' in item.keys() else 'wishlist'
        conn.execute(f"UPDATE {table} SET current_price=?, last_checked=? WHERE id=?",
                     (price, datetime.now().isoformat(), item['id']))
        conn.commit()
        if price > 0 and price <= item['threshold_price']:
            sent = send_alert_email(item['email'], item['skin_name'], item['threshold_price'], price)
            if sent:
                conn.execute(f"UPDATE {table} SET triggered=1 WHERE id=?", (item['id'],))
                conn.commit()
                triggered += 1

    conn.close()
    return jsonify({'alerts_checked': len(active_alerts), 'wishlist_checked': len(active_wishlist), 'triggered': triggered})


if __name__ == '__main__':
    port = int(os.getenv('PORT', 5001))
    app.run(debug=False, host='0.0.0.0', port=port, use_reloader=False)
