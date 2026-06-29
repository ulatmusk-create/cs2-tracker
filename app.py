from flask import Flask, render_template, request, jsonify, Response, session, redirect, url_for
import requests
import re
import time
import sqlite3
import smtplib
import os
import uuid
import json
import csv
import io
import xml.etree.ElementTree as ET
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from dotenv import load_dotenv

load_dotenv()

app = Flask(__name__)
app.secret_key = os.getenv('SECRET_KEY', os.urandom(24))

CACHE_TTL = 3600
price_cache = {}
float_cache = {}  # inspect_url -> float data (floats never change, safe to cache forever)

HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120.0'
}

DATABASE_URL = os.getenv('DATABASE_URL')
if DATABASE_URL and DATABASE_URL.startswith('postgres://'):
    DATABASE_URL = DATABASE_URL.replace('postgres://', 'postgresql://', 1)
USE_POSTGRES = bool(DATABASE_URL)
P = '%s' if USE_POSTGRES else '?'

STRIPE_SECRET = os.getenv('STRIPE_SECRET_KEY')
STRIPE_PUB = os.getenv('STRIPE_PUBLISHABLE_KEY')
STRIPE_PRICE_ID = os.getenv('STRIPE_PRICE_ID')
STRIPE_WEBHOOK_SECRET = os.getenv('STRIPE_WEBHOOK_SECRET')

if STRIPE_SECRET:
    import stripe
    stripe.api_key = STRIPE_SECRET

if USE_POSTGRES:
    import psycopg2
    import psycopg2.extras

@contextmanager
def db():
    if USE_POSTGRES:
        conn = psycopg2.connect(DATABASE_URL)
        cur = conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor)
    else:
        conn = sqlite3.connect('tracker.db')
        conn.row_factory = sqlite3.Row
        cur = conn.cursor()
    try:
        yield cur
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


# ── Database ──────────────────────────────────────────────────────────────────

def init_db():
    pk = 'SERIAL PRIMARY KEY' if USE_POSTGRES else 'INTEGER PRIMARY KEY AUTOINCREMENT'
    with db() as cur:
        cur.execute(f'''
            CREATE TABLE IF NOT EXISTS alerts (
                id {pk},
                email TEXT NOT NULL,
                market_hash_name TEXT NOT NULL,
                skin_name TEXT NOT NULL,
                threshold_price REAL NOT NULL,
                current_price REAL DEFAULT 0,
                created_at TEXT,
                last_checked TEXT,
                triggered INTEGER DEFAULT 0
            )
        ''')
        cur.execute(f'''
            CREATE TABLE IF NOT EXISTS snapshots (
                id {pk},
                steam_id TEXT NOT NULL,
                total_value REAL NOT NULL,
                item_count INTEGER NOT NULL,
                recorded_at TEXT
            )
        ''')
        cur.execute(f'''
            CREATE TABLE IF NOT EXISTS shares (
                id TEXT PRIMARY KEY,
                steam_id TEXT NOT NULL,
                total_value REAL NOT NULL,
                item_count INTEGER NOT NULL,
                items_json TEXT NOT NULL,
                created_at TEXT
            )
        ''')
        cur.execute(f'''
            CREATE TABLE IF NOT EXISTS wishlist (
                id {pk},
                email TEXT NOT NULL,
                market_hash_name TEXT NOT NULL,
                skin_name TEXT NOT NULL,
                target_price REAL NOT NULL,
                current_price REAL DEFAULT 0,
                created_at TEXT,
                last_checked TEXT,
                triggered INTEGER DEFAULT 0
            )
        ''')
        cur.execute(f'''
            CREATE TABLE IF NOT EXISTS subscribers (
                id {pk},
                email TEXT UNIQUE NOT NULL,
                stripe_customer_id TEXT,
                stripe_subscription_id TEXT,
                status TEXT DEFAULT 'inactive',
                created_at TEXT
            )
        ''')
        cur.execute(f'''
            CREATE TABLE IF NOT EXISTS buy_prices (
                id {pk},
                steam_id TEXT NOT NULL,
                market_hash_name TEXT NOT NULL,
                buy_price REAL NOT NULL,
                updated_at TEXT
            )
        ''')
        cur.execute(f'''
            CREATE TABLE IF NOT EXISTS users (
                id {pk},
                steam_id TEXT UNIQUE NOT NULL,
                username TEXT,
                avatar TEXT,
                created_at TEXT,
                last_login TEXT
            )
        ''')

init_db()


def is_pro(email):
    if not email:
        return False
    with db() as cur:
        cur.execute(f"SELECT status FROM subscribers WHERE email={P}", (email.lower().strip(),))
        row = cur.fetchone()
    return bool(row and row['status'] == 'active')


def _upsert_subscriber(email, customer_id, sub_id, status):
    with db() as cur:
        cur.execute(f"SELECT id FROM subscribers WHERE email={P}", (email,))
        if cur.fetchone():
            cur.execute(f"UPDATE subscribers SET stripe_customer_id={P}, stripe_subscription_id={P}, status={P} WHERE email={P}",
                       (customer_id, sub_id, status, email))
        else:
            cur.execute(f"INSERT INTO subscribers (email, stripe_customer_id, stripe_subscription_id, status, created_at) VALUES ({P},{P},{P},{P},{P})",
                       (email, customer_id, sub_id, status, datetime.now().isoformat()))


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


def parse_stickers(desc_list):
    stickers = []
    for entry in desc_list:
        val = entry.get('value', '')
        if 'Sticker:' not in val:
            continue
        img_urls = re.findall(r'src="([^"]+)"', val)
        names = re.findall(r'<a[^>]*>([^<]+)</a>', val)
        if not names:
            plain = re.sub(r'<[^>]+>', '', val)
            after = plain.split('Sticker:')[-1]
            names = [n.strip() for n in after.split(',') if n.strip()]
        for i, name in enumerate(names):
            s = {'name': name.strip()}
            if i < len(img_urls):
                s['icon'] = img_urls[i]
            stickers.append(s)
    return stickers[:4]


def parse_items(steam_id, inv_data):
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

        # Inspect link — substitute assetid and steamid into the template
        inspect_link = ''
        for action in desc.get('actions', []):
            tpl = action.get('link', '')
            if 'csgo_econ_action_preview' in tpl:
                inspect_link = (tpl
                    .replace('%owner_steamid%', str(steam_id))
                    .replace('%assetid%', str(asset.get('assetid', ''))))
                break

        name = desc.get('name', 'Unknown')
        stickers = parse_stickers(desc.get('descriptions', []))
        is_stattrak = 'StatTrak' in name
        is_souvenir = 'Souvenir' in name
        # Knives and gloves have extraordinary rarity color
        is_special = desc.get('name_color', '').upper() in ('D32CE6', 'ADE55C')

        if mhn in seen:
            seen[mhn]['amount'] += 1
        else:
            seen[mhn] = {
                'name': name,
                'market_hash_name': mhn,
                'icon': icon,
                'rarity_color': rarity_color,
                'wear': wear,
                'amount': 1,
                'price': 0.0,
                'total': 0.0,
                'inspect_link': inspect_link,
                'stickers': stickers,
                'is_stattrak': is_stattrak,
                'is_souvenir': is_souvenir,
                'is_special': is_special,
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
    today = datetime.now().strftime('%Y-%m-%d')
    with db() as cur:
        cur.execute(f"SELECT recorded_at FROM snapshots WHERE steam_id={P} ORDER BY recorded_at DESC LIMIT 1", (steam_id,))
        last = cur.fetchone()
        if not last or last['recorded_at'][:10] != today:
            cur.execute(f"INSERT INTO snapshots (steam_id, total_value, item_count, recorded_at) VALUES ({P},{P},{P},{P})",
                       (steam_id, total, count, datetime.now().isoformat()))


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


# ── Steam auth helpers ────────────────────────────────────────────────────────

def fetch_steam_user(steam_id):
    try:
        api_key = os.getenv('STEAM_API_KEY', '')
        if api_key:
            r = requests.get(
                'https://api.steampowered.com/ISteamUser/GetPlayerSummaries/v0002/',
                params={'key': api_key, 'steamids': steam_id}, timeout=6
            )
            if r.status_code == 200:
                players = r.json().get('response', {}).get('players', [])
                if players:
                    return players[0].get('personaname', 'Player'), players[0].get('avatarmedium', '')
        # Fallback: XML profile
        r = requests.get(f"https://steamcommunity.com/profiles/{steam_id}/?xml=1",
                        headers=HEADERS, timeout=6)
        if r.status_code == 200 and '<steamID>' in r.text:
            root = ET.fromstring(r.text)
            name = root.findtext('steamID') or 'Player'
            avatar = root.findtext('avatarMedium') or ''
            return name, avatar
    except Exception:
        pass
    return 'Player', ''


def get_current_user():
    if 'steam_id' not in session:
        return None
    return {
        'steam_id': session['steam_id'],
        'username': session.get('username', 'Player'),
        'avatar': session.get('avatar', ''),
    }


# ── Routes ────────────────────────────────────────────────────────────────────

@app.route('/')
def index():
    user = get_current_user()
    return render_template('index.html', user=user)


def do_track(steam_id):
    inv_data, err = fetch_inventory(steam_id)
    if not inv_data:
        return render_template('index.html', error=err, user=get_current_user())

    items = parse_items(steam_id, inv_data)
    if not items:
        return render_template('index.html', user=get_current_user(),
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

    with db() as cur:
        cur.execute(f"SELECT total_value, recorded_at FROM snapshots WHERE steam_id={P} ORDER BY recorded_at ASC", (steam_id,))
        history = [{'value': float(r['total_value']), 'date': r['recorded_at'][:10]} for r in cur.fetchall()]

    return render_template('dashboard.html',
        items=items, total=total, steam_id=steam_id,
        count=len(items), top_item=items[0] if items else None,
        history=history, user=get_current_user())


@app.route('/track', methods=['POST'])
def track():
    profile = request.form.get('profile', '').strip()
    steam_id, err = extract_steam_id(profile)
    if not steam_id:
        return render_template('index.html', error=err, user=get_current_user())
    return do_track(steam_id)


@app.route('/me')
def me():
    user = get_current_user()
    if not user:
        return redirect('/')
    return do_track(user['steam_id'])


# ── Steam OpenID login ────────────────────────────────────────────────────────

STEAM_OPENID = 'https://steamcommunity.com/openid/login'

@app.route('/login')
def login():
    params = {
        'openid.ns': 'http://specs.openid.net/auth/2.0',
        'openid.mode': 'checkid_setup',
        'openid.return_to': request.host_url.rstrip('/') + '/auth/callback',
        'openid.realm': request.host_url,
        'openid.identity': 'http://specs.openid.net/auth/2.0/identifier_select',
        'openid.claimed_id': 'http://specs.openid.net/auth/2.0/identifier_select',
    }
    return redirect(STEAM_OPENID + '?' + requests.compat.urlencode(params))


@app.route('/auth/callback')
def auth_callback():
    claimed_id = request.args.get('openid.claimed_id', '')
    match = re.search(r'steamcommunity\.com/openid/id/(\d{17})', claimed_id)
    if not match:
        return redirect('/?error=login_failed')

    steam_id = match.group(1)

    # Verify with Steam that this login is genuine
    verify_params = dict(request.args)
    verify_params['openid.mode'] = 'check_authentication'
    try:
        vr = requests.post(STEAM_OPENID, data=verify_params, timeout=8)
        if 'is_valid:true' not in vr.text:
            return redirect('/?error=login_failed')
    except Exception:
        return redirect('/?error=login_failed')

    username, avatar = fetch_steam_user(steam_id)

    with db() as cur:
        cur.execute(f"SELECT id FROM users WHERE steam_id={P}", (steam_id,))
        if cur.fetchone():
            cur.execute(f"UPDATE users SET username={P}, avatar={P}, last_login={P} WHERE steam_id={P}",
                       (username, avatar, datetime.now().isoformat(), steam_id))
        else:
            cur.execute(f"INSERT INTO users (steam_id, username, avatar, created_at, last_login) VALUES ({P},{P},{P},{P},{P})",
                       (steam_id, username, avatar, datetime.now().isoformat(), datetime.now().isoformat()))

    session['steam_id'] = steam_id
    session['username'] = username
    session['avatar'] = avatar
    return redirect('/me')


@app.route('/logout')
def logout():
    session.clear()
    return redirect('/')


# ── Share ─────────────────────────────────────────────────────────────────────

@app.route('/share/create', methods=['POST'])
def create_share():
    data = request.get_json()
    share_id = str(uuid.uuid4())[:8]
    items_to_store = [
        {k: v for k, v in item.items() if k != 'market_hash_name'}
        for item in (data.get('items') or [])
    ]
    with db() as cur:
        cur.execute(
            f"INSERT INTO shares (id, steam_id, total_value, item_count, items_json, created_at) VALUES ({P},{P},{P},{P},{P},{P})",
            (share_id, data.get('steam_id', ''), data.get('total_value', 0),
             data.get('item_count', 0), json.dumps(items_to_store), datetime.now().isoformat())
        )
    return jsonify({'share_id': share_id})


@app.route('/share/<share_id>')
def view_share(share_id):
    with db() as cur:
        cur.execute(f"SELECT * FROM shares WHERE id={P}", (share_id,))
        share = cur.fetchone()
    if not share:
        return render_template('index.html', error="Share link not found or expired.")
    items = json.loads(share['items_json'])
    return render_template('share.html', share=share, items=items)


# ── Portfolio history ─────────────────────────────────────────────────────────

@app.route('/api/history/<steam_id>')
def get_history(steam_id):
    with db() as cur:
        cur.execute(f"SELECT total_value, item_count, recorded_at FROM snapshots WHERE steam_id={P} ORDER BY recorded_at ASC", (steam_id,))
        rows = cur.fetchall()
    return jsonify([{'value': r['total_value'], 'count': r['item_count'], 'date': r['recorded_at'][:10]} for r in rows])


# ── Wishlist ──────────────────────────────────────────────────────────────────

@app.route('/wishlist')
def wishlist():
    email = request.args.get('email', '').strip().lower()
    items = []
    pro = is_pro(email) if email else False
    if email and pro:
        with db() as cur:
            cur.execute(f"SELECT * FROM wishlist WHERE email={P} ORDER BY created_at DESC", (email,))
            items = cur.fetchall()
    return render_template('wishlist.html', items=items, email=email, pro=pro)


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

    if not is_pro(email):
        return jsonify({'success': False, 'pro_required': True, 'error': 'Wishlist is a Pro feature.'}), 403

    with db() as cur:
        cur.execute(
            f"INSERT INTO wishlist (email, market_hash_name, skin_name, target_price, current_price, created_at) VALUES ({P},{P},{P},{P},{P},{P})",
            (email, mhn, skin_name, target_price, float(current_price), datetime.now().isoformat())
        )
    return jsonify({'success': True})


@app.route('/wishlist/delete/<int:item_id>', methods=['POST'])
def delete_wishlist(item_id):
    with db() as cur:
        cur.execute(f"DELETE FROM wishlist WHERE id={P}", (item_id,))
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

    if not is_pro(email):
        with db() as cur:
            cur.execute(f"SELECT COUNT(*) as cnt FROM alerts WHERE email={P} AND triggered=0", (email,))
            row = cur.fetchone()
            count = row['cnt'] if row else 0
        if count >= 1:
            return jsonify({'success': False, 'pro_required': True,
                           'error': 'Free plan allows 1 active alert. Upgrade to Pro for unlimited alerts.'}), 403

    with db() as cur:
        cur.execute(
            f"INSERT INTO alerts (email, market_hash_name, skin_name, threshold_price, created_at) VALUES ({P},{P},{P},{P},{P})",
            (email, mhn, skin_name, threshold, datetime.now().isoformat())
        )
    return jsonify({'success': True})


@app.route('/alerts/delete/<int:alert_id>', methods=['POST'])
def delete_alert(alert_id):
    with db() as cur:
        cur.execute(f"DELETE FROM alerts WHERE id={P}", (alert_id,))
    return jsonify({'success': True})


@app.route('/my-alerts')
def my_alerts():
    email = request.args.get('email', '').strip()
    alerts = []
    if email:
        with db() as cur:
            cur.execute(f"SELECT * FROM alerts WHERE email={P} ORDER BY created_at DESC", (email,))
            alerts = cur.fetchall()
    return render_template('alerts.html', alerts=alerts, email=email)


@app.route('/check-alerts')
def check_alerts():
    with db() as cur:
        cur.execute("SELECT * FROM alerts WHERE triggered=0")
        active_alerts = cur.fetchall()
        cur.execute("SELECT * FROM wishlist WHERE triggered=0")
        active_wishlist = cur.fetchall()

    triggered = 0
    for item in active_alerts:
        _, price = fetch_price(item['market_hash_name'])
        with db() as cur:
            cur.execute(f"UPDATE alerts SET current_price={P}, last_checked={P} WHERE id={P}",
                       (price, datetime.now().isoformat(), item['id']))
            if price > 0 and price <= item['threshold_price']:
                sent = send_alert_email(item['email'], item['skin_name'], item['threshold_price'], price)
                if sent:
                    cur.execute(f"UPDATE alerts SET triggered=1 WHERE id={P}", (item['id'],))
                    triggered += 1

    for item in active_wishlist:
        _, price = fetch_price(item['market_hash_name'])
        with db() as cur:
            cur.execute(f"UPDATE wishlist SET current_price={P}, last_checked={P} WHERE id={P}",
                       (price, datetime.now().isoformat(), item['id']))
            if price > 0 and price <= item['target_price']:
                sent = send_alert_email(item['email'], item['skin_name'], item['target_price'], price)
                if sent:
                    cur.execute(f"UPDATE wishlist SET triggered=1 WHERE id={P}", (item['id'],))
                    triggered += 1

    return jsonify({'alerts_checked': len(active_alerts), 'wishlist_checked': len(active_wishlist), 'triggered': triggered})


# ── Float Inspector ───────────────────────────────────────────────────────────

DOPPLER_PHASES = {
    415: 'Ruby', 416: 'Sapphire', 417: 'Black Pearl',
    418: 'Phase 1', 419: 'Phase 2', 420: 'Phase 3', 421: 'Phase 4',
    568: 'Emerald',
    569: 'Phase 1', 570: 'Phase 2', 571: 'Phase 3', 572: 'Phase 4',
    575: 'Ruby', 576: 'Sapphire', 577: 'Black Pearl',
    580: 'Phase 1', 581: 'Phase 2', 582: 'Phase 3', 583: 'Phase 4',
    584: 'Emerald',
}

@app.route('/api/float')
def get_float():
    inspect_url = request.args.get('url', '').strip()
    if not inspect_url or 'csgo_econ_action_preview' not in inspect_url:
        return jsonify({'error': 'Invalid inspect link'}), 400

    if inspect_url in float_cache:
        return jsonify(float_cache[inspect_url])

    try:
        r = requests.get('https://api.csfloat.com/', params={'url': inspect_url},
                        headers=HEADERS, timeout=12)
        if r.status_code == 200:
            info = r.json().get('iteminfo', {})
            phase = DOPPLER_PHASES.get(info.get('paintindex'))
            # Build sticker icon URLs from material paths
            stickers = []
            for s in info.get('stickers', []):
                entry = {'name': s.get('name', '')}
                mat = s.get('material', '')
                if mat:
                    entry['icon'] = f"https://steamcdn-a.akamaihd.net/apps/730/icons/econ/stickers/{mat}.png"
                stickers.append(entry)
            result = {
                'float': info.get('floatvalue'),
                'seed': info.get('paintseed'),
                'min': info.get('min'),
                'max': info.get('max'),
                'phase': phase,
                'stickers': stickers,
                'wear_name': info.get('wear_name', ''),
                'full_name': info.get('full_item_name', ''),
            }
            float_cache[inspect_url] = result
            return jsonify(result)
        elif r.status_code == 429:
            return jsonify({'error': 'Rate limited — wait a few seconds and try again'}), 429
        elif r.status_code == 404:
            return jsonify({'error': 'Item not found — may be a non-inspectable item'}), 404
        else:
            return jsonify({'error': f'Float service returned {r.status_code}'}), 502
    except requests.exceptions.Timeout:
        return jsonify({'error': 'Request timed out — try again'}), 504
    except Exception as e:
        return jsonify({'error': 'Failed to fetch float data'}), 500


# ── Pricing & Stripe ──────────────────────────────────────────────────────────

@app.route('/pricing')
def pricing():
    return render_template('pricing.html', stripe_pub=STRIPE_PUB)

@app.route('/create-checkout', methods=['POST'])
def create_checkout():
    if not STRIPE_SECRET:
        return jsonify({'error': 'Payments not configured yet'}), 500
    data = request.get_json()
    email = (data.get('email') or '').strip().lower()
    try:
        session = stripe.checkout.Session.create(
            payment_method_types=['card'],
            mode='subscription',
            customer_email=email or None,
            line_items=[{'price': STRIPE_PRICE_ID, 'quantity': 1}],
            success_url=request.host_url + 'success?session_id={CHECKOUT_SESSION_ID}',
            cancel_url=request.host_url + 'pricing',
        )
        return jsonify({'url': session.url})
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/success')
def success():
    return render_template('success.html')

@app.route('/webhook', methods=['POST'])
def stripe_webhook():
    if not STRIPE_SECRET:
        return '', 400
    payload = request.data
    sig = request.headers.get('Stripe-Signature')
    try:
        event = stripe.Webhook.construct_event(payload, sig, STRIPE_WEBHOOK_SECRET)
    except Exception:
        return '', 400

    if event['type'] == 'checkout.session.completed':
        session = event['data']['object']
        email = (session.get('customer_email') or
                 (session.get('customer_details') or {}).get('email') or '').lower()
        sub_id = session.get('subscription')
        customer_id = session.get('customer')
        if email:
            _upsert_subscriber(email, customer_id, sub_id, 'active')

    elif event['type'] in ('customer.subscription.deleted', 'customer.subscription.paused'):
        sub_id = event['data']['object']['id']
        with db() as cur:
            cur.execute(f"UPDATE subscribers SET status='cancelled' WHERE stripe_subscription_id={P}", (sub_id,))

    elif event['type'] == 'customer.subscription.updated':
        sub = event['data']['object']
        status = 'active' if sub['status'] == 'active' else 'cancelled'
        with db() as cur:
            cur.execute(f"UPDATE subscribers SET status={P} WHERE stripe_subscription_id={P}", (status, sub['id']))

    return '', 200

@app.route('/api/check-pro')
def check_pro_route():
    email = request.args.get('email', '').strip().lower()
    return jsonify({'pro': is_pro(email)})


# ── P&L buy price ─────────────────────────────────────────────────────────────

@app.route('/api/buy-price', methods=['POST'])
def save_buy_price():
    data = request.get_json()
    steam_id = (data.get('steam_id') or '').strip()
    mhn = (data.get('market_hash_name') or '').strip()
    try:
        buy_price = float(data.get('buy_price', 0))
    except (ValueError, TypeError):
        return jsonify({'success': False}), 400
    if not steam_id or not mhn:
        return jsonify({'success': False}), 400

    with db() as cur:
        cur.execute(f"SELECT id FROM buy_prices WHERE steam_id={P} AND market_hash_name={P}", (steam_id, mhn))
        if cur.fetchone():
            cur.execute(f"UPDATE buy_prices SET buy_price={P}, updated_at={P} WHERE steam_id={P} AND market_hash_name={P}",
                       (buy_price, datetime.now().isoformat(), steam_id, mhn))
        else:
            cur.execute(f"INSERT INTO buy_prices (steam_id, market_hash_name, buy_price, updated_at) VALUES ({P},{P},{P},{P})",
                       (steam_id, mhn, buy_price, datetime.now().isoformat()))
    return jsonify({'success': True})

@app.route('/api/buy-prices/<steam_id>')
def get_buy_prices(steam_id):
    with db() as cur:
        cur.execute(f"SELECT market_hash_name, buy_price FROM buy_prices WHERE steam_id={P}", (steam_id,))
        rows = cur.fetchall()
    return jsonify({r['market_hash_name']: r['buy_price'] for r in rows})


# ── CSV export ────────────────────────────────────────────────────────────────

@app.route('/export/<steam_id>')
def export_csv(steam_id):
    with db() as cur:
        cur.execute(f"SELECT market_hash_name, buy_price FROM buy_prices WHERE steam_id={P}", (steam_id,))
        bp_rows = cur.fetchall()
    buy_prices_map = {r['market_hash_name']: r['buy_price'] for r in bp_rows}

    inv_data, err = fetch_inventory(steam_id)
    if not inv_data:
        return err or 'Failed', 400

    items = parse_items(steam_id, inv_data)
    unique_names = list({item['market_hash_name'] for item in items})
    prices = {}
    with ThreadPoolExecutor(max_workers=4) as executor:
        for name, price in executor.map(fetch_price, unique_names):
            prices[name] = price
    for item in items:
        item['price'] = prices.get(item['market_hash_name'], 0.0)
        item['total'] = round(item['price'] * item['amount'], 2)
    items.sort(key=lambda x: x['total'], reverse=True)

    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(['Skin', 'Wear', 'Qty', 'Current Price', 'Total Value', 'Buy Price', 'P&L'])
    for item in items:
        bp = buy_prices_map.get(item['market_hash_name'], '')
        pl = round((item['price'] - bp) * item['amount'], 2) if bp != '' else ''
        writer.writerow([item['name'], item['wear'], item['amount'],
                        f"${item['price']:.2f}", f"${item['total']:.2f}",
                        f"${bp:.2f}" if bp != '' else '', f"${pl:.2f}" if pl != '' else ''])

    output.seek(0)
    return Response(output.getvalue(), mimetype='text/csv',
                   headers={'Content-Disposition': f'attachment; filename=cs2-inventory-{steam_id}.csv'})


if __name__ == '__main__':
    port = int(os.getenv('PORT', 5001))
    app.run(debug=False, host='0.0.0.0', port=port, use_reloader=False)
