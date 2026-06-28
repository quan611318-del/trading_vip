
import json
import hmac
import hashlib
import time
import threading
import urllib.request
import urllib.parse
import numpy as np
import websocket
import logging
from logging.handlers import RotatingFileHandler
import requests
import os
import math
import traceback
import random
import queue
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor
from collections import defaultdict
import ssl
import html
import sys
import gc
from typing import Optional, List, Dict, Any, Tuple, Callable

_BINANCE_LAST_REQUEST_TIME = 0
_BINANCE_RATE_LOCK = threading.RLock()
_BINANCE_MIN_INTERVAL = 0.2

_SYMBOL_BLACKLIST = {'BTCUSDT', 'BTCUSDC','ETHUSDT','ETHUSDC'}


_BOOK_TICKER_CACHE = {'ts': 0.0, 'data': {}}
_LEVERAGE_BRACKET_CACHE = {'ts': 0.0, 'data': {}}
_COIN_LOSS_COOLDOWN = {}  # symbol -> timestamp until allowed again

class CoinCache:
    def __init__(self):
        self._data: List[Dict] = []
        self._last_volume_update: float = 0
        self._last_price_update: float = 0
        self._lock = threading.RLock()
        self._volume_cache_ttl = 6 * 3600
        self._price_cache_ttl = 300
        self._refresh_interval = 300

    def get_data(self) -> List[Dict]:
        with self._lock:
            return [coin.copy() for coin in self._data]

    def update_data(self, new_data: List[Dict]):
        with self._lock:
            self._data = new_data

    def update_volume_time(self):
        with self._lock:
            self._last_volume_update = time.time()

    def update_price_time(self):
        with self._lock:
            self._last_price_update = time.time()

    def get_stats(self) -> Dict:
        with self._lock:
            return {
                'count': len(self._data),
                'last_volume_update': self._last_volume_update,
                'last_price_update': self._last_price_update,
                'volume_cache_ttl': self._volume_cache_ttl,
                'price_cache_ttl': self._price_cache_ttl,
                'refresh_interval': self._refresh_interval,
            }

    def need_refresh(self) -> bool:
        with self._lock:
            return time.time() - self._last_price_update > self._refresh_interval

_COINS_CACHE = CoinCache()

def setup_logging():
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(module)s - %(message)s',
        handlers=[logging.StreamHandler(), RotatingFileHandler('bot_errors.log', maxBytes=1_000_000, backupCount=2, encoding='utf-8')]
    )
    return logging.getLogger()

logger = setup_logging()


_SIGNAL_DATA_CACHE = {}
_SIGNAL_DATA_CACHE_TTL = 1.0
_SIGNAL_DATA_CACHE_MAX_SIZE = 200
_POSITION_CACHE_MAX_SIZE = 200

def _cleanup_signal_data_cache():
    try:
        now = time.time()
        expired = [k for k, v in list(_SIGNAL_DATA_CACHE.items())
                   if now - float(v.get('ts', 0) or 0) > max(_SIGNAL_DATA_CACHE_TTL * 5, 5)]
        for k in expired:
            _SIGNAL_DATA_CACHE.pop(k, None)
        if len(_SIGNAL_DATA_CACHE) > _SIGNAL_DATA_CACHE_MAX_SIZE:
            items = sorted(_SIGNAL_DATA_CACHE.items(), key=lambda kv: float(kv[1].get('ts', 0) or 0))
            for k, _ in items[:len(_SIGNAL_DATA_CACHE) - _SIGNAL_DATA_CACHE_MAX_SIZE]:
                _SIGNAL_DATA_CACHE.pop(k, None)
    except Exception:
        pass


def cleanup_runtime_caches(active_symbols=None, aggressive=False):
    """Dọn cache runtime để tránh Railway bị OOM khi bot chạy lâu.

    - Không giữ dữ liệu signal quá TTL.
    - Không để position cache phình theo nhiều coin/API key cũ.
    - Dọn các symbol không còn active khỏi cache nến/giá sẽ được làm trong manager.
    """
    try:
        active = {str(s).upper() for s in (active_symbols or []) if s}
        _cleanup_signal_data_cache()

        # Position cache: chỉ giữ symbol còn active hoặc dữ liệu mới, giới hạn kích thước.
        try:
            now = time.time()
            with _POSITION_CACHE_LOCK:
                for k, v in list(_POSITION_CACHE.items()):
                    sym = k[0] if isinstance(k, tuple) and k else None
                    age = now - float((v or {}).get('ts', 0) or 0)
                    if age > 60 or (active and sym not in active):
                        _POSITION_CACHE.pop(k, None)
                if len(_POSITION_CACHE) > _POSITION_CACHE_MAX_SIZE:
                    items = sorted(_POSITION_CACHE.items(), key=lambda kv: float((kv[1] or {}).get('ts', 0) or 0))
                    for k, _ in items[:len(_POSITION_CACHE) - _POSITION_CACHE_MAX_SIZE]:
                        _POSITION_CACHE.pop(k, None)
        except NameError:
            pass

        if aggressive:
            gc.collect()
    except Exception:
        pass

def escape_html(text):
    if not text: return text
    return html.escape(text)

def send_telegram(message, chat_id=None, reply_markup=None, bot_token=None, default_chat_id=None):
    if not bot_token or not (chat_id or default_chat_id):
        return

    url = f"https://api.telegram.org/bot{bot_token}/sendMessage"
    safe_message = escape_html(message)

    payload = {"chat_id": chat_id or default_chat_id, "text": safe_message, "parse_mode": "HTML"}
    if reply_markup:
        payload["reply_markup"] = json.dumps(reply_markup)

    try:
        response = requests.post(url, json=payload, timeout=15)
        if response.status_code != 200:
            logger.error(f"Lỗi Telegram ({response.status_code}): {response.text}")
    except Exception as e:
        logger.error(f"Lỗi kết nối Telegram: {str(e)}")

def create_main_menu():
    return {
        "keyboard": [
            [{"text": "📊 Danh sách Bot"}, {"text": "📊 Thống kê"}],
            [{"text": "➕ Thêm Bot"}, {"text": "⛔ Dừng Bot"}],
            [{"text": "⛔ Quản lý Coin"}, {"text": "📈 Vị thế"}],
            [{"text": "💰 Số dư"}, {"text": "⚙️ Cấu hình"}],
            [{"text": "🎯 Chiến lược"}]
        ],
        "resize_keyboard": True,
        "one_time_keyboard": False
    }


def create_bot_count_keyboard():
    return {
        "keyboard": [
            [{"text": "1"}, {"text": "3"}, {"text": "5"}],
            [{"text": "10"}, {"text": "20"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True, "one_time_keyboard": True
    }

def create_bot_mode_keyboard():
    return {
        "keyboard": [
            [{"text": "🤖 Bot Tĩnh - Coin cụ thể"}, {"text": "🔄 Bot Động - Tự tìm coin"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True, "one_time_keyboard": True
    }

def create_symbols_keyboard():
    try:
        coins = get_coins_with_info()
        coins_sorted = sorted(coins, key=lambda x: x['volume'], reverse=True)[:12]
        symbols = [coin['symbol'] for coin in coins_sorted if coin['volume'] > 0]
        if not symbols:
            symbols = ["BNBUSDT", "ADAUSDT", "DOGEUSDT", "XRPUSDT", "DOTUSDT", "LINKUSDT", "SOLUSDT", "MATICUSDT"]
    except:
        symbols = ["BNBUSDT", "ADAUSDT", "DOGEUSDT", "XRPUSDT", "DOTUSDT", "LINKUSDT", "SOLUSDT", "MATICUSDT"]

    keyboard = []
    row = []
    for symbol in symbols:
        row.append({"text": symbol})
        if len(row) == 3:
            keyboard.append(row)
            row = []
    if row:
        keyboard.append(row)
    keyboard.append([{"text": "❌ Hủy bỏ"}])

    return {"keyboard": keyboard, "resize_keyboard": True, "one_time_keyboard": True}

def create_leverage_keyboard():
    leverages = ["3", "5", "10", "15", "20", "25", "50", "75", "100"]
    keyboard = []
    row = []
    for lev in leverages:
        row.append({"text": f"{lev}x"})
        if len(row) == 3:
            keyboard.append(row)
            row = []
    if row:
        keyboard.append(row)
    keyboard.append([{"text": "❌ Hủy bỏ"}])
    return {"keyboard": keyboard, "resize_keyboard": True, "one_time_keyboard": True}

def create_percent_keyboard():
    return {
        "keyboard": [
            [{"text": "1"}, {"text": "3"}, {"text": "5"}, {"text": "10"}],
            [{"text": "15"}, {"text": "20"}, {"text": "25"}, {"text": "50"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True, "one_time_keyboard": True
    }

def create_tp_keyboard():
    return {
        "keyboard": [
            [{"text": "50"}, {"text": "100"}, {"text": "200"}],
            [{"text": "300"}, {"text": "500"}, {"text": "1000"}],
            [{"text": "❌ Bỏ qua (không TP)"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True, "one_time_keyboard": True
    }

def create_sl_keyboard():
    return {
        "keyboard": [
            [{"text": "0"}, {"text": "50"}, {"text": "100"}],
            [{"text": "150"}, {"text": "200"}, {"text": "500"}],
            [{"text": "❌ Bỏ qua (không SL)"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True, "one_time_keyboard": True
    }

def create_strategy_config_keyboard():
    """Bàn phím chiến lược random: chỉ giữ TP/SL và bảo vệ lợi nhuận."""
    return {
        "keyboard": [
            [{"text": "📊 Xem tham số chiến lược"}],
            [{"text": "✏️ TP chiến lược"}, {"text": "✏️ SL chiến lược"}],
            [{"text": "✏️ Bảo vệ lợi nhuận"}, {"text": "✏️ ROI bắt đầu bảo vệ"}],
            [{"text": "✏️ ROI tụt từ đỉnh để đóng"}],
            [{"text": "🔄 Reset chiến lược mặc định"}],
            [{"text": "🔙 Quay lại menu chính"}],
        ],
        "resize_keyboard": True,
        "one_time_keyboard": False,
    }

def create_strategy_value_keyboard():
    """Bàn phím nhập giá trị cho TP/SL và bảo vệ lợi nhuận."""
    return {
        "keyboard": [
            [{"text": "0"}, {"text": "1"}, {"text": "5"}, {"text": "10"}],
            [{"text": "20"}, {"text": "30"}, {"text": "50"}, {"text": "100"}],
            [{"text": "150"}, {"text": "200"}, {"text": "300"}, {"text": "500"}],
            [{"text": "❌ Hủy bỏ"}]
        ],
        "resize_keyboard": True,
        "one_time_keyboard": True
    }

def _wait_for_rate_limit():
    global _BINANCE_LAST_REQUEST_TIME
    with _BINANCE_RATE_LOCK:
        now = time.time()
        delta = now - _BINANCE_LAST_REQUEST_TIME
        if delta < _BINANCE_MIN_INTERVAL:
            time.sleep(_BINANCE_MIN_INTERVAL - delta)
        _BINANCE_LAST_REQUEST_TIME = time.time()

def sign(query, api_secret):
    try:
        return hmac.new(api_secret.encode(), query.encode(), hashlib.sha256).hexdigest()
    except Exception as e:
        logger.error(f"Lỗi ký: {str(e)}")
        return ""

def binance_api_request(url, method='GET', params=None, headers=None):
    max_retries = 3
    base_url = url
    retryable_codes = {429, 418, 500, 502, 503, 504}
    retryable_errors = ('Timeout', 'ConnectionError', 'BadStatusLine', 'URLError')

    for attempt in range(max_retries):
        try:
            _wait_for_rate_limit()
            url = base_url

            if headers is None: headers = {}
            if 'User-Agent' not in headers:
                headers['User-Agent'] = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'

            if method.upper() == 'GET':
                if params:
                    query = urllib.parse.urlencode(params)
                    url = f"{url}?{query}"
                req = urllib.request.Request(url, headers=headers)
            else:
                data = urllib.parse.urlencode(params).encode() if params else None
                req = urllib.request.Request(url, data=data, headers=headers, method=method)

            with urllib.request.urlopen(req, timeout=15) as response:
                if response.status == 200:
                    return json.loads(response.read().decode())
                else:
                    error_content = response.read().decode()
                    logger.error(f"Lỗi API ({response.status}): {error_content}")
                    if response.status in retryable_codes:
                        sleep_time = (2 ** attempt) + random.random()
                        logger.warning(f"⚠️ Lỗi {response.status}, đợi {sleep_time:.2f}s, lần thử {attempt+1}/{max_retries}")
                        time.sleep(sleep_time)
                        continue
                    else:
                        return None

        except urllib.error.HTTPError as e:
            if e.code == 451:
                logger.error("❌ Lỗi 451: Truy cập bị chặn - Kiểm tra VPN/proxy")
                return None
            else:
                logger.error(f"Lỗi HTTP ({e.code}): {e.reason}")

            if e.code in retryable_codes:
                sleep_time = (2 ** attempt) + random.random()
                logger.warning(f"⚠️ HTTP {e.code}, đợi {sleep_time:.2f}s, lần thử {attempt+1}/{max_retries}")
                time.sleep(sleep_time)
                continue
            else:
                return None

        except Exception as e:
            error_name = type(e).__name__
            if any(ret in error_name for ret in retryable_errors) or 'timeout' in str(e).lower():
                sleep_time = (2 ** attempt) + random.random()
                logger.warning(f"⚠️ Lỗi kết nối ({error_name}), đợi {sleep_time:.2f}s, lần thử {attempt+1}/{max_retries}: {str(e)}")
                time.sleep(sleep_time)
                continue
            else:
                logger.error(f"Lỗi không xác định (lần thử {attempt + 1}): {str(e)}")
                if attempt == max_retries - 1:
                    return None
                time.sleep(0.5)

    logger.error(f"❌ Thất bại yêu cầu API sau {max_retries} lần thử: {base_url}")
    return None

def refresh_coins_cache():
    try:
        url = "https://fapi.binance.com/fapi/v1/exchangeInfo"
        data = binance_api_request(url)
        if not data:
            logger.error("❌ Không thể lấy exchangeInfo từ Binance")
            return False

        coins = []
        for symbol_info in data.get('symbols', []):
            symbol = symbol_info.get('symbol', '')
            quote = symbol_info.get('quoteAsset', '')
            if quote not in ('USDT', 'USDC'):
                continue
            if symbol_info.get('status') != 'TRADING':
                continue
            if symbol in _SYMBOL_BLACKLIST:
                continue

            max_leverage = 50
            for f in symbol_info.get('filters', []):
                if f['filterType'] == 'LEVERAGE' and 'maxLeverage' in f:
                    max_leverage = int(f['maxLeverage'])
                    break

            step_size = 0.001
            min_qty = 0.001
            min_notional = 5.0
            for f in symbol_info.get('filters', []):
                if f['filterType'] == 'LOT_SIZE':
                    step_size = float(f['stepSize'])
                    min_qty = float(f.get('minQty', step_size))
                if f['filterType'] == 'MIN_NOTIONAL':
                    min_notional = float(f.get('notional', 5.0))

            coins.append({
                'symbol': symbol,
                'quote': quote,
                'max_leverage': max_leverage,
                'step_size': step_size,
                'min_qty': min_qty,
                'min_notional': min_notional,
                'price': 0.0,
                'volume': 0.0,
                'quote_volume': 0.0,
                'base_volume': 0.0,
                'trade_count': 0,
                'price_change_percent': 0.0,
                'last_price': 0.0,
                'last_price_update': 0,
                'last_volume_update': 0
            })

        _COINS_CACHE.update_data(coins)
        _COINS_CACHE.update_volume_time()
        logger.info(f"✅ Đã cập nhật cache {len(coins)} coin USDT/USDC")
        return True

    except Exception as e:
        logger.error(f"❌ Lỗi refresh cache coin: {str(e)}")
        logger.error(traceback.format_exc())
        return False

def update_coins_price():
    try:
        url = "https://fapi.binance.com/fapi/v1/ticker/price"
        all_prices = binance_api_request(url)
        if not all_prices:
            return False

        price_dict = {item['symbol']: float(item['price']) for item in all_prices}
        coins = _COINS_CACHE.get_data()
        updated = 0
        for coin in coins:
            if coin['symbol'] in price_dict:
                coin['price'] = price_dict[coin['symbol']]
                coin['last_price_update'] = time.time()
                updated += 1
        _COINS_CACHE.update_data(coins)
        _COINS_CACHE.update_price_time()
        logger.info(f"✅ Đã cập nhật giá cho {updated} coin")
        return True
    except Exception as e:
        logger.error(f"❌ Lỗi cập nhật giá: {str(e)}")
        return False

def update_coins_volume():
    try:
        url = "https://fapi.binance.com/fapi/v1/ticker/24hr"
        all_tickers = binance_api_request(url)
        if not all_tickers:
            return False

        ticker_dict = {item.get('symbol'): item for item in all_tickers if item.get('symbol')}
        coins = _COINS_CACHE.get_data()
        updated = 0
        for coin in coins:
            item = ticker_dict.get(coin['symbol'])
            if item:
                # Dùng quoteVolume USDT làm thanh khoản chính. volume base không công bằng giữa coin giá nhỏ/lớn.
                coin['base_volume'] = float(item.get('volume', 0.0) or 0.0)
                coin['quote_volume'] = float(item.get('quoteVolume', item.get('volume', 0.0)) or 0.0)
                coin['volume'] = coin['quote_volume']
                coin['trade_count'] = int(float(item.get('count', 0) or 0))
                coin['price_change_percent'] = float(item.get('priceChangePercent', 0.0) or 0.0)
                coin['last_price'] = float(item.get('lastPrice', coin.get('price', 0.0)) or 0.0)
                if coin['last_price'] > 0:
                    coin['price'] = coin['last_price']
                    coin['last_price_update'] = time.time()
                coin['last_volume_update'] = time.time()
                updated += 1
        _COINS_CACHE.update_data(coins)
        _COINS_CACHE.update_volume_time()
        logger.info(f"✅ Đã cập nhật volume cho {updated} coin")
        return True
    except Exception as e:
        logger.error(f"❌ Lỗi cập nhật volume: {str(e)}")
        return False

def get_coins_with_info():
    return _COINS_CACHE.get_data()


def get_min_notional_from_cache(symbol):
    symbol = symbol.upper()
    coins = _COINS_CACHE.get_data()
    for coin in coins:
        if coin['symbol'] == symbol:
            return coin.get('min_notional', 5.0)
    return 5.0

def get_min_qty_from_cache(symbol):
    symbol = symbol.upper()
    coins = _COINS_CACHE.get_data()
    for coin in coins:
        if coin['symbol'] == symbol:
            return coin.get('min_qty', 0.001)
    return 0.001

def get_step_size(symbol):
    if not symbol: return 0.001
    coins = _COINS_CACHE.get_data()
    for coin in coins:
        if coin['symbol'] == symbol.upper():
            return coin['step_size']
    return 0.001


def set_leverage(symbol, lev, api_key, api_secret):
    if not symbol: return False
    try:
        ts = int(time.time() * 1000)
        params = {"symbol": symbol.upper(), "leverage": lev, "timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v1/leverage?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        response = binance_api_request(url, method='POST', headers=headers)
        return bool(response and 'leverage' in response)
    except Exception as e:
        logger.error(f"Lỗi cài đặt đòn bẩy: {str(e)}")
        return False

def get_balance(api_key, api_secret):
    try:
        ts = int(time.time() * 1000)
        params = {"timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/account?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        data = binance_api_request(url, headers=headers)
        if not data: return None
        for asset in data['assets']:
            if asset['asset'] in ('USDT', 'USDC'):
                available_balance = float(asset['availableBalance'])
                logger.info(f"💰 Số dư - Khả dụng: {available_balance:.2f} {asset['asset']}")
                return available_balance
        return 0
    except Exception as e:
        logger.error(f"Lỗi số dư: {str(e)}")
        return None

def get_total_and_available_balance(api_key, api_secret):
    try:
        ts = int(time.time() * 1000)
        params = {"timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/account?{query}&signature={sig}"
        headers = {"X-MBX-APIKEY": api_key}
        data = binance_api_request(url, headers=headers)
        if not data:
            logger.error("❌ Không lấy được số dư từ Binance")
            return None, None
        total_all = 0.0
        available_all = 0.0
        for asset in data["assets"]:
            if asset["asset"] in ("USDT", "USDC"):
                available_all += float(asset["availableBalance"])
                total_all += float(asset["walletBalance"])
        logger.info(f"💰 Tổng số dư (USDT+USDC): {total_all:.2f}, Khả dụng: {available_all:.2f}")
        return total_all, available_all
    except Exception as e:
        logger.error(f"Lỗi lấy tổng số dư: {str(e)}")
        return None, None

def get_margin_balance(api_key, api_secret):
    try:
        ts = int(time.time() * 1000)
        params = {"timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/account?{query}&signature={sig}"
        headers = {"X-MBX-APIKEY": api_key}
        data = binance_api_request(url, headers=headers)
        if not data:
            return None
        margin_balance = float(data.get("totalMarginBalance", 0.0))
        logger.info(f"💰 Số dư ký quỹ: {margin_balance:.2f}")
        return margin_balance
    except Exception as e:
        logger.error(f"Lỗi lấy số dư ký quỹ: {str(e)}")
        return None

def get_margin_safety_info(api_key, api_secret):
    try:
        ts = int(time.time() * 1000)
        params = {"timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/account?{query}&signature={sig}"
        headers = {"X-MBX-APIKEY": api_key}
        data = binance_api_request(url, headers=headers)
        if not data:
            logger.error("❌ Không lấy được thông tin ký quỹ từ Binance")
            return None, None, None
        margin_balance = float(data.get("totalMarginBalance", 0.0))
        maint_margin = float(data.get("totalMaintMargin", 0.0))
        if maint_margin <= 0:
            logger.warning(f"⚠️ Maint margin <= 0 (margin_balance={margin_balance:.4f}, maint_margin={maint_margin:.4f})")
            return margin_balance, maint_margin, None
        ratio = margin_balance / maint_margin
        logger.info(f"🛡️ An toàn ký quỹ: margin_balance={margin_balance:.4f}, maint_margin={maint_margin:.4f}, tỷ lệ={ratio:.2f}x")
        return margin_balance, maint_margin, ratio
    except Exception as e:
        logger.error(f"Lỗi lấy thông tin an toàn ký quỹ: {str(e)}")
        return None, None, None

def place_order(symbol, side, qty, api_key, api_secret):
    if not symbol: return None
    try:
        ts = int(time.time() * 1000)
        params = {
            "symbol": symbol.upper(),
            "side": side,
            "type": "MARKET",
            "quantity": qty,
            "timestamp": ts
        }
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v1/order?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        return binance_api_request(url, method='POST', headers=headers)
    except Exception as e:
        logger.error(f"Lỗi lệnh: {str(e)}")
        return None

def cancel_all_orders(symbol, api_key, api_secret):
    if not symbol: return False
    try:
        ts = int(time.time() * 1000)
        params = {"symbol": symbol.upper(), "timestamp": ts}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v1/allOpenOrders?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        response = binance_api_request(url, method='DELETE', headers=headers)
        return response is not None
    except Exception as e:
        logger.error(f"Lỗi hủy lệnh: {str(e)}")
        return False

def get_current_price(symbol):
    if not symbol: return 0
    try:
        url = f"https://fapi.binance.com/fapi/v1/ticker/price?symbol={symbol.upper()}"
        data = binance_api_request(url)
        if data and 'price' in data:
            price = float(data['price'])
            return price if price > 0 else 0
        return 0
    except Exception as e:
        logger.error(f"Lỗi giá {symbol}: {str(e)}")
        return 0

_BINANCE_INTERVAL_SECONDS = {
    '1m': 60.0, '3m': 180.0, '5m': 300.0, '15m': 900.0,
    '30m': 1800.0, '1h': 3600.0, '2h': 7200.0, '4h': 14400.0
}

def _normalize_interval(value):
    v = str(value or '1m').strip().lower()
    return v if v in _BINANCE_INTERVAL_SECONDS else '1m'

def _interval_seconds(interval=None):
    return float(_BINANCE_INTERVAL_SECONDS.get(_normalize_interval(interval), 60.0))

class StrategyConfig:
    """Cấu hình chiến lược RANDOM.

    Không dùng volume, biên độ, doji, trend, EMA/RSI, taker hay bất kỳ điều kiện tín hiệu nào.
    Hướng vào lệnh được chọn ngẫu nhiên BUY/SELL. Khi đã có vị thế, bot chỉ quản lý thoát
    bằng TP, SL, emergency SL và bảo vệ lợi nhuận tụt từ đỉnh.

    Một số key cũ vẫn được giữ trong DEFAULTS để tránh lỗi tương thích với Telegram/state cũ,
    nhưng không còn được dùng để tạo tín hiệu.
    """
    DEFAULTS = {
        'current_interval': '15m',
        'signal_interval': '15m',
        'timeframe_seconds': 900.0,
        'volume_factor': 1.10,
        'range_factor': 1.10,
        'min_prev_range_pct': 0.08,
        'block_same_candle_reverse': 1.0,
        'use_quote_volume': 1.0,
        'strategy_tp_roi': 0.0,
        'strategy_sl_roi': 0.0,
        'emergency_stop_roi': 0.0,
        'profit_protect_enabled': 1.0,
        'profit_protect_start_roi': 50.0,
        'profit_protect_pullback_roi': 30.0,
        'max_reverse_count': 999,
        'max_hold_seconds': 0,
        'low_volume_filter_enabled': 0.0,
        'min_24h_volume': 0.0,
        'scan_top_coin_limit': 300,
        'max_signal_eval_coins': 300,
        'min_coin_price': 0.0,
        'max_coin_price': 0.0,
        'min_24h_trade_count': 0,
        'max_spread_pct': 999.0,
        'target_leverage': 50,
        'min_allowed_leverage': 50,
        'max_abs_24h_change_pct': 0.0,
        'min_abs_24h_change_pct': 0.0,
        'coin_cooldown_after_loss_sec': 180,
        'max_consecutive_losses_before_pause': 999,
        'pause_after_loss_streak_sec': 0,
        'force_rest_signal_enabled': 0.0,
        # Alias cũ để không lỗi với phần code chung/Telegram cũ, nhưng không dùng làm tín hiệu.
        'entry_buy_force_pct': 0.0,
        'entry_sell_force_pct': 0.0,
        'exit_force_pct': 0.0,
        'reverse_force_pct': 0.0,
        'min_force_gap_pct': 0.0,
        'entry_score_threshold': 0.0,
        'exit_score_threshold': 0.0,
        'reverse_score_threshold': 999999.0,
        'min_score_gap': 0.0,
        'entry_min_body_pct': 0.0,
        'entry_min_range_pct': 0.0,
        'entry_min_body_ratio': 0.0,
        'entry_min_quote_volume': 0.0,
        'entry_min_trades': 0,
        'exit_min_body_pct': 0.0,
        'exit_min_range_pct': 0.0,
        'exit_min_body_ratio': 0.0,
        'exit_min_quote_volume': 0.0,
        'exit_min_trades': 0,
        'exit_taker_ratio_min': 0.0,
        'buy_taker_ratio_min': 0.0,
        'sell_taker_ratio_min': 0.0,
        'compare_interval': '15m',
        'market_interval': '15m',
        'extreme_interval': '15m',
        'min_elapsed_seconds': 0.0,
    }
    INT_KEYS = {'max_reverse_count', 'scan_top_coin_limit', 'max_signal_eval_coins', 'min_24h_trade_count', 'target_leverage', 'min_allowed_leverage', 'max_consecutive_losses_before_pause', 'max_hold_seconds', 'coin_cooldown_after_loss_sec'}
    STRING_KEYS = {'current_interval', 'signal_interval', 'compare_interval', 'market_interval', 'extreme_interval'}

    def __init__(self):
        self._config = self.DEFAULTS.copy()
        self._lock = threading.RLock()

    def _sync_aliases_locked(self):
        self._config['signal_interval'] = self._config.get('current_interval', '1m')
        self._config['timeframe_seconds'] = _interval_seconds(self._config.get('current_interval', '1m'))
        self._config['compare_interval'] = self._config.get('current_interval', '1m')
        self._config['market_interval'] = self._config.get('current_interval', '1m')
        self._config['extreme_interval'] = self._config.get('current_interval', '1m')

    def get(self, key, default=None):
        with self._lock:
            self._sync_aliases_locked()
            if key == 'signal_interval':
                return self._config.get('current_interval', default)
            return self._config.get(key, default)

    def get_all(self):
        with self._lock:
            self._sync_aliases_locked()
            return self._config.copy()

    def update(self, **kwargs):
        with self._lock:
            for key, value in kwargs.items():
                if key in ('signal_interval', 'compare_interval', 'market_interval', 'extreme_interval'):
                    key = 'current_interval'
                if key == 'strategy_mode':
                    continue
                if key in self._config and value is not None:
                    if key in self.STRING_KEYS:
                        self._config[key] = _normalize_interval(value)
                    elif key in self.INT_KEYS:
                        self._config[key] = int(float(value))
                    else:
                        self._config[key] = float(value)
            self._sync_aliases_locked()
        return self.get_all()

    def reset(self):
        with self._lock:
            self._config = self.DEFAULTS.copy()
            self._sync_aliases_locked()
        return self.get_all()

_STRATEGY_CONFIG = StrategyConfig()


def get_strategy_config_text():
    c = _STRATEGY_CONFIG.get_all()
    tp = float(c.get('strategy_tp_roi', 0.0) or 0.0)
    sl = float(c.get('strategy_sl_roi', 0.0) or 0.0)
    protect_on = float(c.get('profit_protect_enabled', 1.0) or 0.0) >= 0.5
    return (
        "🎯 <b>CHIẾN LƯỢC RANDOM</b>\n\n"
        "• Tín hiệu vào lệnh: RANDOM BUY/SELL.\n"
        "• Không còn dùng volume, biên độ nến, nến bẹt, doji, EMA/RSI, trend, taker hay chấm điểm.\n"
        "• Bot động chỉ chọn một coin hợp lệ chưa bị bot khác giữ, sau đó mở hướng random.\n"
        "• Khi đã có vị thế: KHÔNG đảo chiều theo tín hiệu random.\n"
        "• Thoát lệnh chỉ bằng TP/SL, emergency SL hoặc bảo vệ lợi nhuận.\n\n"
        "🛡️ <b>TP/SL - QUẢN LÝ LỆNH</b>\n"
        f"• TP chiến lược: {tp:.1f}% ROI ({'TẮT' if tp <= 0 else 'BẬT'})\n"
        f"• SL chiến lược: {sl:.1f}% ROI ({'TẮT' if sl <= 0 else 'BẬT'})\n"
        f"• Bảo vệ lợi nhuận: {'BẬT' if protect_on else 'TẮT'} | bắt đầu {float(c.get('profit_protect_start_roi', 50.0)):.1f}% | tụt {float(c.get('profit_protect_pullback_roi', 30.0)):.1f}% thì đóng\n"
        "• Đồng bộ vị thế thật Binance: BẬT trước khi xét TP/SL.\n"
    )

def _clamp(value, lo=-1.0, hi=1.0):
    try:
        return max(float(lo), min(float(hi), float(value)))
    except Exception:
        return 0.0












def _safe_progress(candle, timeframe_seconds=None):
    timeframe_seconds = timeframe_seconds or _STRATEGY_CONFIG.get('timeframe_seconds', 60.0)
    try:
        open_ms = int(candle.get('time', 0)) if isinstance(candle, dict) else int(candle[0])
        open_ts = open_ms / 1000.0 if open_ms > 10_000_000_000 else float(open_ms)
        elapsed = max(0.0, time.time() - open_ts)
        return max(0.001, min(1.0, elapsed / float(timeframe_seconds)))
    except Exception:
        return 1.0






























def _quote_volume_of(c):
    try:
        if isinstance(c, dict):
            q = c.get('quote_volume', c.get('q', c.get('quoteVolume', 0.0)))
            q = float(q or 0.0)
            if q > 0:
                return q
            return float(c.get('volume', 0.0) or 0.0) * float(c.get('close', 0.0) or 0.0)
        if len(c) > 7:
            return float(c[7])
        return float(c[5]) * float(c[4])
    except Exception:
        return 0.0


def _taker_buy_quote_of(c):
    try:
        if isinstance(c, dict):
            return float(c.get('taker_buy_quote_volume', c.get('Q', c.get('takerBuyQuoteVolume', 0.0))) or 0.0)
        if len(c) > 10:
            return float(c[10])
    except Exception:
        pass
    return 0.0


def _num_trades_of(c):
    try:
        if isinstance(c, dict):
            return int(float(c.get('num_trades', c.get('n', c.get('trades', 0))) or 0))
        if len(c) > 8:
            return int(float(c[8]))
    except Exception:
        pass
    return 0


def _wick_metrics(open_price, close_price, high_price, low_price):
    try:
        o = float(open_price); c = float(close_price); h = float(high_price); l = float(low_price)
        rng = max(0.0, h - l)
        body = abs(c - o)
        upper = max(0.0, h - max(o, c))
        lower = max(0.0, min(o, c) - l)
        close_pos = 0.5 if rng <= 0 else (c - l) / rng
        body_ratio = 0.0 if rng <= 0 else body / rng
        return upper, lower, close_pos, body_ratio
    except Exception:
        return 0.0, 0.0, 0.5, 0.0


def _candle_open(c):
    try:
        return float(c.get('open') if isinstance(c, dict) else c[1])
    except Exception:
        return 0.0


def _candle_high(c):
    try:
        return float(c.get('high') if isinstance(c, dict) else c[2])
    except Exception:
        return 0.0


def _candle_low(c):
    try:
        return float(c.get('low') if isinstance(c, dict) else c[3])
    except Exception:
        return 0.0


def _candle_close(c):
    try:
        return float(c.get('close') if isinstance(c, dict) else c[4])
    except Exception:
        return 0.0


def _base_volume_of(c):
    try:
        if isinstance(c, dict):
            return float(c.get('volume', c.get('v', 0.0)) or 0.0)
        return float(c[5])
    except Exception:
        return 0.0


def _selected_volume_of(c):
    try:
        if float(_STRATEGY_CONFIG.get('use_quote_volume', 1.0) or 0.0) >= 0.5:
            return float(_quote_volume_of(c) or 0.0)
        return float(_base_volume_of(c) or 0.0)
    except Exception:
        return 0.0


def _range_pct_of(c):
    try:
        o = _candle_open(c); h = _candle_high(c); l = _candle_low(c)
        if o <= 0:
            return 0.0
        return max(0.0, h - l) / o * 100.0
    except Exception:
        return 0.0


def _volatility_volume_range_signal(current_candle=None, prev_closed_candle=None, mode='entry'):
    """Tín hiệu random BUY/SELL, không kiểm tra bất kỳ điều kiện nến/volume nào."""
    try:
        signal = random.choice(('BUY', 'SELL'))
        reason = f"RANDOM_SIGNAL {signal} | no signal filters"
        return signal, 100.0, reason, False
    except Exception as e:
        return None, 0.0, f'random_signal_error:{e}', False

def _force_pct_from_candle(candle):
    # Giữ lại tên cũ để các phần thống kê không lỗi, không dùng cho tín hiệu.
    try:
        q = max(0.0, float(_quote_volume_of(candle) or 0.0))
        tbq = max(0.0, float(_taker_buy_quote_of(candle) or 0.0))
        if q > 0 and tbq > q:
            tbq = q
        tsq = max(0.0, q - tbq)
        if q <= 0:
            return 50.0, 50.0, 0.0, 0.0, 0.0
        return tbq / q * 100.0, tsq / q * 100.0, q, tbq, tsq
    except Exception:
        return 50.0, 50.0, 0.0, 0.0, 0.0


def _current_force_signal_from_candle(candle, mode='entry'):
    # Không còn dùng lực taker đơn lẻ; hàm này chỉ giữ tương thích và cần prev candle nên trả None.
    return None, 0.0, 'need_previous_closed_candle', False


def _score_signal_parts(open_curr, current_price, high_curr, low_curr, volume_curr,
                        prev_candle, market_candle=None, progress=1.0,
                        current_candle=None, mode='entry'):
    candle = current_candle or {
        'open': open_curr,
        'close': current_price,
        'high': high_curr,
        'low': low_curr,
        'volume': volume_curr,
    }
    return _volatility_volume_range_signal(candle, prev_candle or {}, mode=mode)


def _closed_force_current_confirm_signal(current_candle, closed_candle=None, mode='entry'):
    # Tên cũ giữ tương thích; logic mới dùng volume + biên độ nến hiện tại so với nến đóng gần nhất.
    return _volatility_volume_range_signal(current_candle, closed_candle or {}, mode=mode)


def _fetch_rest_1m15m_signal_data(symbol):
    """Tên cũ giữ tương thích: lấy nến hiện tại và nến đóng gần nhất của khung tín hiệu."""
    try:
        cfg = _STRATEGY_CONFIG.get_all()
        current_interval = _normalize_interval(cfg.get('current_interval', '1m'))
        symbol = symbol.upper()
        now = time.time()
        key = (symbol, current_interval, 'real_force_v1')
        cached = _SIGNAL_DATA_CACHE.get(key)
        if cached and now - cached.get('ts', 0) < _SIGNAL_DATA_CACHE_TTL:
            return cached['data']

        url = "https://fapi.binance.com/fapi/v1/klines"
        data = binance_api_request(url, params={"symbol": symbol, "interval": current_interval, "limit": 4})
        if not data or len(data) < 2:
            return None, None, None, []

        curr = data[-1]
        prev_closed = data[-2]
        closed_history = list(data[:-1])
        result = (curr, prev_closed, None, closed_history)
        _cleanup_signal_data_cache()
        _SIGNAL_DATA_CACHE[key] = {'ts': now, 'data': result}
        return result
    except Exception as e:
        logger.error(f"Lỗi REST lấy dữ liệu tín hiệu Real Force Candle {symbol}: {e}")
        return None, None, None, []




def compute_signal_from_candles(prev_candle=None, curr_candle=None, prev15m_candle=None, recent_1m_history=None):
    try:
        return random.choice(('BUY', 'SELL'))
    except Exception as e:
        logger.error(f"Lỗi tính tín hiệu random: {e}")
        return None

def get_candle_signal_1h(symbol):
    """Tên cũ để tương thích: thực tế trả tín hiệu random."""
    try:
        details = get_candle_signal_details(symbol)
        return details.get('signal') if details else None
    except Exception as e:
        logger.error(f"Lỗi phân tích tín hiệu random {symbol}: {e}")
        return None

def get_candle_signal_details(symbol):
    """Lấy tín hiệu random BUY/SELL, không cần dữ liệu nến."""
    try:
        signal = random.choice(('BUY', 'SELL'))
        return {
            'symbol': str(symbol).upper() if symbol else symbol,
            'signal': signal,
            'score': 100.0,
            'reason': f'RANDOM_SIGNAL {signal} | no signal filters',
            'is_spike': False,
            'source': 'RANDOM',
            'current_volume': 0.0,
            'previous_volume': 0.0,
            'current_range_pct': 0.0,
            'previous_range_pct': 0.0,
            'num_trades': 0,
        }
    except Exception as e:
        logger.error(f"Lỗi lấy chi tiết tín hiệu random {symbol}: {e}")
        logger.error(traceback.format_exc())
        return {'symbol': symbol, 'signal': None, 'score': 0.0, 'reason': f'error: {e}', 'is_spike': False, 'source': 'RANDOM'}

def get_positions(symbol=None, api_key=None, api_secret=None):
    try:
        ts = int(time.time() * 1000)
        params = {"timestamp": ts}
        if symbol: params["symbol"] = symbol.upper()
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/positionRisk?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        positions = binance_api_request(url, headers=headers)
        if not positions: return []
        if symbol:
            for pos in positions:
                if pos['symbol'] == symbol.upper():
                    return [pos]
        return positions
    except Exception as e:
        logger.error(f"Lỗi vị thế: {str(e)}")
        return []

def get_position_strict(symbol, api_key, api_secret):
    """Lấy vị thế thật từ Binance, phân biệt lỗi API với không có vị thế.

    Trả về (ok, pos):
    - ok=False: không lấy được dữ liệu Binance, KHÔNG được reset local.
    - ok=True, pos=dict: Binance trả dữ liệu positionRisk của symbol.
    - ok=True, pos=None: Binance trả dữ liệu nhưng không tìm thấy symbol.
    """
    try:
        ts = int(time.time() * 1000)
        params = {"timestamp": ts}
        if symbol:
            params["symbol"] = symbol.upper()
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/positionRisk?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        positions = binance_api_request(url, headers=headers)
        if positions is None:
            return False, None
        if symbol:
            for pos in positions:
                if pos.get('symbol') == symbol.upper():
                    return True, pos
            return True, None
        return True, positions[0] if positions else None
    except Exception as e:
        logger.error(f"Lỗi get_position_strict {symbol}: {e}")
        return False, None


_POSITION_CACHE = {}
_POSITION_CACHE_LOCK = threading.RLock()
_POSITION_CACHE_TTL = 8.0
_POSITION_SYNC_INTERVAL = 1.0  # khi đang có vị thế, sync API mỗi ~1s để phát hiện lệnh đóng ngoài Binance gần realtime
_POSITION_CLOSE_CONFIRM_TIMEOUT = 4.0
_POSITION_CLOSE_CONFIRM_INTERVAL = 0.4

def get_position_cached(symbol, api_key, api_secret, ttl=_POSITION_CACHE_TTL, force=False):
    symbol = symbol.upper()
    now = time.time()
    cache_key = (symbol, api_key[-6:] if api_key else '')
    with _POSITION_CACHE_LOCK:
        item = _POSITION_CACHE.get(cache_key)
        if item and not force and now - item.get('ts', 0) < ttl:
            return item.get('pos')

    ok, pos = get_position_strict(symbol, api_key, api_secret)
    if not ok:
        # API lỗi thì không ghi đè cache bằng None, tránh bot tưởng vị thế đã mất.
        with _POSITION_CACHE_LOCK:
            item = _POSITION_CACHE.get(cache_key)
            if item:
                return item.get('pos')
        return {'_api_error': True}
    with _POSITION_CACHE_LOCK:
        _POSITION_CACHE[cache_key] = {'ts': now, 'pos': pos}
    return pos

def invalidate_position_cache(symbol, api_key=None):
    symbol = symbol.upper()
    with _POSITION_CACHE_LOCK:
        for key in list(_POSITION_CACHE.keys()):
            if key[0] == symbol:
                _POSITION_CACHE.pop(key, None)


class CoinManager:
    def __init__(self):
        self.active_coins = set()
        self._lock = threading.RLock()

    def register_coin(self, symbol):
        if not symbol: return
        with self._lock: self.active_coins.add(symbol.upper())

    def unregister_coin(self, symbol):
        if not symbol: return
        with self._lock: self.active_coins.discard(symbol.upper())

    def is_coin_active(self, symbol):
        if not symbol: return False
        with self._lock: return symbol.upper() in self.active_coins

    def get_active_coins(self):
        with self._lock: return list(self.active_coins)

class BotExecutionCoordinator:
    def __init__(self):
        self._lock = threading.RLock()
        self._bot_queue = queue.Queue()
        self._current_finding_bot = None
        self._found_coins = set()
        self._bots_with_coins = set()
        self._temp_blacklist = {}
        self._blacklist_lock = threading.RLock()

    def add_temp_blacklist(self, symbol, duration=300):
        expiry = time.time() + duration
        with self._blacklist_lock:
            self._temp_blacklist[symbol.upper()] = expiry
        logger.info(f"⏳ Blacklist tạm: {symbol} trong {duration}s")

    def is_temp_blacklisted(self, symbol):
        symbol = symbol.upper()
        now = time.time()
        with self._blacklist_lock:
            expired = [s for s, exp in self._temp_blacklist.items() if exp <= now]
            for s in expired:
                del self._temp_blacklist[s]
            return symbol in self._temp_blacklist

    def release_coin(self, symbol):
        with self._lock:
            self._found_coins.discard(symbol.upper())

    def request_coin_search(self, bot_id):
        with self._lock:
            if bot_id in self._bots_with_coins:
                return False
            if self._current_finding_bot is None or self._current_finding_bot == bot_id:
                self._current_finding_bot = bot_id
                return True
            else:
                if bot_id not in list(self._bot_queue.queue):
                    self._bot_queue.put(bot_id)
                return False

    def finish_coin_search(self, bot_id, found_symbol=None, has_coin_now=False):
        next_bot = None
        with self._lock:
            if self._current_finding_bot == bot_id:
                self._current_finding_bot = None
                if found_symbol:
                    self._found_coins.add(found_symbol)
                if has_coin_now:
                    self._bots_with_coins.add(bot_id)
                if not self._bot_queue.empty():
                    try:
                        next_bot = self._bot_queue.get_nowait()
                        self._current_finding_bot = next_bot
                    except queue.Empty:
                        pass
        return next_bot

    def bot_has_coin(self, bot_id):
        with self._lock:
            self._bots_with_coins.add(bot_id)
            new_queue = queue.Queue()
            while not self._bot_queue.empty():
                try:
                    b = self._bot_queue.get_nowait()
                    if b != bot_id:
                        new_queue.put(b)
                except queue.Empty:
                    break
            self._bot_queue = new_queue

    def bot_lost_coin(self, bot_id):
        with self._lock:
            self._bots_with_coins.discard(bot_id)

    def remove_bot(self, bot_id):
        with self._lock:
            if self._current_finding_bot == bot_id:
                self._current_finding_bot = None
            self._bots_with_coins.discard(bot_id)
            new_queue = queue.Queue()
            while not self._bot_queue.empty():
                try:
                    b = self._bot_queue.get_nowait()
                    if b != bot_id:
                        new_queue.put(b)
                except queue.Empty:
                    break
            self._bot_queue = new_queue

    def get_queue_info(self):
        with self._lock:
            return {
                'current_finding': self._current_finding_bot,
                'queue_size': self._bot_queue.qsize(),
                'queue_bots': list(self._bot_queue.queue),
                'bots_with_coins': list(self._bots_with_coins),
                'found_coins_count': len(self._found_coins)
            }

    def get_queue_position(self, bot_id):
        with self._lock:
            if self._current_finding_bot == bot_id:
                return 0
            else:
                queue_list = list(self._bot_queue.queue)
                return queue_list.index(bot_id) + 1 if bot_id in queue_list else -1


class SmartCoinFinder:
    """Tìm coin rác đáng đánh theo điểm, không shuffle ngẫu nhiên.

    Luồng:
    1) Lọc coin đủ chuẩn 50x: quoteVolume, trade count, giá, spread, leverage.
    2) Chấm điểm nền: thanh khoản, số trade, biến động, spread, leverage.
    3) Chỉ chấm tín hiệu sâu cho top coin nền tốt nhất để giảm request.
    4) Chọn coin có FinalCoinScore cao nhất và có tín hiệu BUY/SELL.
    """
    def __init__(self, api_key, api_secret):
        self.api_key = api_key
        self.api_secret = api_secret
        self.last_scan_time = 0
        self.scan_cooldown = 10
        self._bot_manager = None
        self.bot_leverage = 10
        self._last_best_log = 0

    def set_bot_manager(self, bot_manager):
        self._bot_manager = bot_manager

    def _get_book_ticker_map(self):
        try:
            now = time.time()
            if now - float(_BOOK_TICKER_CACHE.get('ts', 0) or 0) < 3 and _BOOK_TICKER_CACHE.get('data'):
                return _BOOK_TICKER_CACHE['data']
            data = binance_api_request('https://fapi.binance.com/fapi/v1/ticker/bookTicker')
            if not data:
                return _BOOK_TICKER_CACHE.get('data', {}) or {}
            mp = {str(x.get('symbol', '')).upper(): x for x in data if x.get('symbol')}
            _BOOK_TICKER_CACHE['ts'] = now
            _BOOK_TICKER_CACHE['data'] = mp
            return mp
        except Exception:
            return _BOOK_TICKER_CACHE.get('data', {}) or {}

    def _get_leverage_bracket_map(self):
        """Lấy bracket leverage nếu API key cho phép; lỗi thì fallback cache/giá trị coin cũ."""
        try:
            now = time.time()
            if now - float(_LEVERAGE_BRACKET_CACHE.get('ts', 0) or 0) < 900 and _LEVERAGE_BRACKET_CACHE.get('data'):
                return _LEVERAGE_BRACKET_CACHE['data']
            if not self.api_key or not self.api_secret:
                return _LEVERAGE_BRACKET_CACHE.get('data', {}) or {}
            ts = int(time.time() * 1000)
            params = {'timestamp': ts}
            query = urllib.parse.urlencode(params)
            sig = sign(query, self.api_secret)
            url = f'https://fapi.binance.com/fapi/v1/leverageBracket?{query}&signature={sig}'
            headers = {'X-MBX-APIKEY': self.api_key}
            data = binance_api_request(url, headers=headers)
            mp = {}
            if isinstance(data, list):
                for item in data:
                    sym = str(item.get('symbol', '')).upper()
                    brackets = item.get('brackets') or []
                    max_lev = 0
                    first_cap = 0.0
                    for b in brackets:
                        try:
                            max_lev = max(max_lev, int(float(b.get('initialLeverage', 0) or 0)))
                            if first_cap <= 0:
                                first_cap = float(b.get('notionalCap', 0) or 0)
                        except Exception:
                            pass
                    if sym:
                        mp[sym] = {'max_leverage': max_lev, 'first_notional_cap': first_cap}
            if mp:
                _LEVERAGE_BRACKET_CACHE['ts'] = now
                _LEVERAGE_BRACKET_CACHE['data'] = mp
                return mp
            return _LEVERAGE_BRACKET_CACHE.get('data', {}) or {}
        except Exception as e:
            # Không spam lỗi vì endpoint này có thể bị giới hạn quyền; vẫn fallback.
            logger.warning(f"⚠️ Không lấy được leverageBracket, fallback cache: {e}")
            return _LEVERAGE_BRACKET_CACHE.get('data', {}) or {}

    @staticmethod
    def _spread_pct_from_book(item):
        try:
            bid = float(item.get('bidPrice', 0) or 0)
            ask = float(item.get('askPrice', 0) or 0)
            mid = (bid + ask) / 2.0
            if bid <= 0 or ask <= 0 or mid <= 0 or ask < bid:
                return 999.0
            return (ask - bid) / mid * 100.0
        except Exception:
            return 999.0

    @staticmethod
    def _base_coin_score(coin, spread_pct=0.0, max_leverage=0):
        # Điểm nền cực đơn giản: biến động giá 24h càng lớn càng ưu tiên.
        try:
            return abs(float(coin.get('price_change_percent', 0.0) or 0.0))
        except Exception:
            return 0.0

    def _coin_passes_filters(self, coin, book_map, lev_map, excluded_coins):
        """Chỉ lọc thứ bắt buộc: active/blacklist/cooldown và đòn bẩy yêu cầu."""
        try:
            symbol = str(coin.get('symbol', '')).upper()
            if not symbol or symbol in _SYMBOL_BLACKLIST:
                return False, 'blacklist', 0.0, 0.0, 0
            if excluded_coins and symbol in excluded_coins:
                return False, 'active_excluded', 0.0, 0.0, 0
            if self._bot_manager and self._bot_manager.bot_coordinator.is_temp_blacklisted(symbol):
                return False, 'temp_blacklist', 0.0, 0.0, 0
            if self._bot_manager and self._bot_manager.coin_manager.is_coin_active(symbol):
                return False, 'coin_active', 0.0, 0.0, 0
            if time.time() < float(_COIN_LOSS_COOLDOWN.get(symbol, 0) or 0):
                return False, 'cooldown_after_loss', 0.0, 0.0, 0

            lev_info = lev_map.get(symbol) or {}
            max_lev = int(float(lev_info.get('max_leverage', coin.get('max_leverage', 0)) or 0))
            if max_lev <= 0:
                max_lev = int(float(coin.get('max_leverage', 50) or 50))
            min_lev = int(float(_STRATEGY_CONFIG.get('min_allowed_leverage', self.bot_leverage) or self.bot_leverage))
            if max_lev < min_lev:
                return False, 'leverage_low', 0.0, 0.0, max_lev

            base_score = self._base_coin_score(coin, 0.0, max_lev)
            return True, 'ok', base_score, 0.0, max_lev
        except Exception as e:
            return False, f'filter_error:{e}', 0.0, 0.0, 0

    def find_best_coin_with_balance(self, excluded_coins=None):
        """Chọn random một coin hợp lệ, không chấm tín hiệu.

        Chỉ bỏ qua coin blacklist/đang active/cooldown và coin không đạt đòn bẩy yêu cầu.
        Hướng BUY/SELL sẽ random ở BaseBot khi mở vị thế.
        """
        try:
            now = time.time()
            if now - self.last_scan_time < self.scan_cooldown:
                return None
            self.last_scan_time = now

            coins = get_coins_with_info()
            if not coins:
                logger.warning("⚠️ Cache coin trống, không thể tìm coin random.")
                return None

            lev_map = self._get_leverage_bracket_map()
            candidates = []
            for coin in coins:
                ok, reason, base_score, spread, max_lev = self._coin_passes_filters(coin, {}, lev_map, excluded_coins or set())
                if not ok:
                    continue
                candidates.append(coin.copy())

            if not candidates:
                return None

            coin = random.choice(candidates)
            symbol = str(coin.get('symbol', '')).upper()
            logger.info(f"✅ Chọn coin RANDOM {symbol} | không chấm tín hiệu")
            return symbol

        except Exception as e:
            logger.error(f"❌ Lỗi tìm coin random: {str(e)}")
            logger.error(traceback.format_exc())
            return None

class WebSocketManager:
    def __init__(self):
        self.connections = {}
        self.executor = ThreadPoolExecutor(max_workers=2, thread_name_prefix='ws_executor')
        self._lock = threading.RLock()
        self._stop_event = threading.Event()
        self.price_cache = {}
        self.last_price_update = {}

    def add_symbol(self, symbol, callback):
        if not symbol: return
        symbol = symbol.upper()
        with self._lock:
            if symbol not in self.connections:
                self._create_connection(symbol, callback)

    def _create_connection(self, symbol, callback):
        if self._stop_event.is_set(): return
        streams = [f"{symbol.lower()}@trade"]
        url = f"wss://fstream.binance.com/stream?streams={'/'.join(streams)}"

        def on_message(ws, message):
            try:
                data = json.loads(message)
                if 'data' in data:
                    sym = data['data']['s']
                    price = float(data['data']['p'])
                    current_time = time.time()
                    if (sym in self.last_price_update and
                        current_time - self.last_price_update[sym] < 0.1):
                        return
                    self.last_price_update[sym] = current_time
                    self.price_cache[sym] = price
                    callback(price)
            except Exception as e:
                logger.error(f"Lỗi tin nhắn WebSocket {symbol}: {str(e)}")

        def on_error(ws, error):
            logger.error(f"Lỗi WebSocket {symbol}: {str(error)}")
            with self._lock:
                conn = self.connections.get(symbol)
                should_reconnect = (not self._stop_event.is_set()) and conn and not conn.get('removing')
            if should_reconnect:
                time.sleep(5)
                self._reconnect(symbol, callback)

        def on_close(ws, close_status_code, close_msg):
            logger.info(f"WebSocket đã đóng {symbol}: {close_status_code} - {close_msg}")
            with self._lock:
                conn = self.connections.get(symbol)
                should_reconnect = (not self._stop_event.is_set()) and conn and not conn.get('removing')
            if should_reconnect:
                time.sleep(5)
                self._reconnect(symbol, callback)

        ws = websocket.WebSocketApp(url, on_message=on_message, on_error=on_error, on_close=on_close)
        thread = threading.Thread(target=ws.run_forever, daemon=True, name=f"ws-{symbol}")
        thread.start()
        self.connections[symbol] = {'ws': ws, 'thread': thread, 'callback': callback}
        logger.info(f"🔗 WebSocket đã khởi động cho {symbol}")

    def _reconnect(self, symbol, callback):
        symbol = symbol.upper()
        with self._lock:
            conn = self.connections.get(symbol)
            if self._stop_event.is_set() or not conn or conn.get('removing'):
                return
        logger.info(f"Đang kết nối lại WebSocket cho {symbol}")
        self.remove_symbol(symbol)
        self._create_connection(symbol, callback)

    def remove_symbol(self, symbol):
        if not symbol: return
        symbol = symbol.upper()
        with self._lock:
            conn = self.connections.pop(symbol, None)
            self.price_cache.pop(symbol, None)
            self.last_price_update.pop(symbol, None)
        if conn:
            conn['removing'] = True
            conn['callback'] = None
            try:
                conn['ws'].keep_running = False
                conn['ws'].close()
            except Exception as e:
                logger.error(f"Lỗi đóng WebSocket {symbol}: {str(e)}")
            try:
                th = conn.get('thread')
                if th and th.is_alive():
                    th.join(timeout=0.2)
            except Exception:
                pass
            logger.info(f"WebSocket đã xóa cho {symbol}")

    def stop(self):
        self._stop_event.set()
        for symbol in list(self.connections.keys()):
            self.remove_symbol(symbol)
        self.executor.shutdown(wait=False)

class RealtimeKlineManager:
    def __init__(self):
        self.connections = {}
        self._lock = threading.RLock()
        self._stop_event = threading.Event()
        self.executor = ThreadPoolExecutor(max_workers=2)
        self.candle_data = {}
        self.prev_candle_data = {}
        self.callbacks = defaultdict(list)

    def _current_interval(self):
        return _normalize_interval(_STRATEGY_CONFIG.get('current_interval', _STRATEGY_CONFIG.get('signal_interval', '1m')))

    def add_symbol(self, symbol, callback):
        symbol = symbol.upper()
        with self._lock:
            interval = self._current_interval()
            conn = self.connections.get(symbol)
            if (not conn) or conn.get('interval') != interval:
                if conn:
                    self.remove_symbol(symbol)
                self._load_initial_candles(symbol)
                self._connect(symbol)
            if callback not in self.callbacks[symbol]:
                self.callbacks[symbol].append(callback)

    def _to_candle_dict(self, arr, symbol, is_final=True, interval=None):
        interval = interval or self._current_interval()
        return {
            'symbol': symbol, 'interval': interval,
            'open': float(arr[1]), 'high': float(arr[2]), 'low': float(arr[3]),
            'close': float(arr[4]), 'volume': float(arr[5]),
            'quote_volume': float(arr[7]) if len(arr) > 7 else float(arr[5]) * float(arr[4]),
            'num_trades': int(arr[8]) if len(arr) > 8 else 0,
            'taker_buy_base_volume': float(arr[9]) if len(arr) > 9 else 0.0,
            'taker_buy_quote_volume': float(arr[10]) if len(arr) > 10 else 0.0,
            'is_final': is_final, 'time': int(arr[0]), 'close_time': int(arr[6]),
            'update_ts': time.time()
        }

    def _load_initial_candles(self, symbol):
        try:
            interval = self._current_interval()
            url = "https://fapi.binance.com/fapi/v1/klines"
            data = binance_api_request(url, params={"symbol": symbol.upper(), "interval": interval, "limit": 2})
            if data and len(data) >= 2:
                self.candle_data[symbol] = self._to_candle_dict(data[-1], symbol, is_final=False, interval=interval)
                self.prev_candle_data[symbol] = self._to_candle_dict(data[-2], symbol, is_final=True, interval=interval)
        except Exception as e:
            logger.error(f"Lỗi nạp nến ban đầu real-force-candle {symbol}: {e}")

    def _connect(self, symbol):
        interval = self._current_interval()
        stream = f"{symbol.lower()}@kline_{interval}"
        url = f"wss://fstream.binance.com/ws/{stream}"

        def on_message(ws, message):
            try:
                data = json.loads(message)
                k = data['k']
                if k['i'] != interval:
                    return
                candle = {
                    'symbol': symbol, 'interval': interval,
                    'open': float(k['o']), 'high': float(k['h']), 'low': float(k['l']),
                    'close': float(k['c']), 'volume': float(k['v']),
                    'quote_volume': float(k.get('q', 0.0)),
                    'num_trades': int(k.get('n', 0)),
                    'taker_buy_base_volume': float(k.get('V', 0.0)),
                    'taker_buy_quote_volume': float(k.get('Q', 0.0)),
                    'is_final': k['x'], 'time': k['t'], 'close_time': k['T'],
                    'update_ts': time.time()
                }
                if candle['is_final']:
                    old_prev = self.prev_candle_data.get(symbol)
                    candle['prev_for_signal'] = old_prev.copy() if old_prev else None
                    self.candle_data.pop(symbol, None)
                else:
                    self.candle_data[symbol] = candle

                for cb in list(self.callbacks.get(symbol, [])):
                    try:
                        cb(symbol, candle)
                    except Exception as cb_err:
                        logger.error(f"Lỗi callback kline {symbol}: {cb_err}")

                if candle['is_final']:
                    self.prev_candle_data[symbol] = candle.copy()
            except Exception as e:
                logger.error(f"Lỗi kline {interval} WS {symbol}: {e}")

        def on_error(ws, error):
            logger.error(f"Kline {interval} WS error {symbol}: {error}")
            with self._lock:
                conn = self.connections.get(symbol)
                should_reconnect = (not self._stop_event.is_set()) and conn and not conn.get('removing')
            if should_reconnect:
                time.sleep(5)
                self._reconnect(symbol)

        def on_close(ws, close_status_code, close_msg):
            logger.info(f"Kline {interval} WS closed {symbol}")
            with self._lock:
                conn = self.connections.get(symbol)
                should_reconnect = (not self._stop_event.is_set()) and conn and not conn.get('removing')
            if should_reconnect:
                time.sleep(5)
                self._reconnect(symbol)

        ws = websocket.WebSocketApp(url, on_message=on_message, on_error=on_error, on_close=on_close)
        thread = threading.Thread(target=ws.run_forever, daemon=True, name=f"kline-{interval}-{symbol}")
        thread.start()
        self.connections[symbol] = {'ws': ws, 'thread': thread, 'interval': interval}
        logger.info(f"🔗 Kline WebSocket {interval} cho {symbol}")

    def _reconnect(self, symbol):
        symbol = symbol.upper()
        with self._lock:
            conn = self.connections.get(symbol)
            if self._stop_event.is_set() or not conn or conn.get('removing'):
                return
        self.remove_symbol(symbol)
        self._load_initial_candles(symbol)
        self._connect(symbol)

    def remove_symbol(self, symbol):
        symbol = symbol.upper()
        with self._lock:
            conn = self.connections.pop(symbol, None)
            self.callbacks.pop(symbol, None)
            self.candle_data.pop(symbol, None)
            self.prev_candle_data.pop(symbol, None)
        if conn:
            conn['removing'] = True
            try:
                conn['ws'].keep_running = False
                conn['ws'].close()
            except Exception:
                pass
            try:
                th = conn.get('thread')
                if th and th.is_alive():
                    th.join(timeout=0.2)
            except Exception:
                pass

    def get_candle(self, symbol):
        return self.candle_data.get(symbol.upper())

    def get_prev_candle(self, symbol):
        return self.prev_candle_data.get(symbol.upper())

    def get_prev2_candle(self, symbol):
        return None

    def get_prev15_candle(self, symbol):
        return None

    def get_recent_1m_history(self, symbol):
        return []

    def stop(self):
        self._stop_event.set()
        for sym in list(self.connections.keys()):
            self.remove_symbol(sym)
        self.executor.shutdown(wait=False)

class BaseBot:
    def __init__(self, symbol, lev, percent, tp, sl, ws_manager, api_key, api_secret,
                 telegram_bot_token, telegram_chat_id, strategy_name, config_key=None, bot_id=None,
                 coin_manager=None, symbol_locks=None, max_coins=1, bot_coordinator=None,
                 kline_manager=None,   # Thêm kline manager
                 **kwargs):

        self.max_coins = 1
        self.active_symbols = []
        self.symbol_data = {}
        self.symbol = symbol.upper() if symbol else None

        self.lev = lev
        self.percent = percent
        self.tp = tp if tp else None
        self.sl = sl if sl else None
        self.ws_manager = ws_manager
        self.kline_manager = kline_manager
        self.api_key = api_key
        self.api_secret = api_secret
        self.telegram_bot_token = telegram_bot_token
        self.telegram_chat_id = telegram_chat_id
        self.strategy_name = strategy_name
        self.config_key = config_key
        self.bot_id = bot_id or f"{strategy_name}_{int(time.time())}_{random.randint(1000, 9999)}"

        self.status = "searching" if not symbol else "waiting"
        self._stop = False

        self.current_processing_symbol = None
        self.last_trade_completion_time = 0
        self.trade_cooldown = 30

        self.last_error_log_time = 0
        self.last_memory_cleanup = 0

        self.margin_safety_threshold = 1.05
        self.margin_safety_interval = 60
        self.last_margin_safety_check = 0

        self.coin_manager = coin_manager or CoinManager()
        self.symbol_locks = symbol_locks or defaultdict(threading.RLock)
        self.coin_finder = SmartCoinFinder(api_key, api_secret)
        self.coin_finder.bot_leverage = self.lev

        self.find_new_bot_after_close = True
        self.bot_creation_time = time.time()

        self.execution_lock = threading.RLock()
        self.last_execution_time = 0
        self.execution_cooldown = 1

        self.bot_coordinator = bot_coordinator or BotExecutionCoordinator()

        self.enable_balance_orders = False
        self.balance_config = {}

        self.consecutive_failures = 0
        self.failure_cooldown_until = 0

        self.realtime_signal = {}        # symbol -> 'BUY'/'SELL'/None
        self.last_signal_time = {}       # symbol -> timestamp
        self.signal_cache_ttl = 2        # giây
        self.exit_candidate = {}          # symbol -> {'side': ..., 'since': ...}

        # Thống kê lời/lỗ đã đóng trong phiên bot hiện tại.
        # Số này tính theo lệnh bot tự đóng; nếu người dùng đóng tay trên Binance,
        # bot vẫn đồng bộ vị thế thật nhưng có thể không lấy được PnL đã khớp.
        self.closed_win_usd = 0.0
        self.closed_loss_usd = 0.0
        self.closed_trade_count = 0
        self.win_trade_count = 0
        self.loss_trade_count = 0
        self.last_closed_roi = None
        self.last_closed_pnl = None

        self._pending_reverse = False
        self._reverse_symbol = None
        self._reverse_side = None

        if symbol:
            self._add_symbol(symbol)

        self.thread = threading.Thread(target=self._run, daemon=True, name=f"bot-{self.bot_id[-8:]}")
        self.thread.start()

        strategy_tp = float(_STRATEGY_CONFIG.get('strategy_tp_roi', 0.0) or 0.0)
        strategy_sl = float(_STRATEGY_CONFIG.get('strategy_sl_roi', 0.0) or 0.0)
        tp_sl_info = f" | TP chiến lược: {strategy_tp}%" if strategy_tp > 0 else (f" | TP bot: {self.tp}%" if self.tp else " | TP: Tắt")
        tp_sl_info += f" | SL chiến lược: {strategy_sl}%" if strategy_sl > 0 else (f" | SL bot: {self.sl}%" if self.sl else " | SL: Tắt")
        self.log(f"🟢 Bot {strategy_name} đã khởi động | 1 coin | Đòn bẩy: {lev}x | Vốn: {percent}% | Tín hiệu: RANDOM BUY/SELL | Thoát: TP/SL + bảo vệ lợi nhuận{tp_sl_info}")

    def _run(self):
        last_coin_search_log = 0
        log_interval = 30
        last_no_coin_found_log = 0

        while not self._stop:
            try:
                current_time = time.time()

                if current_time - self.last_memory_cleanup > 60:
                    self.last_memory_cleanup = current_time
                    cleanup_runtime_caches(self.active_symbols, aggressive=True)

                if current_time < self.failure_cooldown_until:
                    time.sleep(1)
                    continue

                if current_time - self.last_margin_safety_check > self.margin_safety_interval:
                    self.last_margin_safety_check = current_time
                    if self._check_margin_safety():
                        time.sleep(5)
                        continue

                if not self.active_symbols:
                    search_permission = self.bot_coordinator.request_coin_search(self.bot_id)

                    if search_permission:
                        if current_time - last_coin_search_log > log_interval:
                            queue_info = self.bot_coordinator.get_queue_info()
                            self.log(f"🔍 Đang tìm coin (vị trí: 1/{queue_info['queue_size'] + 1})...")
                            last_coin_search_log = current_time

                        found_coin = self.coin_finder.find_best_coin_with_balance(
                            excluded_coins=self.coin_manager.get_active_coins()
                        )

                        if found_coin:
                            self.bot_coordinator.bot_has_coin(self.bot_id)
                            self._add_symbol(found_coin)
                            self.bot_coordinator.finish_coin_search(self.bot_id, found_coin, has_coin_now=True)
                            self.log(f"✅ Đã tìm thấy coin random: {found_coin}, chuẩn bị vào lệnh random...")
                            last_coin_search_log = 0
                        else:
                            self.bot_coordinator.finish_coin_search(self.bot_id)
                            if current_time - last_no_coin_found_log > 60:
                                self.log(f"❌ Không tìm thấy coin hợp lệ để random")
                                last_no_coin_found_log = current_time
                    else:
                        queue_pos = self.bot_coordinator.get_queue_position(self.bot_id)
                        if queue_pos > 0:
                            if current_time - last_coin_search_log > log_interval:
                                last_coin_search_log = current_time
                        time.sleep(2)

                    time.sleep(5)
                    continue

                if self._pending_reverse:
                    self._pending_reverse = False
                    self._reverse_symbol = None
                    self._reverse_side = None

                for symbol in self.active_symbols.copy():
                    position_opened = self._process_single_symbol(symbol)
                    if position_opened:
                        self.log(f"🎯 Đã vào lệnh thành công {symbol}, chuyển quyền tìm coin...")
                        next_bot = self.bot_coordinator.finish_coin_search(self.bot_id)
                        if next_bot:
                            self.log(f"🔄 Đã chuyển quyền tìm coin cho bot: {next_bot}")
                        break

                time.sleep(1)

            except Exception as e:
                if time.time() - self.last_error_log_time > 10:
                    self.log(f"❌ Lỗi hệ thống: {str(e)}")
                    self.last_error_log_time = time.time()
                time.sleep(5)

    def _process_single_symbol(self, symbol):
        try:
            if symbol not in self.symbol_data:
                return False
            symbol_info = self.symbol_data[symbol]
            current_time = time.time()

            if not symbol_info['position_open'] and current_time - symbol_info.get('added_time', current_time) > 300:
                self.log(f"⏰ {symbol} đã chờ vào lệnh quá 5 phút, dừng để tìm coin khác")
                self.stop_symbol(symbol, failed=True)
                return False

            if symbol_info['position_open']:
                # Đồng bộ vị thế thật với Binance trước khi xét TP/SL và bảo vệ lợi nhuận.
                # Việc này giúp bot biết nhanh khi người dùng đóng lệnh trực tiếp trên Binance,
                # tránh local vẫn tưởng còn vị thế rồi tính TP/SL sai.
                if not self._sync_symbol_position(symbol):
                    return False

                self._check_symbol_tp_sl(symbol)
                # Chiến lược random không đảo chiều theo tín hiệu; lệnh chỉ thoát bằng TP/SL hoặc bảo vệ lợi nhuận.
                return False
            else:
                if self._pending_reverse and self._reverse_symbol == symbol:
                    return False

                if (current_time - symbol_info['last_trade_time'] > 30 and
                    current_time - symbol_info['last_close_time'] > 30):
                    details = self._get_fresh_realtime_signal(symbol, mode='entry', return_details=True)
                    signal = details.get('signal')
                    if signal is None:
                        if symbol in self.symbol_data:
                            self.symbol_data[symbol]['last_entry_check_reason'] = details.get('reason')
                        return False

                    if self._open_symbol_position(symbol, signal, skip_signal_check=False):
                        symbol_info['last_trade_time'] = current_time
                        return True
                return False
        except Exception as e:
            self.log(f"❌ Lỗi xử lý {symbol}: {str(e)}")
            return False

    def _add_symbol(self, symbol):
        symbol = symbol.upper()
        if symbol in self.active_symbols:
            return
        if len(self.active_symbols) >= self.max_coins:
            self.log(f"⚠️ Bot đã có {len(self.active_symbols)} coin theo dõi, không thêm {symbol}")
            return
        self.active_symbols.append(symbol)
        self.symbol_data[symbol] = {
            'position_open': False,
            'entry': 0,
            'entry_base': 0,
            'side': None,
            'qty': 0,
            'status': 'waiting',
            'last_price': 0,
            'last_price_time': 0,
            'last_trade_time': 0,
            'last_close_time': 0,
            'last_position_check': 0,
            'failed_attempts': 0,
            'margin_used': 0.0,
            'reverse_count': 0,
            'best_roi': None,
            'opened_time': 0.0,
            'order_busy': False,
            'last_reverse_candle_time': 0,
            'added_time': time.time()
        }
        self.ws_manager.add_symbol(symbol, lambda p, s=symbol: self._handle_price_update(s, p))
        # Random signal không cần kline websocket; chỉ giữ price websocket để quản lý TP/SL.
        self.coin_manager.register_coin(symbol)
        self.log(f"➕ Đã thêm {symbol} vào theo dõi")

    def _handle_price_update(self, symbol, price):
        if symbol not in self.symbol_data:
            return
        self.symbol_data[symbol]['last_price'] = price
        self.symbol_data[symbol]['last_price_time'] = time.time()

    def _on_kline_update(self, symbol, candle):
        """Callback từ kline manager.
        Chỉ cập nhật trạng thái tín hiệu mới nhất để xem/log.
        Quyết định đóng/đảo chiều vẫn được tính lại trực tiếp trong _check_realtime_exit().
        """
        if symbol not in self.symbol_data:
            return

        # Chiến lược mới chỉ xét nến hiện tại. Không gọi REST trong callback kline để tránh
        # hàng đợi callback/API làm Railway tăng RAM theo thời gian.
        prev = candle.get('prev_for_signal') or (self.kline_manager.get_prev_candle(symbol) if self.kline_manager else {})
        signal = self._compute_signal_from_candle(candle, prev or {}, None, recent_1m_history=[])
        self.realtime_signal[symbol] = signal
        self.last_signal_time[symbol] = time.time()
        self.symbol_data[symbol]['realtime_signal'] = signal

    def _compute_signal_from_candle(self, current_candle=None, prev_candle=None, prev15_candle=None, mode='entry', return_details=False, recent_1m_history=None):
        """Tín hiệu random BUY/SELL, không dùng dữ liệu nến."""
        try:
            signal = random.choice(('BUY', 'SELL'))
            candle_time = 0
            if isinstance(current_candle, dict):
                candle_time = int(current_candle.get('time', 0) or 0)
            details = {
                'signal': signal,
                'score': 100.0,
                'reason': f'RANDOM_SIGNAL {signal} | no signal filters',
                'is_spike': False,
                'progress': 1.0,
                'current_candle_time': candle_time,
                'source': 'RANDOM',
            }
            return details if return_details else signal
        except Exception as e:
            logger.error(f"Lỗi compute signal random: {e}")
            details = {'signal': None, 'score': 0, 'reason': 'error', 'is_spike': False, 'source': 'RANDOM'}
            return details if return_details else None

    def _get_fresh_realtime_signal(self, symbol, mode='entry', return_details=False):
        """Trả tín hiệu random ngay lập tức, không gọi REST/WS để kiểm tra điều kiện tín hiệu."""
        try:
            symbol = symbol.upper()
            signal = random.choice(('BUY', 'SELL'))
            details = {
                'symbol': symbol,
                'signal': signal,
                'score': 100.0,
                'reason': f'RANDOM_SIGNAL {signal} | no signal filters',
                'is_spike': False,
                'progress': 1.0,
                'current_candle_time': 0,
                'source': 'RANDOM',
                'quote_volume': 0.0,
                'taker_buy_quote': 0.0,
                'taker_sell_quote': 0.0,
                'num_trades': 0,
            }
            self.realtime_signal[symbol] = signal
            self.last_signal_time[symbol] = time.time()
            if symbol in self.symbol_data:
                self.symbol_data[symbol]['realtime_signal'] = signal
                self.symbol_data[symbol]['last_signal_details'] = details
            return details if return_details else signal
        except Exception as e:
            logger.error(f"Lỗi lấy tín hiệu random {symbol}: {e}")
            details = {'signal': None, 'score': 0, 'reason': 'error', 'is_spike': False, 'source': 'RANDOM'}
            return details if return_details else None

    def _get_rest_current_and_prev_candle(self, symbol):
        """REST fallback: current + previous của khung signal_interval."""
        try:
            curr, prev, market, market_history = _fetch_rest_1m15m_signal_data(symbol)
            if not curr or not prev:
                return None, None, None, []
            interval = _normalize_interval(_STRATEGY_CONFIG.get('current_interval', _STRATEGY_CONFIG.get('signal_interval', '1m')))
            def conv(arr, is_final, used_interval):
                return {
                    'symbol': symbol.upper(), 'interval': used_interval,
                    'open': float(arr[1]), 'high': float(arr[2]), 'low': float(arr[3]),
                    'close': float(arr[4]), 'volume': float(arr[5]),
                    'quote_volume': float(arr[7]) if len(arr) > 7 else float(arr[5]) * float(arr[4]),
                    'num_trades': int(arr[8]) if len(arr) > 8 else 0,
                    'taker_buy_base_volume': float(arr[9]) if len(arr) > 9 else 0.0,
                    'taker_buy_quote_volume': float(arr[10]) if len(arr) > 10 else 0.0,
                    'is_final': is_final, 'time': int(arr[0]), 'close_time': int(arr[6]),
                    'update_ts': time.time()
                }
            return conv(curr, False, interval), conv(prev, True, interval), None, []
        except Exception as e:
            logger.error(f"Lỗi REST fallback lấy nến Real Force Candle {symbol}: {e}")
            return None, None, None, []
    def _check_realtime_exit(self, symbol):
        """Đã tắt đảo chiều theo tín hiệu.

        Với chiến lược random, bot không dùng tín hiệu ngược để đóng/đảo lệnh nữa.
        Lệnh đang mở chỉ được quản lý bởi TP/SL, emergency stop và bảo vệ lợi nhuận.
        """
        return

    def _calc_roi_pnl_for_symbol(self, symbol, pos=None, price=None):
        """Tính ROI/PnL hiện tại theo vị thế thật Binance nếu có.

        ROI dùng cùng công thức TP/SL: biến động giá * đòn bẩy.
        PnL ưu tiên lấy unRealizedProfit từ Binance; nếu không có thì ước tính theo entry/qty/giá hiện tại.
        """
        try:
            data = self.symbol_data.get(symbol, {})
            entry = float((pos or {}).get('entryPrice') or data.get('entry') or 0)
            amt = float((pos or {}).get('positionAmt') or data.get('qty') or 0)
            if entry <= 0 or abs(amt) <= 0:
                return None, None
            side = 'BUY' if amt > 0 else 'SELL'
            mark_price = float((pos or {}).get('markPrice') or 0)
            current_price = float(price or mark_price or self._get_fresh_price(symbol) or 0)
            if current_price <= 0:
                return None, None
            if side == 'BUY':
                roi = (current_price - entry) / entry * 100 * self.lev
                pnl_est = (current_price - entry) * abs(amt)
            else:
                roi = (entry - current_price) / entry * 100 * self.lev
                pnl_est = (entry - current_price) * abs(amt)
            try:
                pnl = float((pos or {}).get('unRealizedProfit'))
            except Exception:
                pnl = pnl_est
            return float(roi), float(pnl)
        except Exception as e:
            logger.error(f"Lỗi tính ROI/PnL {symbol}: {e}")
            return None, None

    def _record_closed_trade_stats(self, symbol, roi=None, pnl=None):
        """Cộng dồn thống kê thắng/thua sau khi bot xác nhận đóng vị thế."""
        try:
            if pnl is None:
                return
            pnl = float(pnl)
            roi_val = None if roi is None else float(roi)
            self.closed_trade_count += 1
            self.last_closed_roi = roi_val
            self.last_closed_pnl = pnl
            if pnl >= 0:
                self.closed_win_usd += pnl
                self.win_trade_count += 1
                if roi_val is not None:
                    self.log(f"🏆 {symbol} - Đóng lệnh THẮNG | ROI: {roi_val:.2f}% | Lời: +{pnl:.4f} USDT")
                else:
                    self.log(f"🏆 {symbol} - Đóng lệnh THẮNG | Lời: +{pnl:.4f} USDT")
            else:
                self.closed_loss_usd += abs(pnl)
                self.loss_trade_count += 1
                cooldown = float(_STRATEGY_CONFIG.get('coin_cooldown_after_loss_sec', 180) or 0)
                if cooldown > 0:
                    _COIN_LOSS_COOLDOWN[str(symbol).upper()] = time.time() + cooldown
                if roi_val is not None:
                    self.log(f"💔 {symbol} - Đóng lệnh THUA | ROI: {roi_val:.2f}% | Lỗ: {pnl:.4f} USDT | nghỉ coin {cooldown:.0f}s")
                else:
                    self.log(f"💔 {symbol} - Đóng lệnh THUA | Lỗ: {pnl:.4f} USDT | nghỉ coin {cooldown:.0f}s")
        except Exception as e:
            logger.error(f"Lỗi ghi thống kê đóng lệnh {symbol}: {e}")


    def _check_symbol_tp_sl(self, symbol):
        if symbol not in self.symbol_data:
            return
        data = self.symbol_data[symbol]
        if not data['position_open']:
            return

        entry = float(data.get('entry', 0) or 0)
        if entry <= 0 or abs(float(data.get('qty', 0) or 0)) <= 0:
            return

        current_price = self._get_fresh_price(symbol)
        if current_price <= 0:
            return

        if data['side'] == 'BUY':
            roi = (current_price - entry) / entry * 100 * self.lev
        else:
            roi = (entry - current_price) / entry * 100 * self.lev

        max_hold = float(_STRATEGY_CONFIG.get('max_hold_seconds', 0.0) or 0.0)
        opened_time = float(data.get('opened_time', 0.0) or 0.0)
        if max_hold > 0 and opened_time > 0 and (time.time() - opened_time) >= max_hold:
            self.log(f"⏱️ {symbol} - Giữ quá {max_hold:.0f}s | ROI hiện tại {roi:.2f}%, đóng lệnh để tránh coin rác trả lực")
            self._close_symbol_position(symbol, reason=f"Max hold {max_hold:.0f}s")
            return

        if float(_STRATEGY_CONFIG.get('profit_protect_enabled', 1.0)) >= 0.5:
            best_roi = data.get('best_roi')
            if best_roi is None:
                best_roi = roi
            best_roi = max(float(best_roi), float(roi))
            data['best_roi'] = best_roi
            start_roi = float(_STRATEGY_CONFIG.get('profit_protect_start_roi', 10.0))
            pullback_roi = float(_STRATEGY_CONFIG.get('profit_protect_pullback_roi', 8.0))
            if best_roi >= start_roi and (best_roi - roi) >= pullback_roi:
                self.log(f"🔒 {symbol} - Hút lực từ đỉnh: ROI đỉnh {best_roi:.2f}% tụt còn {roi:.2f}%, đóng lệnh bảo vệ lời")
                self._close_symbol_position(symbol, reason="Profit protect peak pullback")
                return

        _, pnl_now = self._calc_roi_pnl_for_symbol(symbol, price=current_price)
        pnl_txt = f" | PnL tạm tính {pnl_now:.4f} USDT" if pnl_now is not None else ""

        emergency_stop = float(_STRATEGY_CONFIG.get('emergency_stop_roi', 120.0) or 0.0)
        if emergency_stop > 0 and roi <= -emergency_stop:
            self.log(f"🚨 {symbol} - Cắt lỗ khẩn cấp {emergency_stop:.1f}% | ROI hiện tại {roi:.2f}%{pnl_txt}, đóng lệnh ngay")
            self._close_symbol_position(symbol, reason=f"Emergency SL {emergency_stop:.1f}%")
            return


        # TP/SL trong Chiến lược được đọc realtime để có thể chỉnh sau khi bot đã vào lệnh.
        strategy_tp = float(_STRATEGY_CONFIG.get('strategy_tp_roi', 0.0) or 0.0)
        strategy_sl = float(_STRATEGY_CONFIG.get('strategy_sl_roi', 0.0) or 0.0)
        effective_tp = strategy_tp if strategy_tp > 0 else (self.tp or 0)
        effective_sl = strategy_sl if strategy_sl > 0 else (self.sl or 0)

        if effective_tp and roi >= effective_tp:
            self.log(f"🎯 {symbol} - Đạt TP {effective_tp}% | ROI hiện tại {roi:.2f}%{pnl_txt}, đóng lệnh")
            self._close_symbol_position(symbol, reason=f"TP {effective_tp}%")
            return
        if effective_sl and roi <= -abs(effective_sl):
            self.log(f"🛡️ {symbol} - Đạt SL {effective_sl}% | ROI hiện tại {roi:.2f}%{pnl_txt}, đóng lệnh")
            self._close_symbol_position(symbol, reason=f"SL {effective_sl}%")
            return

    def _close_symbol_position(self, symbol, reason="", reverse_side=None):
        with self.symbol_locks[symbol]:
            try:
                if symbol not in self.symbol_data:
                    return False
                if not self.symbol_data[symbol]['position_open']:
                    return False
                real_pos = self._force_check_position(symbol)
                if real_pos and real_pos.get('_api_error'):
                    self.log(f"⚠️ {symbol} - Không xác minh được vị thế thật từ Binance, không đóng/reset để tránh mất kiểm soát")
                    return False
                if not real_pos:
                    self.log(f"ℹ️ {symbol} - Binance xác nhận không còn vị thế, reset trạng thái và tiếp tục theo dõi coin.")
                    self._reset_symbol_position(symbol)
                    return True

                close_roi, close_pnl = self._calc_roi_pnl_for_symbol(symbol, pos=real_pos)

                qty = abs(float(real_pos.get('positionAmt', 0)))
                if qty == 0:
                    self.log(f"ℹ️ {symbol} - Vị thế đã đóng, reset.")
                    self._reset_symbol_position(symbol)
                    return True

                side = self.symbol_data[symbol]['side']
                prev_margin_used = float(self.symbol_data[symbol].get('margin_used', 0.0) or 0.0)
                prev_reverse_count = int(self.symbol_data[symbol].get('reverse_count', 0) or 0)
                if prev_margin_used <= 0:
                    try:
                        prev_margin_used = (qty * self._get_fresh_price(symbol)) / max(float(self.lev), 1.0)
                    except Exception:
                        prev_margin_used = 0.0
                close_side = "SELL" if side == "BUY" else "BUY"

                cancel_all_orders(symbol, self.api_key, self.api_secret)
                time.sleep(1)

                result = place_order(symbol, close_side, qty, self.api_key, self.api_secret)
                invalidate_position_cache(symbol, self.api_key)
                if result and 'orderId' in result:
                    closed_ok, last_pos = self._wait_until_position_closed(symbol)
                    if not closed_ok:
                        remain_amt = 0.0
                        try:
                            remain_amt = abs(float(last_pos.get('positionAmt', 0) or 0)) if last_pos else 0.0
                        except Exception:
                            remain_amt = 0.0
                        if remain_amt > 0:
                            self.log(f"⚠️ {symbol} - Lệnh đóng đã gửi nhưng Binance vẫn báo còn vị thế {remain_amt}. Không reset local, sẽ kiểm tra lại vòng sau.")
                            self._sync_symbol_position(symbol, force=True)
                            return False

                    roi_txt = f" | ROI: {close_roi:.2f}%" if close_roi is not None else ""
                    pnl_txt = f" | PnL: {close_pnl:.4f} USDT" if close_pnl is not None else ""
                    self.log(f"🔴 Đã đóng vị thế {symbol} | Lý do: {reason}{roi_txt}{pnl_txt}")
                    self._record_closed_trade_stats(symbol, roi=close_roi, pnl=close_pnl)
                    self._reset_symbol_position(symbol)

                    if reverse_side or "Candle opposite" in reason:
                        reverse_side = reverse_side or ("SELL" if side == "BUY" else "BUY")
                        self._pending_reverse = False
                        self._reverse_symbol = None
                        self._reverse_side = None
                        self.log(f"🔄 Đảo chiều ngay {symbol} sang {reverse_side}")
                        max_rev = int(_STRATEGY_CONFIG.get('max_reverse_count', 999) or 999)
                        if max_rev > 0 and prev_reverse_count >= max_rev:
                            self.log(f"⛔ {symbol} đã đảo {prev_reverse_count} lần liên tiếp, dừng coin để tránh sideway")
                            self.stop_symbol(symbol, failed=True)
                            return True
                        if self._open_symbol_position(symbol, reverse_side, skip_signal_check=True, margin_override=None, is_reverse=True, reverse_count=prev_reverse_count + 1):
                            self.log(f"✅ Đảo chiều thành công trên {symbol}")
                        else:
                            self.log(f"❌ Đảo chiều thất bại trên {symbol}, dừng coin")
                            self.stop_symbol(symbol, failed=True)
                    elif "TP" in reason or "SL" in reason:
                        self.log(f"⛔ {symbol} đóng do TP/SL với cả hai ngưỡng, sẽ tìm coin mới")
                        self._blacklist_and_stop_symbol(symbol, reason=reason)
                    else:
                        self._blacklist_and_stop_symbol(symbol, reason=reason)

                    return True
                else:
                    err_text = ''
                    try:
                        err_text = f" | Phản hồi: {result}" if result else " | Không có phản hồi từ Binance"
                    except Exception:
                        err_text = ''
                    # Nếu đóng thất bại vì thực tế vị thế đã không còn, đồng bộ lại ngay.
                    if not self._sync_symbol_position(symbol, force=True):
                        return True
                    self.log(f"❌ Đóng lệnh {symbol} thất bại{err_text}")
                    return False

            except Exception as e:
                self.log(f"❌ Lỗi đóng vị thế {symbol}: {str(e)}")
                return False

    def _blacklist_and_stop_symbol(self, symbol, reason=""):
        if symbol not in self.active_symbols:
            return
        self.bot_coordinator.add_temp_blacklist(symbol, duration=300)
        self.log(f"⛔ {symbol} đã bị blacklist 5 phút do {reason}")
        self.stop_symbol(symbol, failed=False)

    def _open_symbol_position(self, symbol, side, skip_signal_check=False, margin_override=None, is_reverse=False, reverse_count=0):
        with self.symbol_locks[symbol]:
            try:
                if self.symbol_data.get(symbol, {}).get('position_open'):
                    self.log(f"⚠️ {symbol} local đang có vị thế, không mở thêm")
                    return False

                # Chiến lược random: không kiểm tra lại tín hiệu trước khi mở lệnh.
                # Side đã được chọn ngẫu nhiên ở bước gọi hàm, nên re-check sẽ làm lệch kết quả.

                if not set_leverage(symbol, self.lev, self.api_key, self.api_secret):
                    self.log(f"❌ {symbol} - Không thể cài đặt đòn bẩy {self.lev}x")
                    self.stop_symbol(symbol, failed=True)
                    return False

                total_balance, available_balance = get_total_and_available_balance(self.api_key, self.api_secret)
                margin_balance = get_margin_balance(self.api_key, self.api_secret)
                if margin_balance is None or margin_balance <= 0:
                    self.log(f"❌ {symbol} - Không thể lấy số dư margin")
                    self.stop_symbol(symbol, failed=True)
                    return False

                required_usd = margin_balance * (self.percent / 100)
                sizing_label = f"{self.percent}% số dư margin hiện tại"

                if required_usd <= 0:
                    self.log(f"❌ {symbol} - Vốn vào lệnh quá nhỏ ({required_usd:.2f})")
                    self.stop_symbol(symbol, failed=True)
                    return False

                if available_balance is not None and required_usd > available_balance:
                    self.log(f"⚠️ {symbol} - Vốn tính theo margin ({required_usd:.2f}) > số dư khả dụng ({available_balance:.2f}), vẫn thử lệnh theo yêu cầu margin...")

                current_price = self._get_fresh_price(symbol)
                if current_price <= 0:
                    self.log(f"❌ {symbol} - Lỗi giá")
                    self.stop_symbol(symbol, failed=True)
                    return False

                step_size = get_step_size(symbol)
                min_qty = get_min_qty_from_cache(symbol)
                min_notional = get_min_notional_from_cache(symbol)

                qty = (required_usd * self.lev) / current_price
                if step_size > 0:
                    qty = math.floor(qty / step_size) * step_size
                    qty = round(qty, 8)

                if qty < min_qty:
                    self.log(f"❌ {symbol} - Khối lượng {qty} nhỏ hơn minQty {min_qty}")
                    self.stop_symbol(symbol, failed=True)
                    return False

                notional_value = qty * current_price
                if notional_value < min_notional:
                    self.log(f"❌ {symbol} - Giá trị danh nghĩa {notional_value:.2f} < {min_notional}")
                    self.stop_symbol(symbol, failed=True)
                    return False

                if qty <= 0:
                    self.log(f"❌ {symbol} - Khối lượng không hợp lệ")
                    self.stop_symbol(symbol, failed=True)
                    return False

                cancel_all_orders(symbol, self.api_key, self.api_secret)
                time.sleep(1)

                result = place_order(symbol, side, qty, self.api_key, self.api_secret)
                invalidate_position_cache(symbol, self.api_key)
                if result and 'orderId' in result:
                    executed_qty = float(result.get('executedQty') or result.get('origQty') or qty)
                    avg_price = float(result.get('avgPrice') or current_price)
                    if executed_qty <= 0:
                        executed_qty = qty
                    if avg_price <= 0:
                        avg_price = current_price

                    self.symbol_data[symbol].update({
                        'entry': avg_price,
                        'entry_base': avg_price,
                        'qty': executed_qty if side == "BUY" else -executed_qty,
                        'side': side,
                        'position_open': True,
                        'status': "open",
                        'last_trade_time': time.time(),
                        'margin_used': required_usd,
                        'reverse_count': int(reverse_count) if is_reverse else 0,
                        'best_roi': 0.0,
                        'opened_time': time.time(),
                    })

                    self.bot_coordinator.bot_has_coin(self.bot_id)
                    # Giữ quyền kiểm soát coin cho bot đang có vị thế.
                    # Không release_coin ở đây, nếu không bot khác có thể lấy cùng coin
                    # hoặc coordinator tưởng bot đã nhả coin.

                    self.consecutive_failures = 0
                    message = (f"✅ <b>ĐÃ MỞ VỊ THẾ {symbol}</b>\n"
                               f"🤖 Bot: {self.bot_id}\n📌 Hướng: {side}\n"
                               f"🏷️ Entry: {self.symbol_data[symbol]['entry']:.4f}\n"
                               f"📊 Khối lượng: {abs(self.symbol_data[symbol]['qty']):.4f}\n"
                               f"💵 Vốn vào lệnh: {required_usd:.2f} USDT ({sizing_label})\n"
                               f"💰 Đòn bẩy: {self.lev}x\n")
                    if self.tp: message += f"🎯 TP: {self.tp}% | "
                    if self.sl: message += f"🛡️ SL: {self.sl}%"
                    message += f"\n🔄 Thoát: chỉ TP/SL hoặc bảo vệ lợi nhuận tụt từ đỉnh"
                    self.log(message)
                    return True
                else:
                    error_msg = result.get('msg', 'Lỗi không xác định') if result else 'Không có phản hồi'
                    self.log(f"❌ {symbol} - Lỗi lệnh: {error_msg}")
                    self.stop_symbol(symbol, failed=True)
                    return False

            except Exception as e:
                self.log(f"❌ {symbol} - Lỗi mở vị thế: {str(e)}")
                self.stop_symbol(symbol, failed=True)
                return False

    def _check_margin_safety(self):
        try:
            margin_balance, maint_margin, ratio = get_margin_safety_info(self.api_key, self.api_secret)
            if ratio is not None and ratio < self.margin_safety_threshold:
                self.log(f"🚫 CẢNH BÁO AN TOÀN KÝ QUỸ: tỷ lệ {ratio:.2f}x < {self.margin_safety_threshold}x")
                self.log("⛔ Đóng tất cả vị thế do margin thấp")
                for symbol in self.active_symbols.copy():
                    if self._close_symbol_position(symbol, reason="(Margin safety)"):
                        self._blacklist_and_stop_symbol(symbol, reason="Margin safety")
                return True
            return False
        except Exception as e:
            logger.error(f"Lỗi kiểm tra margin safety: {str(e)}")
            return False

    def get_current_price(self, symbol):
        if symbol in self.symbol_data and self.symbol_data[symbol]['last_price'] > 0:
            return self.symbol_data[symbol]['last_price']
        return get_current_price(symbol)

    def _get_fresh_price(self, symbol):
        data = self.symbol_data.get(symbol)
        if data and time.time() - data.get('last_price_time', 0) < 5:
            return data['last_price']
        price = get_current_price(symbol)
        if price > 0 and data:
            data['last_price'] = price
            data['last_price_time'] = time.time()
        return price

    def _sync_symbol_position(self, symbol, force=False):
        """Đồng bộ local position với Binance khi bot đang giữ lệnh.

        Nguyên tắc an toàn:
        - API lỗi: KHÔNG reset local, vẫn coi như còn vị thế để tiếp tục kiểm soát.
        - Binance xác nhận positionAmt = 0: reset local về trạng thái chờ nhưng vẫn giữ coin theo dõi.
        - Binance xác nhận còn vị thế: cập nhật entry/qty/side theo Binance.
        """
        try:
            if symbol not in self.symbol_data:
                return False
            data = self.symbol_data[symbol]
            if not data.get('position_open'):
                return False

            now = time.time()
            last_sync = float(data.get('last_position_api_sync', 0) or 0)
            if not force and (now - last_sync) < _POSITION_SYNC_INTERVAL:
                return True
            data['last_position_api_sync'] = now

            invalidate_position_cache(symbol, self.api_key)
            ok, pos = get_position_strict(symbol, self.api_key, self.api_secret)
            if not ok:
                logger.warning(f"⚠️ Không đồng bộ được vị thế {symbol} do lỗi API, giữ local để tiếp tục kiểm soát")
                return True

            amt = 0.0
            entry_price = 0.0
            if pos:
                amt = float(pos.get('positionAmt', 0) or 0)
                entry_price = float(pos.get('entryPrice', 0) or 0)

            if abs(amt) <= 0:
                self.log(f"ℹ️ {symbol} - Binance xác nhận không còn vị thế, đồng bộ local về trạng thái chờ và tiếp tục theo dõi coin.")
                self._reset_symbol_position(symbol)
                return False

            real_side = 'BUY' if amt > 0 else 'SELL'
            local_side = data.get('side')
            if local_side in ('BUY', 'SELL') and real_side != local_side:
                self.log(f"⚠️ {symbol} - Binance side {real_side} khác local {local_side}, đồng bộ lại theo Binance")

            data.update({
                'position_open': True,
                'qty': amt,
                'side': real_side,
                'status': 'open'
            })
            if entry_price > 0:
                data['entry'] = entry_price
                data['entry_base'] = entry_price
            return True
        except Exception as e:
            logger.error(f"Lỗi sync vị thế {symbol}: {str(e)}")
            return True

    def _wait_until_position_closed(self, symbol, timeout=None, interval=None):
        """Sau khi gửi lệnh đóng, poll Binance vài lần để chắc chắn positionAmt về 0."""
        timeout = _POSITION_CLOSE_CONFIRM_TIMEOUT if timeout is None else float(timeout)
        interval = _POSITION_CLOSE_CONFIRM_INTERVAL if interval is None else float(interval)
        deadline = time.time() + timeout
        last_pos = None
        while time.time() < deadline:
            try:
                invalidate_position_cache(symbol, self.api_key)
                ok, pos = get_position_strict(symbol, self.api_key, self.api_secret)
                if not ok:
                    # API lỗi, không xác nhận đã đóng. Tiếp tục poll.
                    time.sleep(interval)
                    continue
                last_pos = pos
                amt = float(pos.get('positionAmt', 0) or 0) if pos else 0.0
                if abs(amt) <= 0:
                    return True, pos
            except Exception:
                pass
            time.sleep(interval)
        return False, last_pos

    def _force_check_position(self, symbol):
        try:
            ok, pos = get_position_strict(symbol, self.api_key, self.api_secret)
            if not ok:
                return {'_api_error': True}
            if pos:
                amt = float(pos.get('positionAmt', 0) or 0)
                if abs(amt) > 0:
                    return pos
            return None
        except Exception as e:
            logger.error(f"Lỗi force check position {symbol}: {str(e)}")
            return {'_api_error': True}

    def _check_symbol_position(self, symbol):
        """Kiểm tra vị thế thủ công/có cooldown. Không gọi lặp 2 lần để tránh spam API."""
        try:
            pos = get_position_cached(symbol, self.api_key, self.api_secret, ttl=15.0, force=False)
            if pos and not pos.get('_api_error'):
                amt = float(pos.get('positionAmt', 0))
                if abs(amt) > 0:
                    if not self.symbol_data[symbol]['position_open']:
                        entry_price = float(pos.get('entryPrice', 0))
                        if entry_price == 0:
                            return
                        self.symbol_data[symbol].update({
                            'position_open': True,
                            'entry': entry_price,
                            'entry_base': entry_price,
                            'qty': amt,
                            'side': 'BUY' if amt > 0 else 'SELL',
                            'status': 'open'
                        })
                        self.log(f"📌 Phát hiện vị thế {symbol} từ API")
                else:
                    if self.symbol_data[symbol]['position_open']:
                        self._reset_symbol_position(symbol)
            else:
                if self.symbol_data[symbol]['position_open']:
                    self._reset_symbol_position(symbol)
        except Exception as e:
            logger.error(f"Lỗi kiểm tra vị thế {symbol}: {str(e)}")

    def _reset_symbol_position(self, symbol):
        if symbol in self.symbol_data:
            self.symbol_data[symbol].update({
                'position_open': False,
                'entry': 0,
                'entry_base': 0,
                'side': None,
                'qty': 0,
                'status': 'closed',
                'margin_used': 0.0,
                'best_roi': None,
            })
            now = time.time()
            self.symbol_data[symbol]['last_close_time'] = now
            # Khi vị thế mất/đóng nhưng vẫn giữ coin theo dõi, reset lại mốc chờ để không bị timeout 5 phút ngay lập tức.
            self.symbol_data[symbol]['added_time'] = now

    def stop_symbol(self, symbol, failed=False):
        if symbol not in self.active_symbols:
            return False

        self.log(f"⛔ Đang dừng coin {symbol}...{' (lỗi)' if failed else ''}")

        if self.symbol_data.get(symbol, {}).get('position_open'):
            try:
                self._close_symbol_position(symbol, reason="(Stop by user)")
            except Exception as e:
                self.log(f"❌ Lỗi đóng vị thế khi dừng {symbol}: {str(e)}")

        try:
            self.ws_manager.remove_symbol(symbol)
        except Exception as e:
            self.log(f"❌ Lỗi dừng WebSocket {symbol}: {str(e)}")

        if self.kline_manager:
            try:
                self.kline_manager.remove_symbol(symbol)
            except Exception as e:
                self.log(f"❌ Lỗi dừng Kline WS {symbol}: {str(e)}")

        try:
            self.active_symbols.remove(symbol)
        except ValueError:
            self.log(f"⚠️ {symbol} không có trong active_symbols khi dừng")

        self.coin_manager.unregister_coin(symbol)
        self.realtime_signal.pop(symbol, None)
        self.last_signal_time.pop(symbol, None)
        self.exit_candidate.pop(symbol, None)
        self.symbol_data.pop(symbol, None)
        invalidate_position_cache(symbol, self.api_key)
        cleanup_runtime_caches(self.active_symbols, aggressive=True)

        if failed:
            if hasattr(self, '_bot_manager') and self._bot_manager:
                try:
                    self._bot_manager.bot_coordinator.release_coin(symbol)
                    self._bot_manager.bot_coordinator.add_temp_blacklist(symbol, duration=1800)
                except Exception as e:
                    self.log(f"❌ Lỗi release/blacklist {symbol}: {str(e)}")
            self.consecutive_failures += 1
            cooldown = min(60, 5 * self.consecutive_failures)
            self.failure_cooldown_until = time.time() + cooldown
            self.log(f"⏳ Thất bại lần {self.consecutive_failures}, nghỉ {cooldown}s trước khi tìm coin mới")
        else:
            self.consecutive_failures = 0

        if not self.active_symbols:
            self.bot_coordinator.bot_lost_coin(self.bot_id)
            self.bot_coordinator.finish_coin_search(self.bot_id)
            self.status = "searching"
            self.log("🔍 Chuyển sang trạng thái tìm coin mới")

        self.log(f"✅ Đã dừng coin {symbol}")
        return True

    def stop_all_symbols(self):
        count = 0
        for symbol in self.active_symbols.copy():
            if self.stop_symbol(symbol):
                count += 1
        return count

    def stop(self):
        self.log("🔴 Bot đang dừng...")
        self._stop = True
        self.stop_all_symbols()
        if self.bot_coordinator:
            self.bot_coordinator.remove_bot(self.bot_id)
        self.log("✅ Bot đã dừng")

    def log(self, message):
        logger.info(f"[{self.bot_id}] {message}")
        if self.telegram_bot_token and self.telegram_chat_id:
            send_telegram(f"<b>{self.bot_id}</b>: {message}",
                         chat_id=self.telegram_chat_id,
                         bot_token=self.telegram_bot_token,
                         default_chat_id=self.telegram_chat_id)

class GlobalMarketBot(BaseBot):
    pass

class BotManager:
    def __init__(self, api_key=None, api_secret=None, telegram_bot_token=None, telegram_chat_id=None):
        self.ws_manager = WebSocketManager()
        self.kline_manager = RealtimeKlineManager()   # Thêm kline manager
        self.bots = {}
        self.running = True
        self.start_time = time.time()
        self.user_states = {}

        self.api_key = api_key
        self.api_secret = api_secret
        self.telegram_bot_token = telegram_bot_token
        self.telegram_chat_id = telegram_chat_id

        self.bot_coordinator = BotExecutionCoordinator()
        self.coin_manager = CoinManager()
        self.symbol_locks = defaultdict(threading.RLock)

        if api_key and api_secret:
            self._verify_api_connection()
            self.log("🟢 HỆ THỐNG BOT RANDOM SIGNAL - CLEAN")
            self._initialize_cache()
            self._cache_thread = threading.Thread(target=self._cache_updater, daemon=True, name='cache_updater')
            self._cache_thread.start()
            self.telegram_thread = threading.Thread(target=self._telegram_listener, daemon=True, name='telegram')
            self.telegram_thread.start()
            if self.telegram_chat_id:
                self.send_main_menu(self.telegram_chat_id)
        else:
            self.log("⚡ BotManager đã khởi động ở chế độ không cấu hình")

    def _initialize_cache(self):
        logger.info("🔄 Hệ thống đang khởi tạo cache...")
        if refresh_coins_cache():
            update_coins_volume()
            update_coins_price()
            coins_count = len(_COINS_CACHE.get_data())
            logger.info(f"✅ Hệ thống đã khởi tạo cache {coins_count} coin")
        else:
            logger.error("❌ Hệ thống không thể khởi tạo cache")

    def _cache_updater(self):
        while self.running:
            try:
                time.sleep(300)
                logger.info("🔄 Tự động làm mới cache...")
                refresh_coins_cache()
                update_coins_volume()
                update_coins_price()
                active = []
                try:
                    for b in self.bots.values():
                        active.extend(getattr(b, 'active_symbols', []) or [])
                except Exception:
                    active = []
                cleanup_runtime_caches(active, aggressive=True)
            except Exception as e:
                logger.error(f"❌ Lỗi làm mới cache tự động: {str(e)}")

    def _verify_api_connection(self):
        try:
            balance = get_balance(self.api_key, self.api_secret)
            if balance is None:
                self.log("❌ LỖI: Không thể kết nối đến API Binance. Kiểm tra API Key/Secret, VPN, internet.")
                return False
            else:
                self.log(f"✅ Kết nối Binance thành công! Số dư: {balance:.2f} USDT/USDC")
                return True
        except Exception as e:
            self.log(f"❌ Lỗi kiểm tra kết nối: {str(e)}")
            return False

    def get_position_summary(self):
        try:
            positions = get_positions(api_key=self.api_key, api_secret=self.api_secret)
            long_count = sum(1 for p in positions if float(p.get('positionAmt', 0)) > 0)
            short_count = sum(1 for p in positions if float(p.get('positionAmt', 0)) < 0)
            long_pnl = sum(float(p.get('unRealizedProfit', 0)) for p in positions if float(p.get('positionAmt', 0)) > 0)
            short_pnl = sum(float(p.get('unRealizedProfit', 0)) for p in positions if float(p.get('positionAmt', 0)) < 0)
            total_unrealized_pnl = long_pnl + short_pnl

            bot_details = []
            total_bots_with_coins, trading_bots = 0, 0

            sorted_bots = sorted(self.bots.items(), key=lambda item: item[1].bot_creation_time)
            for idx, (bot_id, bot) in enumerate(sorted_bots, start=1):
                has_coin = len(bot.active_symbols) > 0 if hasattr(bot, 'active_symbols') else False
                is_trading = False
                if has_coin and hasattr(bot, 'symbol_data'):
                    for symbol, data in bot.symbol_data.items():
                        if data.get('position_open', False):
                            is_trading = True
                            break
                if has_coin:
                    total_bots_with_coins += 1
                if is_trading:
                    trading_bots += 1
                bot_details.append({
                    'index': idx,
                    'bot_id': bot_id,
                    'has_coin': has_coin,
                    'is_trading': is_trading,
                    'symbols': bot.active_symbols if hasattr(bot, 'active_symbols') else [],
                    'symbol_data': bot.symbol_data if hasattr(bot, 'symbol_data') else {},
                    'status': bot.status,
                    'leverage': bot.lev,
                    'percent': bot.percent,
                    'tp': bot.tp,
                    'sl': bot.sl,
                })

            summary = "📊 **THỐNG KÊ CHI TIẾT - BOT RANDOM SIGNAL**\n\n"

            cache_stats = _COINS_CACHE.get_stats()
            coins_in_cache = cache_stats['count']
            last_price_update = cache_stats['last_price_update']
            update_time = time.ctime(last_price_update) if last_price_update > 0 else "Chưa cập nhật"

            summary += f"🗂️ **CACHE HỆ THỐNG**: {coins_in_cache} coin | Cập nhật: {update_time}\n"
            summary += get_strategy_config_text().replace("<b>", "**").replace("</b>", "**") + "\n\n"

            total_balance, available_balance = get_total_and_available_balance(self.api_key, self.api_secret)
            margin_balance = get_margin_balance(self.api_key, self.api_secret)
            if total_balance is not None:
                summary += f"💰 **TỔNG SỐ DƯ**: {total_balance:.2f} USDT/USDC\n"
                summary += f"💰 **SỐ DƯ KHẢ DỤNG**: {available_balance:.2f} USDT/USDC\n"
                summary += f"💰 **SỐ DƯ KÝ QUỸ**: {margin_balance:.2f} USDT/USDC\n"
                summary += f"📈 **Tổng PnL**: {total_unrealized_pnl:.2f} USDT/USDC\n\n"
            else:
                summary += f"💰 **SỐ DƯ**: ❌ Lỗi kết nối\n\n"

            closed_win_total = sum(float(getattr(b, 'closed_win_usd', 0.0) or 0.0) for b in self.bots.values())
            closed_loss_total = sum(float(getattr(b, 'closed_loss_usd', 0.0) or 0.0) for b in self.bots.values())
            closed_trade_total = sum(int(getattr(b, 'closed_trade_count', 0) or 0) for b in self.bots.values())
            win_trade_total = sum(int(getattr(b, 'win_trade_count', 0) or 0) for b in self.bots.values())
            loss_trade_total = sum(int(getattr(b, 'loss_trade_count', 0) or 0) for b in self.bots.values())
            net_closed_total = closed_win_total - closed_loss_total

            summary += f"🤖 **SỐ BOT HỆ THỐNG**: {len(self.bots)} bot | {total_bots_with_coins} bot có coin | {trading_bots} bot đang giao dịch\n\n"
            summary += f"🏁 **THỐNG KÊ LỆNH ĐÃ ĐÓNG TRONG PHIÊN BOT**:\n"
            summary += f"   ✅ Lệnh thắng: {win_trade_total} | Tiền thắng: +{closed_win_total:.4f} USDT/USDC\n"
            summary += f"   ❌ Lệnh thua: {loss_trade_total} | Tiền thua: -{closed_loss_total:.4f} USDT/USDC\n"
            summary += f"   📌 Tổng lệnh đã đóng: {closed_trade_total} | Lãi/lỗ đã chốt: {net_closed_total:.4f} USDT/USDC\n\n"
            summary += f"📈 **PHÂN TÍCH PnL VÀ KHỐI LƯỢNG**:\n"
            summary += f"   📊 Số lượng: LONG={long_count} | SHORT={short_count}\n"
            summary += f"   💰 PnL: LONG={long_pnl:.2f} | SHORT={short_pnl:.2f}\n"
            summary += f"   ⚖️ Chênh lệch: {abs(long_pnl - short_pnl):.2f}\n\n"

            queue_info = self.bot_coordinator.get_queue_info()
            summary += f"🎪 **THÔNG TIN HÀNG ĐỢI (FIFO)**\n"
            summary += f"• Bot đang tìm coin: {queue_info['current_finding'] or 'Không có'}\n"
            summary += f"• Bot trong hàng đợi: {queue_info['queue_size']}\n"
            summary += f"• Bot có coin: {len(queue_info['bots_with_coins'])}\n"
            summary += f"• Coin đã phân phối: {queue_info['found_coins_count']}\n\n"

            if bot_details:
                summary += "📋 **CHI TIẾT BOT**:\n"
                for bot in bot_details:
                    status_emoji = "🟢" if bot['is_trading'] else "🟡" if bot['has_coin'] else "🔴"
                    stp = float(_STRATEGY_CONFIG.get('strategy_tp_roi', 0.0) or 0.0)
                    sslv = float(_STRATEGY_CONFIG.get('strategy_sl_roi', 0.0) or 0.0)
                    tp_sl_str = f"TP chiến lược:{stp}%" if stp > 0 else (f"TP bot:{bot['tp']}%" if bot['tp'] else "TP:Tắt")
                    tp_sl_str += f" SL chiến lược:{sslv}%" if sslv > 0 else (f" SL bot:{bot['sl']}%" if bot['sl'] else " SL:Tắt")
                    summary += f"{status_emoji} **bot_{bot['index']}** {tp_sl_str}\n"
                    summary += f"   💰 Đòn bẩy: {bot['leverage']}x | Vốn: {bot['percent']}%\n"
                    try:
                        bot_obj = self.bots.get(bot['bot_id'])
                        if bot_obj:
                            bw = float(getattr(bot_obj, 'closed_win_usd', 0.0) or 0.0)
                            bl = float(getattr(bot_obj, 'closed_loss_usd', 0.0) or 0.0)
                            bt = int(getattr(bot_obj, 'closed_trade_count', 0) or 0)
                            lr = getattr(bot_obj, 'last_closed_roi', None)
                            lp = getattr(bot_obj, 'last_closed_pnl', None)
                            extra = ""
                            if lr is not None and lp is not None:
                                extra = f" | Lệnh cuối ROI {float(lr):.2f}% / PnL {float(lp):.4f}"
                            summary += f"   🏁 Đã đóng: {bt} lệnh | Thắng +{bw:.4f} | Thua -{bl:.4f}{extra}\n"
                    except Exception:
                        pass
                    if bot['symbols']:
                        for symbol in bot['symbols']:
                            symbol_info = bot['symbol_data'].get(symbol, {})
                            status = "🟢 Đang giao dịch" if symbol_info.get('position_open') else "🟡 Chờ tín hiệu"
                            side = symbol_info.get('side', '')
                            qty = symbol_info.get('qty', 0)
                            summary += f"   🔗 {symbol} | {status}"
                            if side:
                                summary += f" | {side} {abs(qty):.4f}"
                                try:
                                    entry = float(symbol_info.get('entry', 0) or 0)
                                    price = get_current_price(symbol)
                                    if entry > 0 and price > 0:
                                        if side == 'BUY':
                                            roi_now = (price - entry) / entry * 100 * float(bot['leverage'])
                                            pnl_now = (price - entry) * abs(float(qty))
                                        else:
                                            roi_now = (entry - price) / entry * 100 * float(bot['leverage'])
                                            pnl_now = (entry - price) * abs(float(qty))
                                        summary += f" | ROI {roi_now:.2f}% | PnL {pnl_now:.4f}"
                                except Exception:
                                    pass
                            summary += "\n"
                    else:
                        summary += f"   🔍 Đang tìm coin...\n"
                    summary += "\n"

            return summary
        except Exception as e:
            return f"❌ Lỗi thống kê: {str(e)}"

    def log(self, message):
        important_keywords = ['❌', '✅', '⛔', '💰', '📈', '📊', '🎯', '🛡️', '🔴', '🟢', '⚠️', '🚫', '🔄']
        if any(keyword in message for keyword in important_keywords):
            logger.warning(f"[HỆ THỐNG] {message}")
            if self.telegram_bot_token and self.telegram_chat_id:
                send_telegram(f"<b>HỆ THỐNG</b>: {message}",
                             chat_id=self.telegram_chat_id,
                             bot_token=self.telegram_bot_token,
                             default_chat_id=self.telegram_chat_id)

    def send_main_menu(self, chat_id):
        welcome = (
            "🤖 <b>BOT GIAO DỊCH FUTURES - RANDOM SIGNAL</b>\n\n"
            "🎯 <b>CƠ CHẾ HOẠT ĐỘNG:</b>\n"
            "• Tín hiệu vào lệnh là random BUY/SELL.\n"
            "• Không dùng volume, biên độ nến, nến bẹt, doji, EMA/RSI, trend, taker hay chấm điểm.\n"
            "• Bot động chọn một coin hợp lệ rồi mở vị thế random.\n"
            "• Khi đang có vị thế, bot KHÔNG đảo chiều theo tín hiệu.\n"
            "• Lệnh chỉ thoát bằng TP/SL hoặc bảo vệ lợi nhuận tụt từ đỉnh.\n"
            "• TP/SL trong mục Chiến lược có thể chỉnh sau khi bot đã vào lệnh.\n\n"
            "📌 <b>LƯU Ý:</b> Random rất rủi ro; hãy chạy vốn nhỏ để test trước."
        )
        send_telegram(welcome, chat_id=chat_id, reply_markup=create_main_menu(),
                     bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

    def add_bot(self, symbol, lev, percent, tp, sl, strategy_type, bot_count=1, **kwargs):
        if sl == 0: sl = None
        if tp == 0: tp = None

        if not self.api_key or not self.api_secret:
            self.log("❌ API Key chưa được cài đặt trong BotManager")
            return False

        if not self._verify_api_connection():
            self.log("❌ KHÔNG THỂ KẾT NỐI VỚI BINANCE - KHÔNG THỂ TẠO BOT")
            return False

        bot_mode = kwargs.get('bot_mode', 'static')

        created_count = 0
        for i in range(bot_count):
            if bot_mode == 'static' and symbol:
                bot_id = f"STATIC_{strategy_type}_{int(time.time())}_{i}"
            else:
                bot_id = f"DYNAMIC_{strategy_type}_{int(time.time())}_{i}"
            if bot_id in self.bots:
                continue

            bot = BaseBot(
                symbol, lev, percent, tp, sl, self.ws_manager,
                self.api_key, self.api_secret, self.telegram_bot_token, self.telegram_chat_id,
                coin_manager=self.coin_manager, symbol_locks=self.symbol_locks,
                bot_coordinator=self.bot_coordinator, bot_id=bot_id, max_coins=1,
                strategy_name=strategy_type,
                kline_manager=self.kline_manager   # Truyền kline manager
            )
            bot._bot_manager = self
            bot.coin_finder.set_bot_manager(self)
            self.bots[bot_id] = bot
            created_count += 1

        if created_count > 0:
            tp_info = f"🎯 TP: {tp}%" if tp else "🎯 TP: Tắt"
            sl_info = f"🛡️ SL: {sl}%" if sl else "🛡️ SL: Tắt"
            success_msg = (f"✅ <b>ĐÃ TẠO {created_count} BOT RANDOM</b>\n\n"
                           f"🎯 Chiến lược: {strategy_type}\n💰 Đòn bẩy: {lev}x\n"
                           f"📈 % Số dư: {percent}%\n{tp_info}\n{sl_info}\n"
                           f"🔧 Chế độ: {bot_mode}\n🔢 Số bot: {created_count}\n")
            if bot_mode == 'static' and symbol:
                success_msg += f"🔗 Coin ban đầu: {symbol}\n"
            else:
                success_msg += f"🔗 Coin: Tự động chọn random một coin hợp lệ (USDT/USDC)\n"
            success_msg += "🎯 Tín hiệu random; chỉ dùng cấu hình TP/SL và bảo vệ lợi nhuận.\n"
            self.log(success_msg)
            return True
        else:
            self.log("❌ Không thể tạo bot")
            return False

    def stop_coin(self, symbol):
        stopped_count = 0
        symbol = symbol.upper()
        for bot_id, bot in self.bots.items():
            if hasattr(bot, 'stop_symbol') and symbol in bot.active_symbols:
                if bot.stop_symbol(symbol): stopped_count += 1
        if stopped_count > 0:
            self.log(f"✅ Đã dừng coin {symbol} trong {stopped_count} bot")
            return True
        else:
            self.log(f"❌ Không tìm thấy coin {symbol} trong bot nào")
            return False

    def get_coin_management_keyboard(self):
        all_coins = set()
        for bot in self.bots.values():
            if hasattr(bot, 'active_symbols'):
                all_coins.update(bot.active_symbols)
        if not all_coins: return None
        keyboard = []
        row = []
        for coin in sorted(list(all_coins))[:12]:
            row.append({"text": f"⛔ Coin: {coin}"})
            if len(row) == 2:
                keyboard.append(row)
                row = []
        if row: keyboard.append(row)
        keyboard.append([{"text": "⛔ DỪNG TẤT CẢ COIN"}])
        keyboard.append([{"text": "❌ Hủy bỏ"}])
        return {"keyboard": keyboard, "resize_keyboard": True, "one_time_keyboard": True}

    def stop_bot_symbol(self, bot_id, symbol):
        bot = self.bots.get(bot_id)
        if bot and hasattr(bot, 'stop_symbol'):
            success = bot.stop_symbol(symbol)
            if success: self.log(f"⛔ Đã dừng coin {symbol} trong bot {bot_id}")
            return success
        return False

    def stop_all_bot_symbols(self, bot_id):
        bot = self.bots.get(bot_id)
        if bot and hasattr(bot, 'stop_all_symbols'):
            stopped_count = bot.stop_all_symbols()
            self.log(f"⛔ Đã dừng {stopped_count} coin trong bot {bot_id}")
            return stopped_count
        return 0

    def stop_all_coins(self):
        self.log("⛔ Đang dừng tất cả coin trong tất cả bot...")
        total_stopped = 0
        for bot_id, bot in self.bots.items():
            if hasattr(bot, 'stop_all_symbols'):
                stopped_count = bot.stop_all_symbols()
                total_stopped += stopped_count
                self.log(f"⛔ Đã dừng {stopped_count} coin trong bot {bot_id}")
        self.log(f"✅ Đã dừng tổng cộng {total_stopped} coin, hệ thống vẫn chạy")
        return total_stopped

    def stop_bot(self, bot_id):
        bot = self.bots.get(bot_id)
        if bot:
            bot.stop()
            self.bot_coordinator.remove_bot(bot_id)
            del self.bots[bot_id]
            self.log(f"🔴 Đã dừng bot {bot_id}")
            return True
        return False

    def stop_all(self):
        self.log("🔴 Đang dừng tất cả bot...")
        for bot_id in list(self.bots.keys()):
            self.stop_bot(bot_id)
        self.log("🔴 Đã dừng tất cả bot, hệ thống vẫn chạy")

    def _telegram_listener(self):
        last_update_id = 0
        executor = ThreadPoolExecutor(max_workers=4, thread_name_prefix='tg_handler')
        while self.running and self.telegram_bot_token:
            try:
                url = f"https://api.telegram.org/bot{self.telegram_bot_token}/getUpdates?offset={last_update_id+1}&timeout=30"
                response = requests.get(url, timeout=35)
                if response.status_code == 200:
                    data = response.json()
                    if data.get('ok'):
                        for update in data['result']:
                            update_id = update['update_id']
                            if update_id > last_update_id:
                                last_update_id = update_id
                                executor.submit(self._handle_telegram_message, update)
                time.sleep(0.1)
            except Exception as e:
                logger.error(f"Lỗi nghe Telegram: {str(e)}")
                time.sleep(1)
        executor.shutdown(wait=False)

    def _handle_telegram_message(self, update):
        try:
            message = update.get('message', {})
            chat_id = str(message.get('chat', {}).get('id'))
            text = message.get('text', '').strip()
            if chat_id != self.telegram_chat_id:
                return
            self._process_telegram_command(chat_id, text)
        except Exception as e:
            logger.error(f"Lỗi xử lý tin nhắn Telegram: {str(e)}")

    def _process_telegram_command(self, chat_id, text):
        user_state = self.user_states.get(chat_id, {})
        current_step = user_state.get('step')

        strategy_key_map = {
            '✏️ TP chiến lược': ('strategy_tp_roi', 'TP ROI dùng realtime, có thể chỉnh sau khi đã vào lệnh. 0 = tắt.'),
            '✏️ SL chiến lược': ('strategy_sl_roi', 'SL ROI dùng realtime, có thể chỉnh sau khi đã vào lệnh. 0 = tắt.'),
            '✏️ Bảo vệ lợi nhuận': ('profit_protect_enabled', '1 = bật bảo vệ lợi nhuận tụt từ đỉnh, 0 = tắt.'),
            '✏️ ROI bắt đầu bảo vệ': ('profit_protect_start_roi', 'ROI từng đạt từ mức này trở lên thì bắt đầu bảo vệ lợi nhuận.'),
            '✏️ ROI tụt từ đỉnh để đóng': ('profit_protect_pullback_roi', 'Khi ROI tụt từ đỉnh xuống mức này thì đóng.'),
        }

        if text == "📊 Danh sách Bot":
            if not self.bots:
                send_telegram("🤖 Hiện không có bot nào đang chạy.", chat_id=chat_id,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                sorted_bots = sorted(self.bots.items(), key=lambda item: item[1].bot_creation_time)
                bot_list = "\n".join([f"• bot_{idx} - {'🟢' if b.status != 'searching' else '🔴'}" for idx, (_, b) in enumerate(sorted_bots, start=1)])
                send_telegram(f"📋 Danh sách Bot:\n{bot_list}", chat_id=chat_id,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "📊 Thống kê":
            send_telegram(self.get_position_summary(), chat_id=chat_id,
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "➕ Thêm Bot":
            self.user_states[chat_id] = {'step': 'waiting_bot_mode'}
            send_telegram("🤖 Chọn chế độ bot:", chat_id=chat_id, reply_markup=create_bot_mode_keyboard(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "⛔ Dừng Bot":
            if not self.bots:
                send_telegram("🤖 Không có bot nào để dừng.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                sorted_bots = sorted(self.bots.items(), key=lambda item: item[1].bot_creation_time)
                keyboard = [[{"text": f"bot_{idx}"}] for idx, _ in enumerate(sorted_bots, start=1)]
                keyboard.append([{"text": "❌ Hủy bỏ"}])
                self.user_states[chat_id] = {'step': 'waiting_stop_bot'}
                send_telegram("⛔ Chọn bot muốn dừng:", chat_id=chat_id,
                             reply_markup={"keyboard": keyboard, "resize_keyboard": True, "one_time_keyboard": True},
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "⛔ Quản lý Coin":
            kb = self.get_coin_management_keyboard()
            if not kb:
                send_telegram("📭 Chưa có coin nào đang được bot theo dõi.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                self.user_states[chat_id] = {'step': 'waiting_stop_coin'}
                send_telegram("⛔ Chọn coin muốn dừng:", chat_id=chat_id, reply_markup=kb,
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "📈 Vị thế":
            positions = get_positions(api_key=self.api_key, api_secret=self.api_secret)
            open_positions = [p for p in positions if abs(float(p.get('positionAmt', 0))) > 0]
            if not open_positions:
                msg = "📭 Không có vị thế đang mở."
            else:
                msg = "📈 <b>VỊ THẾ ĐANG MỞ</b>\n\n"
                for p0 in open_positions[:20]:
                    qty = float(p0.get('positionAmt', 0))
                    side = "BUY" if qty > 0 else "SELL"
                    msg += f"• {p0.get('symbol')} | {side} | qty={abs(qty)} | PnL={float(p0.get('unRealizedProfit', 0)):.3f}\n"
            send_telegram(msg, chat_id=chat_id,
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "💰 Số dư":
            total, available = get_total_and_available_balance(self.api_key, self.api_secret)
            margin = get_margin_balance(self.api_key, self.api_secret)
            if total is not None:
                msg = (f"💰 <b>SỐ DƯ</b>\n\n"
                       f"• Tổng số dư: {total:.2f}\n"
                       f"• Khả dụng: {available:.2f}\n"
                       f"• Ký quỹ: {margin:.2f}")
            else:
                msg = "❌ Không thể lấy số dư"
            send_telegram(msg, chat_id=chat_id,
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "⚙️ Cấu hình":
            send_telegram("⚙️ Cấu hình chính hiện nằm trong mục 🎯 Chiến lược.", chat_id=chat_id,
                         reply_markup=create_main_menu(), bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "🎯 Chiến lược":
            self.user_states[chat_id] = {'step': 'waiting_strategy_config'}
            send_telegram(get_strategy_config_text(), chat_id=chat_id, reply_markup=create_strategy_config_keyboard(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif text == "❌ Hủy bỏ":
            self.user_states[chat_id] = {}
            send_telegram("❌ Đã hủy thao tác.", chat_id=chat_id, reply_markup=create_main_menu(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_strategy_config':
            if text in ('📊 Xem tham số chiến lược', '📊 Xem cấu hình chiến lược'):
                send_telegram(get_strategy_config_text(), chat_id=chat_id, reply_markup=create_strategy_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text in ('🔄 Reset chiến lược', '♻️ Reset tham số chiến lược', '🔄 Reset chiến lược mặc định'):
                _STRATEGY_CONFIG.reset()
                send_telegram("✅ Đã reset tham số chiến lược về mặc định.\n\n" + get_strategy_config_text(),
                             chat_id=chat_id, reply_markup=create_strategy_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text in strategy_key_map:
                key, help_text = strategy_key_map[text]
                self.user_states[chat_id] = {'step': 'waiting_strategy_value', 'strategy_key': key}
                send_telegram(f"✏️ Nhập giá trị mới cho <b>{key}</b>\n{help_text}", chat_id=chat_id,
                             reply_markup=create_strategy_value_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("⚠️ Chọn tham số cần chỉnh.", chat_id=chat_id, reply_markup=create_strategy_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_strategy_value':
            if text == "❌ Hủy bỏ":
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return
            try:
                key = user_state.get('strategy_key')
                if key in ('signal_interval', 'current_interval', 'compare_interval', 'market_interval', 'extreme_interval'):
                    val = _normalize_interval(text)
                    if val != text.strip().lower():
                        raise ValueError
                    _STRATEGY_CONFIG.update(**{key: val})
                else:
                    val = float(text)
                    int_keys = {'max_reverse_count', 'entry_min_trades', 'exit_min_trades', 'scan_top_coin_limit', 'confirm_min_trades', 'max_signal_eval_coins', 'min_24h_trade_count', 'target_leverage', 'min_allowed_leverage', 'max_consecutive_losses_before_pause', 'max_hold_seconds', 'coin_cooldown_after_loss_sec'}
                    if key in int_keys:
                        val = int(val)
                        if val < 0 or val > 10000:
                            raise ValueError
                    else:
                        if val < 0:
                            raise ValueError
                        if key in ('buy_taker_ratio_min', 'sell_taker_ratio_min', 'exit_taker_ratio_min', 'absorption_taker_ratio') and val > 1:
                            raise ValueError
                        if key in ('max_buy_close_position', 'min_sell_close_position') and val > 1:
                            raise ValueError
                    _STRATEGY_CONFIG.update(**{key: val})
                self.user_states[chat_id] = {'step': 'waiting_strategy_config'}
                send_telegram("✅ Đã cập nhật.\n\n" + get_strategy_config_text(), chat_id=chat_id,
                             reply_markup=create_strategy_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            except Exception:
                send_telegram("⚠️ Giá trị không hợp lệ. Hãy nhập số phù hợp.", chat_id=chat_id,
                             reply_markup=create_strategy_value_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_bot_mode':
            if text == "🤖 Bot Tĩnh - Coin cụ thể":
                user_state['bot_mode'] = 'static'
                user_state['step'] = 'waiting_symbol'
                send_telegram("🔗 Nhập tên coin, ví dụ SOLUSDT:", chat_id=chat_id, reply_markup=create_symbols_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text == "🔄 Bot Động - Tự tìm coin":
                user_state['bot_mode'] = 'dynamic'
                user_state['step'] = 'waiting_leverage'
                send_telegram("⚙️ Chọn đòn bẩy:", chat_id=chat_id, reply_markup=create_leverage_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("⚠️ Vui lòng chọn chế độ bot hợp lệ.", chat_id=chat_id, reply_markup=create_bot_mode_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_symbol':
            if text != "❌ Hủy bỏ":
                user_state['symbol'] = text.upper()
                user_state['step'] = 'waiting_leverage'
                send_telegram("⚙️ Chọn đòn bẩy:", chat_id=chat_id, reply_markup=create_leverage_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_leverage':
            try:
                lev = int(text.replace('x', ''))
                if lev <= 0:
                    raise ValueError
                user_state['leverage'] = lev
                user_state['step'] = 'waiting_percent'
                send_telegram("📊 Chọn % số dư cho mỗi lệnh:", chat_id=chat_id, reply_markup=create_percent_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            except Exception:
                send_telegram("⚠️ Vui lòng nhập/chọn đòn bẩy hợp lệ.", chat_id=chat_id, reply_markup=create_leverage_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_percent':
            try:
                percent = float(text)
                if percent <= 0 or percent > 100:
                    raise ValueError
                user_state['percent'] = percent
                user_state['step'] = 'waiting_tp'
                send_telegram("🎯 Nhập TP % ROI sau đòn bẩy, hoặc bỏ qua:", chat_id=chat_id, reply_markup=create_tp_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            except Exception:
                send_telegram("⚠️ Vui lòng nhập % hợp lệ.", chat_id=chat_id, reply_markup=create_percent_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_tp':
            if text == "❌ Bỏ qua (không TP)":
                user_state['tp'] = None
            elif text != "❌ Hủy bỏ":
                try:
                    tp = float(text)
                    if tp < 0:
                        raise ValueError
                    user_state['tp'] = tp if tp > 0 else None
                except Exception:
                    send_telegram("⚠️ Vui lòng nhập TP >= 0.", chat_id=chat_id, reply_markup=create_tp_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                    return
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return
            user_state['step'] = 'waiting_sl'
            send_telegram("🛡️ Nhập SL % ROI sau đòn bẩy, hoặc bỏ qua:", chat_id=chat_id, reply_markup=create_sl_keyboard(),
                         bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_sl':
            if text == "❌ Bỏ qua (không SL)":
                user_state['sl'] = None
            elif text != "❌ Hủy bỏ":
                try:
                    sl = float(text)
                    if sl < 0:
                        raise ValueError
                    user_state['sl'] = sl if sl > 0 else None
                except Exception:
                    send_telegram("⚠️ Vui lòng nhập SL >= 0.", chat_id=chat_id, reply_markup=create_sl_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                    return
            else:
                self.user_states[chat_id] = {}
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return

            if user_state.get('bot_mode') == 'static':
                self._finish_bot_creation(chat_id, user_state)
            else:
                user_state['step'] = 'waiting_bot_count'
                send_telegram("🔢 Nhập số bot muốn tạo:", chat_id=chat_id, reply_markup=create_bot_count_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_bot_count':
            try:
                bot_count = int(text)
                if bot_count <= 0:
                    raise ValueError
                user_state['bot_count'] = bot_count
                self._finish_bot_creation(chat_id, user_state)
            except Exception:
                send_telegram("⚠️ Vui lòng nhập số nguyên > 0.", chat_id=chat_id, reply_markup=create_bot_count_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_stop_bot':
            if text.startswith("bot_"):
                try:
                    idx = int(text.split("_")[1])
                    sorted_bots = sorted(self.bots.items(), key=lambda item: item[1].bot_creation_time)
                    bot_id = sorted_bots[idx-1][0]
                    self.stop_bot(bot_id)
                    send_telegram(f"✅ Đã dừng {text}", chat_id=chat_id, reply_markup=create_main_menu(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                except Exception:
                    send_telegram("❌ Bot không tồn tại.", chat_id=chat_id, reply_markup=create_main_menu(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            self.user_states[chat_id] = {}

        elif current_step == 'waiting_stop_coin':
            if text.startswith("⛔ Coin: "):
                coin = text.replace("⛔ Coin: ", "")
                self.stop_coin(coin)
                send_telegram(f"✅ Đã dừng coin {coin}", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text == "⛔ DỪNG TẤT CẢ COIN":
                self.stop_all_coins()
                send_telegram("✅ Đã dừng tất cả coin", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("❌ Đã hủy.", chat_id=chat_id, reply_markup=create_main_menu(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            self.user_states[chat_id] = {}

        else:
            self.send_main_menu(chat_id)

    def _finish_bot_creation(self, chat_id, user_state):
        try:
            bot_mode = user_state.get('bot_mode', 'static')
            leverage = user_state.get('leverage')
            percent = user_state.get('percent')
            tp = user_state.get('tp')
            sl = user_state.get('sl')
            symbol = user_state.get('symbol')
            bot_count = user_state.get('bot_count', 1)

            success = self.add_bot(
                symbol=symbol, lev=leverage, percent=percent, tp=tp, sl=sl,
                strategy_type="SpeedPatternStrategy",
                bot_mode=bot_mode, bot_count=bot_count
            )

            if success:
                success_msg = (
                    f"✅ <b>ĐÃ TẠO BOT RANDOM THÀNH CÔNG</b>\n\n"
                    f"🤖 Chiến lược: random BUY/SELL, không dùng điều kiện tín hiệu\n"
                    f"🔧 Chế độ: {bot_mode}\n"
                    f"🔢 Số bot: {bot_count}\n"
                    f"💰 Đòn bẩy: {leverage}x\n"
                    f"📊 % Số dư: {percent}%\n"
                    f"🎯 TP: {tp if tp else 'Tắt'}\n"
                    f"🛡️ SL: {sl if sl else 'Tắt'}\n"
                    f"🔄 Thoát: chỉ TP/SL hoặc bảo vệ lợi nhuận tụt từ đỉnh\n"
                    f"⚖️ Điều kiện tín hiệu: Đã bỏ hết\n\n"
                    f"{get_strategy_config_text()}"
                )
                if bot_mode == 'static' and symbol:
                    success_msg += f"\n🔗 Coin: {symbol}"
                send_telegram(success_msg, chat_id=chat_id, reply_markup=create_main_menu(),
                            bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("❌ Lỗi tạo bot. Vui lòng thử lại.",
                            chat_id=chat_id, reply_markup=create_main_menu(),
                            bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

            self.user_states[chat_id] = {}
        except Exception as e:
            send_telegram(f"❌ Lỗi tạo bot: {str(e)}", chat_id=chat_id, reply_markup=create_main_menu(),
                        bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            self.user_states[chat_id] = {}

ssl._create_default_https_context = ssl._create_unverified_context
