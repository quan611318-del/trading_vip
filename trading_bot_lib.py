#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
LIVE MERGED VERSION
- Giữ nguyên live trading Binance Futures và giao diện Telegram của file gốc.
- Port cấu hình/tín hiệu/risk/DCA/reverse/side-balance từ bản EMA-volume PostgreSQL.
- Tín hiệu chính chỉ dùng nến đã đóng.
- Lệnh đóng dùng reduceOnly để giảm nguy cơ vô tình đảo vị thế.

CẢNH BÁO: File này CÓ THỂ ĐẶT LỆNH THẬT khi được cấp API key có quyền Futures.
"""
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

_ACCOUNT_RISK_LOCK = threading.RLock()
_LAST_ENTRY_CANDLE = {}
_BINANCE_TIME_OFFSET_MS = 0


def sync_binance_time():
    global _BINANCE_TIME_OFFSET_MS
    try:
        data = binance_api_request('https://fapi.binance.com/fapi/v1/time')
        server_time = int((data or {}).get('serverTime', 0) or 0)
        if server_time > 0:
            _BINANCE_TIME_OFFSET_MS = server_time - int(time.time() * 1000)
            return True
    except Exception as exc:
        logger.warning(f"Không đồng bộ được Binance time: {exc}")
    return False


def _signed_timestamp():
    return int(time.time() * 1000) + int(_BINANCE_TIME_OFFSET_MS)


def _signed_request_json(path, method, params, api_key, api_secret):
    try:
        _wait_for_rate_limit()
        payload = dict(params or {})
        payload.setdefault('timestamp', _signed_timestamp())
        payload.setdefault('recvWindow', 10000)
        query = urllib.parse.urlencode(payload)
        signature = sign(query, api_secret)
        url = f"https://fapi.binance.com{path}?{query}&signature={signature}"
        response = requests.request(method.upper(), url, headers={'X-MBX-APIKEY': api_key}, timeout=15)
        try:
            data = response.json()
        except Exception:
            data = {'raw': response.text}
        return 200 <= response.status_code < 300, data
    except Exception as exc:
        return False, {'msg': str(exc)}


def ensure_one_way_mode_live(api_key, api_secret):
    ok, data = _signed_request_json('/fapi/v1/positionSide/dual', 'GET', {}, api_key, api_secret)
    if not ok:
        return False, data
    raw_dual = data.get('dualSidePosition') if isinstance(data, dict) else False
    dual = str(raw_dual).strip().lower() == 'true' if isinstance(raw_dual, str) else bool(raw_dual)
    if not dual:
        return True, 'already one-way'
    ok, data = _signed_request_json(
        '/fapi/v1/positionSide/dual', 'POST', {'dualSidePosition': 'false'}, api_key, api_secret
    )
    return ok, data


def set_margin_type_live(symbol, margin_type, api_key, api_secret):
    ok, data = _signed_request_json(
        '/fapi/v1/marginType', 'POST',
        {'symbol': symbol.upper(), 'marginType': str(margin_type).upper()}, api_key, api_secret
    )
    # Binance code -4046 means the requested margin type is already set.
    if not ok and isinstance(data, dict) and int(data.get('code', 0) or 0) == -4046:
        return True
    return ok


def get_positions_strict_all(api_key, api_secret):
    try:
        params = {'timestamp': _signed_timestamp(), 'recvWindow': 10000}
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v2/positionRisk?{query}&signature={sig}"
        data = binance_api_request(url, headers={'X-MBX-APIKEY': api_key})
        if data is None or not isinstance(data, list):
            return False, []
        return True, data
    except Exception as exc:
        logger.error(f"Lỗi lấy toàn bộ positionRisk: {exc}")
        return False, []


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

# --- Cập nhật bàn phím chiến lược với nút bộ lọc ---
def create_strategy_config_keyboard():
    """Bàn phím chiến lược: quản lý lệnh, tín hiệu BUY/SELL và bộ lọc coin."""
    return {
        "keyboard": [
            [{"text": "📊 Xem tham số chiến lược"}],
            [{"text": "📡 Cấu hình tín hiệu BUY/SELL"}],
            [{"text": "✏️ TP chiến lược"}, {"text": "✏️ SL chiến lược"}],
            [{"text": "✏️ Bảo vệ lợi nhuận"}, {"text": "✏️ ROI bắt đầu bảo vệ"}],
            [{"text": "✏️ ROI tụt từ đỉnh để đóng"}],
            [{"text": "⚙️ Bộ lọc coin (khối lượng, giá,...)"}],
            [{"text": "🔄 Reset chiến lược mặc định"}],
            [{"text": "🔙 Quay lại menu chính"}],
        ],
        "resize_keyboard": True,
        "one_time_keyboard": False,
    }


def create_signal_config_keyboard():
    """Bàn phím chỉnh riêng độ khó tín hiệu BUY và SELL."""
    return {
        "keyboard": [
            [{"text": "✏️ Khung tín hiệu"}, {"text": "✏️ EMA nhanh"}, {"text": "✏️ EMA chậm"}],
            [{"text": "✏️ Số nến volume TB"}],
            [{"text": "✏️ Điểm BUY"}, {"text": "✏️ Điểm SELL"}],
            [{"text": "✏️ Volume BUY x"}, {"text": "✏️ Volume SELL x"}],
            [{"text": "✏️ Khoảng cách điểm BUY"}, {"text": "✏️ Khoảng cách điểm SELL"}],
            [{"text": "✏️ Vị trí close BUY"}, {"text": "✏️ Vị trí close SELL"}],
            [{"text": "✏️ EMA nghiêm BUY"}, {"text": "✏️ EMA nghiêm SELL"}],
            [{"text": "🔙 Quay lại cấu hình chiến lược"}],
        ],
        "resize_keyboard": True,
        "one_time_keyboard": False,
    }


def create_signal_value_keyboard():
    """Gợi ý giá trị thường dùng; người dùng vẫn có thể nhập số hoặc timeframe khác."""
    return {
        "keyboard": [
            [{"text": "1m"}, {"text": "3m"}, {"text": "5m"}, {"text": "15m"}],
            [{"text": "30m"}, {"text": "1h"}, {"text": "2h"}, {"text": "4h"}],
            [{"text": "0"}, {"text": "0.5"}, {"text": "0.8"}, {"text": "1"}],
            [{"text": "1.1"}, {"text": "1.2"}, {"text": "5"}, {"text": "7"}],
            [{"text": "9"}, {"text": "20"}, {"text": "21"}, {"text": "50"}],
            [{"text": "❌ Hủy bỏ"}],
        ],
        "resize_keyboard": True,
        "one_time_keyboard": True,
    }


def create_filter_keyboard():
    """Bàn phím cho các tham số bộ lọc coin."""
    return {
        "keyboard": [
            [{"text": "✏️ Min 24h Vol (USDT)"}, {"text": "✏️ Min Price"}],
            [{"text": "✏️ Max Price"}, {"text": "✏️ Min Trades"}],
            [{"text": "✏️ Min Abs Change %"}, {"text": "✏️ Max Abs Change %"}],
            [{"text": "🔙 Quay lại cấu hình chiến lược"}],
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
        ts = _signed_timestamp()
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
        ts = _signed_timestamp()
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
        ts = _signed_timestamp()
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
        ts = _signed_timestamp()
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
        ts = _signed_timestamp()
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

def place_order(symbol, side, qty, api_key, api_secret, reduce_only=False, client_order_id=None):
    """Đặt MARKET order thật. Lệnh đóng phải truyền reduce_only=True."""
    if not symbol or not api_key or not api_secret:
        return None
    try:
        params = {
            "symbol": symbol.upper(),
            "side": str(side).upper(),
            "type": "MARKET",
            "quantity": qty,
            "timestamp": _signed_timestamp(),
            "recvWindow": 10000,
        }
        if reduce_only:
            params["reduceOnly"] = "true"
        if client_order_id:
            params["newClientOrderId"] = str(client_order_id)[:36]
        query = urllib.parse.urlencode(params)
        sig = sign(query, api_secret)
        url = f"https://fapi.binance.com/fapi/v1/order?{query}&signature={sig}"
        headers = {'X-MBX-APIKEY': api_key}
        return binance_api_request(url, method='POST', headers=headers)
    except Exception as e:
        logger.error(f"Lỗi lệnh {symbol} {side}: {str(e)}")
        return None

def cancel_all_orders(symbol, api_key, api_secret):
    if not symbol: return False
    try:
        ts = _signed_timestamp()
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
    """Cấu hình LIVE EMA + volume, đồng bộ với bộ tham số của bản PostgreSQL.

    File vẫn đặt lệnh thật trên Binance Futures. Các key cũ được giữ để phần
    Telegram và state cũ không bị lỗi.
    """
    DEFAULTS = {
        'current_interval': '15m',
        'signal_interval': '15m',
        'timeframe_seconds': 900.0,
        'use_quote_volume': 1.0,

        # Tín hiệu chính: giống bản đầu tiên, chỉ dùng nến đã đóng.
        'ema_fast_period': 9,
        'ema_slow_period': 21,
        'signal_volume_lookback': 20,
        'buy_score_threshold': 7.0,
        'sell_score_threshold': 5.0,
        'buy_min_score_gap': 1.0,
        'sell_min_score_gap': 0.4,
        'buy_min_volume_ratio': 1.50,
        'sell_min_volume_ratio': 1.10,
        'buy_min_body_pct': 0.15,
        'sell_min_body_pct': 0.08,
        'buy_min_close_position': 0.65,
        'sell_max_close_position': 0.45,
        'max_signal_candle_range_pct': 5.0,
        'buy_taker_ratio_min': 0.55,
        'sell_taker_ratio_min': 0.55,
        'btc_context_enabled': 1.0,
        'btc_block_buy_drop_pct': 1.0,
        # Alias giao diện cũ; bộ điểm mới tự kiểm tra EMA theo hướng.
        'buy_require_ema_trend': 1.0,
        'sell_require_ema_trend': 0.0,

        # TP/SL riêng theo hướng (ROI margin sau đòn bẩy).
        'long_tp_roi_pct': 125.0,
        'long_sl_roi_pct': 50.0,
        'short_tp_roi_pct': 100.0,
        'short_sl_roi_pct': 50.0,
        'strategy_tp_roi': 0.0,
        'strategy_sl_roi': 0.0,
        'emergency_stop_roi': 0.0,

        # DCA LIVE.
        'enable_dca_long': 1.0,
        'enable_dca_short': 1.0,
        'dca_mode': 'loss',
        'dca_trigger_roi_pct': 25.0,
        'dca_multiplier': 1.10,
        'max_dca_steps': 3,
        'dca_min_seconds_between_adds': 20,

        # Bảo vệ lợi nhuận.
        'profit_protect_enabled': 1.0,
        'profit_protect_start_roi': 50.0,
        'profit_protect_pullback_roi': 30.0,

        # Reverse và thoát bằng tín hiệu ngược.
        'reverse_mode': 'confirmed',       # none | immediate | confirmed
        'reverse_min_score': 7.0,
        'max_reverse_count': 1,
        'enable_exit_on_opposite_signal': 0.0,
        'opposite_exit_min_score': 7.0,

        # Cân bằng LONG/SHORT trên toàn tài khoản.
        'enable_side_balance': 1.0,
        'side_balance_mode': 'override',   # filter | override
        'side_balance_threshold': 1.25,
        'balance_override_min_signal_score': 3.0,

        # Rủi ro tài khoản.
        'max_positions': 3,
        'max_total_margin_per_symbol_pct': 4.0,
        'max_total_notional_pct': 150.0,
        'max_daily_loss_pct': 0.0,
        'margin_type': 'ISOLATED',
        'ensure_one_way_mode': 1.0,
        'trading_enabled': 1.0,

        # Scanner giống bản đầu tiên.
        'quote_asset': 'USDT',
        'min_24h_volume': 10_000_000.0,
        'scan_top_coin_limit': 80,
        'max_signal_eval_coins': 40,
        'min_coin_price': 0.0,
        'max_coin_price': 0.0,
        'min_24h_trade_count': 0,
        'max_spread_pct': 0.25,
        'max_abs_24h_change_pct': 60.0,
        'min_abs_24h_change_pct': 0.0,
        'target_leverage': 50,
        'min_allowed_leverage': 1,

        # Cooldown/runtime.
        'cooldown_after_close_seconds': 60,
        'blacklist_after_tp_sl_seconds': 180,
        'coin_cooldown_after_loss_sec': 180,
        'max_hold_seconds': 0,
        'max_consecutive_losses_before_pause': 999,
        'pause_after_loss_streak_sec': 0,

        # Alias cũ để tương thích.
        'volume_factor': 1.10,
        'range_factor': 1.10,
        'min_prev_range_pct': 0.08,
        'block_same_candle_reverse': 1.0,
        'low_volume_filter_enabled': 0.0,
        'force_rest_signal_enabled': 0.0,
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
        'compare_interval': '15m',
        'market_interval': '15m',
        'extreme_interval': '15m',
        'min_elapsed_seconds': 0.0,
    }

    INT_KEYS = {
        'max_reverse_count', 'scan_top_coin_limit', 'max_signal_eval_coins',
        'min_24h_trade_count', 'target_leverage', 'min_allowed_leverage',
        'max_consecutive_losses_before_pause', 'max_hold_seconds',
        'coin_cooldown_after_loss_sec', 'ema_fast_period', 'ema_slow_period',
        'signal_volume_lookback', 'max_positions', 'max_dca_steps',
        'dca_min_seconds_between_adds', 'cooldown_after_close_seconds',
        'blacklist_after_tp_sl_seconds',
    }
    STRING_KEYS = {
        'current_interval', 'signal_interval', 'compare_interval', 'market_interval',
        'extreme_interval', 'dca_mode', 'reverse_mode', 'side_balance_mode',
        'margin_type', 'quote_asset',
    }

    def __init__(self):
        self._config = self.DEFAULTS.copy()
        self._lock = threading.RLock()

    def _sync_aliases_locked(self):
        interval = _normalize_interval(self._config.get('current_interval', '15m'))
        self._config['current_interval'] = interval
        self._config['signal_interval'] = interval
        self._config['timeframe_seconds'] = _interval_seconds(interval)
        self._config['compare_interval'] = interval
        self._config['market_interval'] = interval
        self._config['extreme_interval'] = interval

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
                if key == 'strategy_mode' or key not in self._config or value is None:
                    continue
                if key in self.STRING_KEYS:
                    if key == 'current_interval':
                        self._config[key] = _normalize_interval(value)
                    else:
                        self._config[key] = str(value).strip().upper() if key in {'margin_type', 'quote_asset'} else str(value).strip().lower()
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


def _load_strategy_config_from_env():
    mapping = {
        'SIGNAL_INTERVAL': 'current_interval', 'EMA_FAST_PERIOD': 'ema_fast_period',
        'EMA_SLOW_PERIOD': 'ema_slow_period', 'VOLUME_LOOKBACK': 'signal_volume_lookback',
        'BUY_SCORE_THRESHOLD': 'buy_score_threshold', 'SELL_SCORE_THRESHOLD': 'sell_score_threshold',
        'BUY_MIN_SCORE_GAP': 'buy_min_score_gap', 'SELL_MIN_SCORE_GAP': 'sell_min_score_gap',
        'BUY_VOLUME_RATIO': 'buy_min_volume_ratio', 'SELL_VOLUME_RATIO': 'sell_min_volume_ratio',
        'BUY_MIN_BODY_PCT': 'buy_min_body_pct', 'SELL_MIN_BODY_PCT': 'sell_min_body_pct',
        'BUY_CLOSE_POSITION_MIN': 'buy_min_close_position', 'SELL_CLOSE_POSITION_MAX': 'sell_max_close_position',
        'MAX_SIGNAL_CANDLE_RANGE_PCT': 'max_signal_candle_range_pct',
        'BUY_TAKER_RATIO_MIN': 'buy_taker_ratio_min', 'SELL_TAKER_RATIO_MIN': 'sell_taker_ratio_min',
        'BTC_CONTEXT_ENABLED': 'btc_context_enabled', 'BTC_BLOCK_BUY_DROP_PCT': 'btc_block_buy_drop_pct',
        'LONG_TP_ROI_PCT': 'long_tp_roi_pct', 'LONG_SL_ROI_PCT': 'long_sl_roi_pct',
        'SHORT_TP_ROI_PCT': 'short_tp_roi_pct', 'SHORT_SL_ROI_PCT': 'short_sl_roi_pct',
        'ENABLE_DCA_LONG': 'enable_dca_long', 'ENABLE_DCA_SHORT': 'enable_dca_short',
        'DCA_MODE': 'dca_mode', 'DCA_TRIGGER_ROI_PCT': 'dca_trigger_roi_pct',
        'DCA_MULTIPLIER': 'dca_multiplier', 'MAX_DCA_STEPS': 'max_dca_steps',
        'DCA_MIN_SECONDS_BETWEEN_ADDS': 'dca_min_seconds_between_adds',
        'ENABLE_PROFIT_PROTECT': 'profit_protect_enabled',
        'PROTECT_START_ROI_PCT': 'profit_protect_start_roi',
        'PROTECT_PULLBACK_ROI_PCT': 'profit_protect_pullback_roi',
        'REVERSE_MODE': 'reverse_mode', 'REVERSE_MIN_SCORE': 'reverse_min_score',
        'MAX_REVERSE_COUNT': 'max_reverse_count',
        'ENABLE_EXIT_ON_OPPOSITE_SIGNAL': 'enable_exit_on_opposite_signal',
        'OPPOSITE_EXIT_MIN_SCORE': 'opposite_exit_min_score',
        'ENABLE_SIDE_BALANCE': 'enable_side_balance', 'SIDE_BALANCE_MODE': 'side_balance_mode',
        'SIDE_BALANCE_THRESHOLD': 'side_balance_threshold',
        'BALANCE_OVERRIDE_MIN_SIGNAL_SCORE': 'balance_override_min_signal_score',
        'MAX_POSITIONS': 'max_positions',
        'MAX_TOTAL_MARGIN_PER_SYMBOL_PCT': 'max_total_margin_per_symbol_pct',
        'MAX_TOTAL_NOTIONAL_PCT': 'max_total_notional_pct',
        'MAX_DAILY_LOSS_PCT': 'max_daily_loss_pct', 'MARGIN_TYPE': 'margin_type',
        'ENSURE_ONE_WAY_MODE': 'ensure_one_way_mode', 'TRADING_ENABLED': 'trading_enabled',
        'QUOTE_ASSET': 'quote_asset', 'MIN_24H_QUOTE_VOLUME': 'min_24h_volume',
        'SCAN_TOP_N': 'scan_top_coin_limit', 'MAX_SIGNAL_EVAL_COINS': 'max_signal_eval_coins',
        'MIN_COIN_PRICE': 'min_coin_price', 'MAX_COIN_PRICE': 'max_coin_price',
        'MIN_24H_TRADE_COUNT': 'min_24h_trade_count', 'MAX_SPREAD_PCT': 'max_spread_pct',
        'MAX_ABS_24H_CHANGE_PCT': 'max_abs_24h_change_pct',
        'MIN_ABS_24H_CHANGE_PCT': 'min_abs_24h_change_pct',
        'COOLDOWN_AFTER_CLOSE_SECONDS': 'cooldown_after_close_seconds',
        'BLACKLIST_AFTER_TP_SL_SECONDS': 'blacklist_after_tp_sl_seconds',
    }
    bool_keys = {
        'btc_context_enabled', 'enable_dca_long', 'enable_dca_short',
        'profit_protect_enabled', 'enable_exit_on_opposite_signal',
        'enable_side_balance', 'ensure_one_way_mode', 'trading_enabled',
    }
    for env_name, key in mapping.items():
        raw = os.getenv(env_name)
        if raw is None or raw == '':
            continue
        try:
            if key in bool_keys:
                value = 1.0 if raw.strip().lower() in {'1','true','yes','on','y','bat','bật'} else 0.0
            elif key.endswith(('_tp_roi_pct', '_sl_roi_pct')) and raw.strip().lower() in {'none','null','off','false'}:
                value = 0.0
            else:
                value = raw
            _STRATEGY_CONFIG.update(**{key: value})
        except Exception as exc:
            logger.warning(f"Bỏ qua env strategy {env_name}={raw!r}: {exc}")


_load_strategy_config_from_env()



def get_strategy_config_text():
    c = _STRATEGY_CONFIG.get_all()
    return (
        "🎯 <b>LIVE EMA + VOLUME — NẾN ĐÃ ĐÓNG</b>\n\n"
        f"• Khung {c.get('current_interval')} | EMA {int(c.get('ema_fast_period'))}/{int(c.get('ema_slow_period'))} | volume TB {int(c.get('signal_volume_lookback'))} nến\n"
        f"• BUY: score≥{float(c.get('buy_score_threshold')):.2f}, gap≥{float(c.get('buy_min_score_gap')):.2f}, vol≥{float(c.get('buy_min_volume_ratio')):.2f}x, closePos≥{float(c.get('buy_min_close_position')):.2f}\n"
        f"• SELL: score≥{float(c.get('sell_score_threshold')):.2f}, gap≥{float(c.get('sell_min_score_gap')):.2f}, vol≥{float(c.get('sell_min_volume_ratio')):.2f}x, closePos≤{float(c.get('sell_max_close_position')):.2f}\n"
        f"• TP/SL LONG: {float(c.get('long_tp_roi_pct')):.1f}% / {float(c.get('long_sl_roi_pct')):.1f}% ROI\n"
        f"• TP/SL SHORT: {float(c.get('short_tp_roi_pct')):.1f}% / {float(c.get('short_sl_roi_pct')):.1f}% ROI\n"
        f"• DCA: {'BẬT' if float(c.get('enable_dca_long'))>=0.5 or float(c.get('enable_dca_short'))>=0.5 else 'TẮT'} | mode={c.get('dca_mode')} | trigger={float(c.get('dca_trigger_roi_pct')):.1f}% | ×{float(c.get('dca_multiplier')):.2f} | max {int(c.get('max_dca_steps'))}\n"
        f"• Bảo vệ lời: {'BẬT' if float(c.get('profit_protect_enabled'))>=0.5 else 'TẮT'} từ {float(c.get('profit_protect_start_roi')):.1f}%, pullback {float(c.get('profit_protect_pullback_roi')):.1f}%\n"
        f"• Reverse: {c.get('reverse_mode')} | min score {float(c.get('reverse_min_score')):.1f} | max {int(c.get('max_reverse_count'))}\n"
        f"• Side balance: {c.get('side_balance_mode')} | tỷ lệ {float(c.get('side_balance_threshold')):.2f}\n"
        f"• Risk: max positions={int(c.get('max_positions'))}, total notional≤{float(c.get('max_total_notional_pct')):.1f}% equity, margin/symbol≤{float(c.get('max_total_margin_per_symbol_pct')):.1f}%\n"
        f"• Scanner: {c.get('quote_asset')} | min volume={float(c.get('min_24h_volume')):.0f} | top {int(c.get('scan_top_coin_limit'))}, evaluate {int(c.get('max_signal_eval_coins'))} | spread≤{float(c.get('max_spread_pct')):.2f}%\n"
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


def _ema_value(values, period):
    """Tính EMA cuối chuỗi; không phụ thuộc thư viện chỉ báo ngoài."""
    try:
        vals = [float(v) for v in values if float(v) > 0]
        p = max(2, int(period))
        if not vals:
            return 0.0
        seed_count = min(p, len(vals))
        ema = sum(vals[:seed_count]) / seed_count
        alpha = 2.0 / (p + 1.0)
        for value in vals[seed_count:]:
            ema = alpha * value + (1.0 - alpha) * ema
        return float(ema)
    except Exception:
        return 0.0


def _normalized_closed_history(history, prev_closed_candle=None, max_items=250):
    """Chuẩn hóa lịch sử nến đóng, loại trùng theo open time và luôn chứa nến trước."""
    items = []
    seen = set()
    try:
        for candle in list(history or []) + ([prev_closed_candle] if prev_closed_candle else []):
            if not candle:
                continue
            t = int(candle.get('time', 0) if isinstance(candle, dict) else candle[0])
            key = t if t else (len(items), _candle_close(candle))
            if key in seen:
                continue
            seen.add(key)
            items.append(candle)
        items.sort(key=lambda x: int(x.get('time', 0) if isinstance(x, dict) else x[0]))
        return items[-max(5, int(max_items)):]
    except Exception:
        return [prev_closed_candle] if prev_closed_candle else []


def _candle_time_of(c):
    try:
        return int(c.get('time', c.get('open_time', 0)) if isinstance(c, dict) else c[0])
    except Exception:
        return 0


def _candle_close_time_of(c):
    try:
        return int(c.get('close_time', 0) if isinstance(c, dict) else c[6])
    except Exception:
        return 0


_BTC_CONTEXT_CACHE = {'ts': 0.0, 'interval': None, 'bearish': False, 'bullish': False, 'return_pct': 0.0}
_SIGNAL_DECISION_CACHE = {}
_SIGNAL_DECISION_LOCK = threading.RLock()


def _btc_closed_context(interval, fast_period, slow_period):
    if float(_STRATEGY_CONFIG.get('btc_context_enabled', 1.0) or 0.0) < 0.5:
        return {'bearish': False, 'bullish': False, 'return_pct': 0.0}
    now = time.time()
    if (_BTC_CONTEXT_CACHE.get('interval') == interval and
            now - float(_BTC_CONTEXT_CACHE.get('ts', 0) or 0) < 15):
        return dict(_BTC_CONTEXT_CACHE)
    try:
        limit = min(200, max(40, int(slow_period) + 8))
        rows = binance_api_request(
            'https://fapi.binance.com/fapi/v1/klines',
            params={'symbol': 'BTCUSDT', 'interval': interval, 'limit': limit}
        )
        if not rows:
            return dict(_BTC_CONTEXT_CACHE)
        now_ms_value = int(time.time() * 1000)
        closed = [x for x in rows if len(x) > 6 and int(x[6]) < now_ms_value]
        if len(closed) < max(3, slow_period):
            return dict(_BTC_CONTEXT_CACHE)
        closes = [float(x[4]) for x in closed]
        last = closed[-1]
        fast = _ema_value(closes, fast_period)
        slow = _ema_value(closes, slow_period)
        o = float(last[1]); c = float(last[4])
        ret = (c - o) / o * 100.0 if o > 0 else 0.0
        _BTC_CONTEXT_CACHE.update({
            'ts': now, 'interval': interval,
            'bearish': bool(fast < slow and c < fast),
            'bullish': bool(fast > slow and c > fast),
            'return_pct': ret,
        })
    except Exception as exc:
        logger.warning(f"Không lấy được BTC context: {exc}")
    return dict(_BTC_CONTEXT_CACHE)


def _closed_ema_volume_decision(current_candle=None, prev_closed_candle=None, closed_history=None):
    """Chấm BUY/SELL bằng đúng nến đã đóng; không lấy nến đang chạy làm tín hiệu."""
    cfg = _STRATEGY_CONFIG.get_all()
    curr_raw = current_candle or {}
    prev_raw = prev_closed_candle or {}

    all_closed = _normalized_closed_history(closed_history, prev_raw, max_items=500)
    curr_is_final = bool(curr_raw.get('is_final', False)) if isinstance(curr_raw, dict) else False
    signal_candle = curr_raw if curr_is_final else prev_raw
    signal_time = _candle_time_of(signal_candle)
    if not signal_candle or signal_time <= 0:
        return {
            'signal': None, 'side': None, 'score': 0.0, 'selected_score': 0.0,
            'buy_score': 0.0, 'sell_score': 0.0, 'reason': 'Không có nến đóng để chấm',
            'is_spike': False, 'candle_open_time': 0, 'candle_close_time': 0,
            'components': {}, 'source': 'EMA_VOLUME_CLOSED_LIVE'
        }

    prior = [x for x in all_closed if _candle_time_of(x) < signal_time]
    if curr_is_final and prev_raw and _candle_time_of(prev_raw) < signal_time:
        prior = _normalized_closed_history(prior, prev_raw, max_items=500)
    previous = prior[-1] if prior else None

    fast_period = max(2, int(cfg.get('ema_fast_period', 9)))
    slow_period = max(fast_period + 1, int(cfg.get('ema_slow_period', 21)))
    volume_lookback = max(2, int(cfg.get('signal_volume_lookback', 20)))
    minimum_history = max(slow_period, volume_lookback, 5)
    if not previous or len(prior) < minimum_history:
        return {
            'signal': None, 'side': None, 'score': 0.0, 'selected_score': 0.0,
            'buy_score': 0.0, 'sell_score': 0.0,
            'reason': f'Không đủ nến đóng ({len(prior)}/{minimum_history})',
            'is_spike': False, 'candle_open_time': signal_time,
            'candle_close_time': _candle_close_time_of(signal_candle),
            'components': {}, 'source': 'EMA_VOLUME_CLOSED_LIVE'
        }

    o = _candle_open(signal_candle); h = _candle_high(signal_candle)
    l = _candle_low(signal_candle); c = _candle_close(signal_candle)
    ph = _candle_high(previous); pl = _candle_low(previous)
    if min(o, h, l, c, ph, pl) <= 0 or h < l:
        return {
            'signal': None, 'side': None, 'score': 0.0, 'selected_score': 0.0,
            'buy_score': 0.0, 'sell_score': 0.0, 'reason': 'Dữ liệu nến đóng không hợp lệ',
            'is_spike': False, 'candle_open_time': signal_time,
            'candle_close_time': _candle_close_time_of(signal_candle),
            'components': {}, 'source': 'EMA_VOLUME_CLOSED_LIVE'
        }

    closes_before = [_candle_close(x) for x in prior if _candle_close(x) > 0]
    ema_fast = _ema_value(closes_before + [c], fast_period)
    ema_slow = _ema_value(closes_before + [c], slow_period)
    ema_fast_prev = _ema_value(closes_before, fast_period)

    volumes = [_selected_volume_of(x) for x in prior[-volume_lookback:] if _selected_volume_of(x) > 0]
    avg_volume = sum(volumes) / len(volumes) if volumes else 0.0
    current_volume = _selected_volume_of(signal_candle)
    volume_ratio = current_volume / avg_volume if avg_volume > 0 else 0.0

    range_value = max(0.0, h - l)
    range_pct = range_value / o * 100.0 if o > 0 else 0.0
    body_pct = abs(c - o) / o * 100.0 if o > 0 else 0.0
    close_position = 0.5 if range_value <= 0 else (c - l) / range_value
    qv = max(0.0, _quote_volume_of(signal_candle))
    taker_buy_ratio = _clamp(_taker_buy_quote_of(signal_candle) / qv if qv > 0 else 0.5, 0.0, 1.0)
    taker_sell_ratio = 1.0 - taker_buy_ratio

    buy_score = 0.0; sell_score = 0.0
    buy_parts = []; sell_parts = []

    if c > ema_fast:
        buy_score += 1.5; buy_parts.append('close>EMAfast +1.5')
    if ema_fast > ema_slow and ema_fast >= ema_fast_prev:
        buy_score += 2.0; buy_parts.append('EMA tăng +2.0')
    if c > ph:
        buy_score += 1.5; buy_parts.append('phá đỉnh +1.5')
    if c > o and body_pct >= float(cfg.get('buy_min_body_pct', 0.15)):
        buy_score += 1.0; buy_parts.append('thân BUY +1.0')
    if volume_ratio >= float(cfg.get('buy_min_volume_ratio', 1.50)):
        buy_score += 2.0; buy_parts.append('volume BUY +2.0')
    if close_position >= float(cfg.get('buy_min_close_position', 0.65)):
        buy_score += 1.0; buy_parts.append('đóng gần đỉnh +1.0')
    if taker_buy_ratio >= float(cfg.get('buy_taker_ratio_min', 0.55)):
        buy_score += 0.75; buy_parts.append('taker BUY +0.75')

    if c < ema_fast:
        sell_score += 1.5; sell_parts.append('close<EMAfast +1.5')
    if ema_fast < ema_slow and ema_fast <= ema_fast_prev:
        sell_score += 1.5; sell_parts.append('EMA giảm +1.5')
    if c < pl:
        sell_score += 1.5; sell_parts.append('phá đáy +1.5')
    if c < o and body_pct >= float(cfg.get('sell_min_body_pct', 0.08)):
        sell_score += 1.0; sell_parts.append('thân SELL +1.0')
    if volume_ratio >= float(cfg.get('sell_min_volume_ratio', 1.10)):
        sell_score += 1.5; sell_parts.append('volume SELL +1.5')
    if close_position <= float(cfg.get('sell_max_close_position', 0.45)):
        sell_score += 1.0; sell_parts.append('đóng gần đáy +1.0')
    if taker_sell_ratio >= float(cfg.get('sell_taker_ratio_min', 0.55)):
        sell_score += 0.75; sell_parts.append('taker SELL +0.75')

    interval = _normalize_interval(cfg.get('current_interval', '15m'))
    btc = _btc_closed_context(interval, fast_period, slow_period)
    btc_buy_blocked = (
        float(cfg.get('btc_context_enabled', 1.0) or 0.0) >= 0.5 and
        float(btc.get('return_pct', 0.0) or 0.0) <= -abs(float(cfg.get('btc_block_buy_drop_pct', 1.0)))
    )
    if btc.get('bearish'):
        sell_score += 0.5; sell_parts.append('BTC yếu +0.5')
    elif btc.get('bullish'):
        buy_score += 0.5; buy_parts.append('BTC hỗ trợ +0.5')

    spike = range_pct > float(cfg.get('max_signal_candle_range_pct', 5.0))
    side = None
    reason = 'Không đạt ngưỡng'
    buy_threshold = float(cfg.get('buy_score_threshold', 7.0))
    sell_threshold = float(cfg.get('sell_score_threshold', 5.0))
    buy_gap = float(cfg.get('buy_min_score_gap', 1.0))
    sell_gap = float(cfg.get('sell_min_score_gap', 0.4))

    if spike:
        reason = f"Chặn spike: range {range_pct:.2f}% > {float(cfg.get('max_signal_candle_range_pct', 5.0)):.2f}%"
    else:
        buy_ok = buy_score >= buy_threshold and not btc_buy_blocked
        sell_ok = sell_score >= sell_threshold
        if buy_ok and buy_score - sell_score >= buy_gap:
            side = 'BUY'; reason = '; '.join(buy_parts)
        if sell_ok and sell_score - buy_score >= sell_gap:
            if side is None or sell_score > buy_score:
                side = 'SELL'; reason = '; '.join(sell_parts)
        if buy_ok and sell_ok and abs(buy_score - sell_score) < min(buy_gap, sell_gap):
            side = None; reason = 'BUY/SELL quá gần nhau, chờ nến tiếp theo'
        if btc_buy_blocked and buy_score >= buy_threshold:
            reason = f"BUY bị chặn do BTC giảm {float(btc.get('return_pct', 0.0)):.2f}%"

    selected = buy_score if side == 'BUY' else sell_score if side == 'SELL' else max(buy_score, sell_score)
    details = {
        'signal': side, 'side': side, 'score': selected, 'selected_score': selected,
        'buy_score': buy_score, 'sell_score': sell_score,
        'reason': reason, 'is_spike': spike,
        'candle_open_time': signal_time,
        'candle_close_time': _candle_close_time_of(signal_candle),
        'source': 'EMA_VOLUME_CLOSED_LIVE',
        'components': {
            'ema_fast': ema_fast, 'ema_slow': ema_slow, 'volume_ratio': volume_ratio,
            'body_pct': body_pct, 'range_pct': range_pct, 'close_position': close_position,
            'taker_buy_ratio': taker_buy_ratio, 'taker_sell_ratio': taker_sell_ratio,
            'buy_parts': buy_parts, 'sell_parts': sell_parts, 'btc': btc, 'close': c,
        },
        'current_volume': current_volume,
        'previous_volume': _selected_volume_of(previous),
        'current_range_pct': range_pct,
        'num_trades': _num_trades_of(signal_candle),
    }
    with _SIGNAL_DECISION_LOCK:
        _SIGNAL_DECISION_CACHE[(str(signal_candle.get('symbol', '') if isinstance(signal_candle, dict) else ''), signal_time)] = details
        if len(_SIGNAL_DECISION_CACHE) > 500:
            for key in list(_SIGNAL_DECISION_CACHE.keys())[:100]:
                _SIGNAL_DECISION_CACHE.pop(key, None)
    return details


def _volatility_volume_range_signal(current_candle=None, prev_closed_candle=None, mode='entry', closed_history=None):
    details = _closed_ema_volume_decision(current_candle, prev_closed_candle, closed_history)
    return details.get('signal'), float(details.get('selected_score', 0.0) or 0.0), details.get('reason', ''), bool(details.get('is_spike'))


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
    return _volatility_volume_range_signal(candle, prev_candle or {}, mode=mode, closed_history=None)


def _closed_force_current_confirm_signal(current_candle, closed_candle=None, mode='entry'):
    # Tên cũ giữ tương thích; logic mới dùng volume + biên độ nến hiện tại so với nến đóng gần nhất.
    return _volatility_volume_range_signal(current_candle, closed_candle or {}, mode=mode, closed_history=None)


def _fetch_rest_1m15m_signal_data(symbol):
    """Tên cũ giữ tương thích: lấy nến hiện tại và nến đóng gần nhất của khung tín hiệu."""
    try:
        cfg = _STRATEGY_CONFIG.get_all()
        current_interval = _normalize_interval(cfg.get('current_interval', '1m'))
        symbol = symbol.upper()
        now = time.time()
        key = (symbol, current_interval, 'ema_volume_v2')
        cached = _SIGNAL_DATA_CACHE.get(key)
        if cached and now - cached.get('ts', 0) < _SIGNAL_DATA_CACHE_TTL:
            return cached['data']

        url = "https://fapi.binance.com/fapi/v1/klines"
        history_limit = min(200, max(40, int(cfg.get('ema_slow_period', 21)) + 10, int(cfg.get('signal_volume_lookback', 20)) + 10))
        data = binance_api_request(url, params={"symbol": symbol, "interval": current_interval, "limit": history_limit})
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
        logger.error(f"Lỗi REST lấy dữ liệu tín hiệu EMA-volume {symbol}: {e}")
        return None, None, None, []




def compute_signal_from_candles(prev_candle=None, curr_candle=None, prev15m_candle=None, recent_1m_history=None):
    """Trả hướng vào lệnh theo trạng thái tương đối của nến hiện tại và nến trước."""
    try:
        signal, _, _, _ = _volatility_volume_range_signal(curr_candle, prev_candle or {}, mode='entry', closed_history=recent_1m_history)
        return signal
    except Exception as e:
        logger.error(f"Lỗi tính tín hiệu nến tương đối: {e}")
        return None


def get_candle_signal_1h(symbol):
    """Tên cũ để tương thích; sử dụng khung nến đang cấu hình."""
    try:
        details = get_candle_signal_details(symbol)
        return details.get('signal') if details else None
    except Exception as e:
        logger.error(f"Lỗi phân tích tín hiệu tương đối {symbol}: {e}")
        return None


def get_candle_signal_details(symbol):
    """Lấy tín hiệu từ nến đã đóng gần nhất của khung đang cấu hình."""
    try:
        curr, prev, _, closed_history = _fetch_rest_1m15m_signal_data(symbol)
        if curr is None or prev is None:
            return {
                'symbol': str(symbol).upper() if symbol else symbol,
                'signal': None, 'score': 0.0, 'selected_score': 0.0,
                'buy_score': 0.0, 'sell_score': 0.0,
                'reason': 'Không lấy được đủ nến', 'is_spike': False,
                'source': 'EMA_VOLUME_CLOSED_LIVE',
            }
        details = _closed_ema_volume_decision(curr, prev, closed_history)
        details['symbol'] = str(symbol).upper()
        return details
    except Exception as e:
        logger.error(f"Lỗi lấy chi tiết tín hiệu nến đóng {symbol}: {e}")
        return {
            'symbol': symbol, 'signal': None, 'score': 0.0, 'selected_score': 0.0,
            'buy_score': 0.0, 'sell_score': 0.0,
            'reason': f'error: {e}', 'is_spike': False,
            'source': 'EMA_VOLUME_CLOSED_LIVE'
        }

def get_positions(symbol=None, api_key=None, api_secret=None):
    try:
        ts = _signed_timestamp()
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
        ts = _signed_timestamp()
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
            ts = _signed_timestamp()
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
        try:
            symbol = str(coin.get('symbol', '')).upper()
            if not symbol or symbol in _SYMBOL_BLACKLIST:
                return False, 'blacklist', 0.0, 999.0, 0
            if excluded_coins and symbol in excluded_coins:
                return False, 'active_excluded', 0.0, 999.0, 0
            if self._bot_manager and self._bot_manager.bot_coordinator.is_temp_blacklisted(symbol):
                return False, 'temp_blacklist', 0.0, 999.0, 0
            if self._bot_manager and self._bot_manager.coin_manager.is_coin_active(symbol):
                return False, 'coin_active', 0.0, 999.0, 0
            if time.time() < float(_COIN_LOSS_COOLDOWN.get(symbol, 0) or 0):
                return False, 'cooldown_after_loss', 0.0, 999.0, 0

            cfg = _STRATEGY_CONFIG.get_all()
            quote_asset = str(cfg.get('quote_asset', 'USDT')).upper()
            if quote_asset and str(coin.get('quote', '')).upper() != quote_asset:
                return False, 'wrong_quote', 0.0, 999.0, 0

            lev_info = lev_map.get(symbol) or {}
            max_lev = int(float(lev_info.get('max_leverage', coin.get('max_leverage', 0)) or 0))
            if max_lev <= 0:
                max_lev = int(float(coin.get('max_leverage', 50) or 50))
            min_lev = int(float(cfg.get('min_allowed_leverage', 1) or 1))
            if max_lev < max(min_lev, int(self.bot_leverage)):
                return False, 'leverage_low', 0.0, 999.0, max_lev

            quote_volume = float(coin.get('quote_volume', 0.0) or 0.0)
            if quote_volume < float(cfg.get('min_24h_volume', 0.0) or 0.0):
                return False, 'volume_low', 0.0, 999.0, max_lev
            price = float(coin.get('price', 0.0) or 0.0)
            min_price = float(cfg.get('min_coin_price', 0.0) or 0.0)
            max_price = float(cfg.get('max_coin_price', 0.0) or 0.0)
            if min_price > 0 and price < min_price:
                return False, 'price_low', 0.0, 999.0, max_lev
            if max_price > 0 and price > max_price:
                return False, 'price_high', 0.0, 999.0, max_lev
            trades = int(float(coin.get('trade_count', 0) or 0))
            if trades < int(float(cfg.get('min_24h_trade_count', 0) or 0)):
                return False, 'trades_low', 0.0, 999.0, max_lev
            abs_change = abs(float(coin.get('price_change_percent', 0.0) or 0.0))
            min_change = float(cfg.get('min_abs_24h_change_pct', 0.0) or 0.0)
            max_change = float(cfg.get('max_abs_24h_change_pct', 0.0) or 0.0)
            if min_change > 0 and abs_change < min_change:
                return False, 'change_low', 0.0, 999.0, max_lev
            if max_change > 0 and abs_change > max_change:
                return False, 'change_high', 0.0, 999.0, max_lev

            spread = self._spread_pct_from_book(book_map.get(symbol, {}))
            max_spread = float(cfg.get('max_spread_pct', 999.0) or 999.0)
            if max_spread > 0 and spread > max_spread:
                return False, 'spread_high', 0.0, spread, max_lev
            base_score = quote_volume
            return True, 'ok', base_score, spread, max_lev
        except Exception as e:
            return False, f'filter_error:{e}', 0.0, 999.0, 0

    def find_best_coin_with_balance(self, excluded_coins=None):
        """Quét top thanh khoản và chỉ trả coin đang có tín hiệu nến đóng hợp lệ."""
        try:
            now = time.time()
            if now - self.last_scan_time < self.scan_cooldown:
                return None
            self.last_scan_time = now
            coins = get_coins_with_info()
            if not coins:
                logger.warning("⚠️ Cache coin trống, không thể tìm coin.")
                return None

            cfg = _STRATEGY_CONFIG.get_all()
            book_map = self._get_book_ticker_map()
            lev_map = self._get_leverage_bracket_map()
            candidates = []
            for coin in coins:
                ok, _, base_score, spread, max_lev = self._coin_passes_filters(
                    coin, book_map, lev_map, excluded_coins or set()
                )
                if ok:
                    item = coin.copy()
                    item['_base_score'] = base_score
                    item['_spread_pct'] = spread
                    item['_max_leverage'] = max_lev
                    candidates.append(item)
            if not candidates:
                return None

            candidates.sort(key=lambda x: float(x.get('quote_volume', 0.0) or 0.0), reverse=True)
            top_n = max(1, int(cfg.get('scan_top_coin_limit', 80)))
            eval_n = max(1, int(cfg.get('max_signal_eval_coins', 40)))
            best = None
            for coin in candidates[:top_n][:eval_n]:
                symbol = str(coin.get('symbol', '')).upper()
                details = get_candle_signal_details(symbol)
                if not details.get('signal') or details.get('is_spike'):
                    continue
                rank = (
                    float(details.get('selected_score', details.get('score', 0.0)) or 0.0),
                    float(coin.get('quote_volume', 0.0) or 0.0),
                    -float(coin.get('_spread_pct', 999.0) or 999.0),
                )
                if best is None or rank > best[0]:
                    best = (rank, symbol, details)
            if not best:
                return None
            _, symbol, details = best
            logger.info(
                f"✅ Chọn {symbol} {details.get('signal')} | score={float(details.get('selected_score', 0)):.2f} "
                f"| nến đóng={details.get('candle_open_time')}"
            )
            return symbol
        except Exception as e:
            logger.error(f"❌ Lỗi tìm coin: {str(e)}")
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
        self.closed_history_data = {}
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
            cfg = _STRATEGY_CONFIG.get_all()
            limit = min(200, max(40, int(cfg.get('ema_slow_period', 21)) + 10,
                                     int(cfg.get('signal_volume_lookback', 20)) + 10))
            url = "https://fapi.binance.com/fapi/v1/klines"
            data = binance_api_request(url, params={"symbol": symbol.upper(), "interval": interval, "limit": limit})
            if data and len(data) >= 2:
                converted_closed = [self._to_candle_dict(x, symbol, is_final=True, interval=interval) for x in data[:-1]]
                self.closed_history_data[symbol] = converted_closed
                self.candle_data[symbol] = self._to_candle_dict(data[-1], symbol, is_final=False, interval=interval)
                self.prev_candle_data[symbol] = converted_closed[-1]
        except Exception as e:
            logger.error(f"Lỗi nạp nến ban đầu EMA-volume {symbol}: {e}")

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
                    history = self.closed_history_data.setdefault(symbol, [])
                    history.append(candle.copy())
                    keep = min(250, max(50, int(_STRATEGY_CONFIG.get('ema_slow_period', 21)) + 15,
                                             int(_STRATEGY_CONFIG.get('signal_volume_lookback', 20)) + 15))
                    if len(history) > keep:
                        del history[:-keep]
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
            self.closed_history_data.pop(symbol, None)
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
        return list(self.closed_history_data.get(symbol.upper(), []))

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
        self.log(f"🟢 Bot {strategy_name} đã khởi động | 1 coin | Đòn bẩy: {lev}x | Vốn: {percent}% | Tín hiệu: NẾN TƯƠNG ĐỐI | Thoát: TP/SL + bảo vệ lợi nhuận{tp_sl_info}")

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
                            self.log(f"✅ Đã tìm thấy coin: {found_coin}, chuẩn bị chờ tín hiệu tương đối...")
                            last_coin_search_log = 0
                        else:
                            self.bot_coordinator.finish_coin_search(self.bot_id)
                            if current_time - last_no_coin_found_log > 60:
                                self.log(f"❌ Không tìm thấy coin hợp lệ")
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
            data = self.symbol_data[symbol]
            current_time = time.time()
            if not data['position_open'] and current_time - data.get('added_time', current_time) > 300:
                self.log(f"⏰ {symbol} chờ tín hiệu quá 5 phút, đổi coin")
                self.stop_symbol(symbol, failed=True)
                return False

            if data['position_open']:
                if not self._sync_symbol_position(symbol):
                    return False
                self._check_symbol_tp_sl(symbol)
                return False

            cooldown = float(_STRATEGY_CONFIG.get('cooldown_after_close_seconds', 60) or 0)
            if current_time - data.get('last_trade_time', 0) <= 30:
                return False
            if current_time - data.get('last_close_time', 0) <= cooldown:
                return False
            details = self._get_fresh_realtime_signal(symbol, mode='entry', return_details=True)
            details = self._apply_side_balance(details)
            side = details.get('signal')
            if side is None:
                data['last_entry_check_reason'] = details.get('reason')
                return False
            if self._open_symbol_position(symbol, side, skip_signal_check=False):
                data['last_trade_time'] = current_time
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
            'position_open': False, 'entry': 0.0, 'entry_base': 0.0,
            'side': None, 'qty': 0.0, 'status': 'waiting',
            'last_price': 0.0, 'last_price_time': 0.0,
            'last_trade_time': 0.0, 'last_close_time': 0.0,
            'last_position_check': 0.0, 'last_position_api_sync': 0.0,
            'failed_attempts': 0, 'margin_used': 0.0,
            'initial_margin': 0.0, 'current_margin': 0.0,
            'dca_count': 0, 'last_dca_time': 0.0,
            'reverse_count': 0, 'best_roi': None, 'worst_roi': None,
            'opened_time': 0.0, 'order_busy': False,
            'last_reverse_candle_time': 0, 'last_opposite_check': 0.0,
            'entry_candle_time': 0, 'signal_score': 0.0,
            'balance_reason': '', 'added_time': time.time(),
        }
        self.ws_manager.add_symbol(symbol, lambda p, s=symbol: self._handle_price_update(s, p))
        if self.kline_manager:
            self.kline_manager.add_symbol(symbol, self._on_kline_update)
        self.coin_manager.register_coin(symbol)
        self.log(f"➕ Đã thêm {symbol}; chờ tín hiệu từ NẾN ĐÃ ĐÓNG")

    def _handle_price_update(self, symbol, price):
        if symbol not in self.symbol_data:
            return
        self.symbol_data[symbol]['last_price'] = price
        self.symbol_data[symbol]['last_price_time'] = time.time()

    def _on_kline_update(self, symbol, candle):
        """Callback từ kline manager.
        Chỉ cập nhật trạng thái tín hiệu mới nhất để xem/log.
        Tín hiệu chỉ dùng cho bước vào lệnh; _check_realtime_exit() vẫn không đảo chiều.
        """
        if symbol not in self.symbol_data:
            return

        # Chiến lược dùng nến hiện tại cùng lịch sử đã giữ trong RAM. Không gọi REST trong callback để tránh
        # hàng đợi callback/API làm Railway tăng RAM theo thời gian.
        prev = candle.get('prev_for_signal') or (self.kline_manager.get_prev_candle(symbol) if self.kline_manager else {})
        history = self.kline_manager.get_recent_1m_history(symbol) if self.kline_manager else []
        signal = self._compute_signal_from_candle(candle, prev or {}, None, recent_1m_history=history)
        self.realtime_signal[symbol] = signal
        self.last_signal_time[symbol] = time.time()
        self.symbol_data[symbol]['realtime_signal'] = signal

    def _compute_signal_from_candle(self, current_candle=None, prev_candle=None, prev15_candle=None, mode='entry', return_details=False, recent_1m_history=None):
        """Chấm EMA + volume trên nến đã đóng, trả cả điểm BUY và SELL."""
        try:
            details = _closed_ema_volume_decision(
                current_candle or {}, prev_candle or {}, recent_1m_history or []
            )
            return details if return_details else details.get('signal')
        except Exception as e:
            logger.error(f"Lỗi compute tín hiệu nến đóng: {e}")
            details = {
                'signal': None, 'side': None, 'score': 0.0, 'selected_score': 0.0,
                'buy_score': 0.0, 'sell_score': 0.0,
                'reason': f'error:{e}', 'is_spike': False,
                'source': 'EMA_VOLUME_CLOSED_LIVE'
            }
            return details if return_details else None

    def _get_fresh_realtime_signal(self, symbol, mode='entry', return_details=False):
        """Ưu tiên nến WebSocket; nếu thiếu thì dùng REST fallback."""
        try:
            symbol = symbol.upper()
            current = self.kline_manager.get_candle(symbol) if self.kline_manager else None
            previous = self.kline_manager.get_prev_candle(symbol) if self.kline_manager else None
            history = self.kline_manager.get_recent_1m_history(symbol) if self.kline_manager else []

            if not current or not previous:
                current, previous, _, history = self._get_rest_current_and_prev_candle(symbol)

            if not current or not previous:
                details = {
                    'symbol': symbol, 'signal': None, 'score': 0.0,
                    'reason': 'Chưa có đủ dữ liệu nến hiện tại/nến trước',
                    'is_spike': False, 'source': 'EMA_VOLUME_SEPARATE'
                }
            else:
                details = self._compute_signal_from_candle(
                    current, previous, None, mode=mode,
                    return_details=True, recent_1m_history=history
                )
                details['symbol'] = symbol

            signal = details.get('signal')
            self.realtime_signal[symbol] = signal
            self.last_signal_time[symbol] = time.time()
            if symbol in self.symbol_data:
                self.symbol_data[symbol]['realtime_signal'] = signal
                self.symbol_data[symbol]['last_signal_details'] = details
            return details if return_details else signal
        except Exception as e:
            logger.error(f"Lỗi lấy tín hiệu tương đối {symbol}: {e}")
            details = {
                'signal': None, 'score': 0, 'reason': f'error:{e}',
                'is_spike': False, 'source': 'EMA_VOLUME_SEPARATE'
            }
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
            converted_history = [conv(x, True, interval) for x in market_history]
            return conv(curr, False, interval), conv(prev, True, interval), None, converted_history
        except Exception as e:
            logger.error(f"Lỗi REST fallback lấy nến EMA-volume {symbol}: {e}")
            return None, None, None, []
    def _check_realtime_exit(self, symbol):
        """Đã tắt đảo chiều theo tín hiệu.

        Với chiến lược EMA + volume, bot không dùng tín hiệu ngược để đóng/đảo lệnh.
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
        if not data.get('position_open'):
            return
        entry = float(data.get('entry', 0) or 0)
        qty = abs(float(data.get('qty', 0) or 0))
        if entry <= 0 or qty <= 0:
            return
        current_price = self._get_fresh_price(symbol)
        if current_price <= 0:
            return
        side = data.get('side')
        roi = ((current_price - entry) / entry if side == 'BUY' else (entry - current_price) / entry) * 100.0 * float(self.lev)
        data['best_roi'] = roi if data.get('best_roi') is None else max(float(data.get('best_roi')), roi)
        data['worst_roi'] = roi if data.get('worst_roi') is None else min(float(data.get('worst_roi')), roi)

        max_hold = float(_STRATEGY_CONFIG.get('max_hold_seconds', 0.0) or 0.0)
        if max_hold > 0 and float(data.get('opened_time', 0) or 0) > 0 and time.time() - float(data['opened_time']) >= max_hold:
            self._close_symbol_position(symbol, reason=f"MAX_HOLD {max_hold:.0f}s")
            return

        emergency = float(_STRATEGY_CONFIG.get('emergency_stop_roi', 0.0) or 0.0)
        if emergency > 0 and roi <= -abs(emergency):
            self._close_symbol_position(symbol, reason=f"EMERGENCY_SL {emergency:.2f}%")
            return

        if side == 'BUY':
            directional_tp = float(_STRATEGY_CONFIG.get('long_tp_roi_pct', 0.0) or 0.0)
            directional_sl = float(_STRATEGY_CONFIG.get('long_sl_roi_pct', 0.0) or 0.0)
        else:
            directional_tp = float(_STRATEGY_CONFIG.get('short_tp_roi_pct', 0.0) or 0.0)
            directional_sl = float(_STRATEGY_CONFIG.get('short_sl_roi_pct', 0.0) or 0.0)
        generic_tp = float(_STRATEGY_CONFIG.get('strategy_tp_roi', 0.0) or 0.0)
        generic_sl = float(_STRATEGY_CONFIG.get('strategy_sl_roi', 0.0) or 0.0)
        effective_tp = directional_tp if directional_tp > 0 else generic_tp if generic_tp > 0 else float(self.tp or 0)
        effective_sl = directional_sl if directional_sl > 0 else generic_sl if generic_sl > 0 else float(self.sl or 0)

        _, pnl_now = self._calc_roi_pnl_for_symbol(symbol, price=current_price)
        pnl_txt = f" | PnL≈{pnl_now:.4f}" if pnl_now is not None else ''
        if effective_tp > 0 and roi >= effective_tp:
            self.log(f"🎯 {symbol} đạt TP {effective_tp:.2f}% | ROI {roi:.2f}%{pnl_txt}")
            self._close_symbol_position(symbol, reason=f"TP {effective_tp:.2f}%")
            return
        if effective_sl > 0 and roi <= -abs(effective_sl):
            self.log(f"🛡️ {symbol} đạt SL {effective_sl:.2f}% | ROI {roi:.2f}%{pnl_txt}")
            self._close_symbol_position(symbol, reason=f"SL {effective_sl:.2f}%")
            return

        if float(_STRATEGY_CONFIG.get('profit_protect_enabled', 1.0) or 0.0) >= 0.5:
            start = float(_STRATEGY_CONFIG.get('profit_protect_start_roi', 50.0) or 0.0)
            pullback = float(_STRATEGY_CONFIG.get('profit_protect_pullback_roi', 30.0) or 0.0)
            best = float(data.get('best_roi', roi) or roi)
            if best >= start and best - roi >= pullback:
                self.log(f"🔒 {symbol} bảo vệ lợi nhuận: đỉnh {best:.2f}% -> {roi:.2f}%")
                self._close_symbol_position(symbol, reason=f"TRAILING_PROFIT peak={best:.2f}%")
                return

        if float(_STRATEGY_CONFIG.get('enable_exit_on_opposite_signal', 0.0) or 0.0) >= 0.5:
            now = time.time()
            if now - float(data.get('last_opposite_check', 0) or 0) >= 5:
                data['last_opposite_check'] = now
                details = self._get_fresh_realtime_signal(symbol, mode='entry', return_details=True)
                opposite = 'SELL' if side == 'BUY' else 'BUY'
                opposite_score = float(details.get('buy_score' if opposite == 'BUY' else 'sell_score', 0.0) or 0.0)
                own_score = float(details.get('buy_score' if side == 'BUY' else 'sell_score', 0.0) or 0.0)
                min_score = float(_STRATEGY_CONFIG.get('opposite_exit_min_score', 7.0) or 0.0)
                if opposite_score >= min_score and opposite_score > own_score:
                    self._close_symbol_position(symbol, reason=f"OPPOSITE_SIGNAL {opposite} score={opposite_score:.2f}")
                    return

        if self._should_dca(symbol, roi):
            self._add_dca(symbol, roi)

    def _close_symbol_position(self, symbol, reason="", reverse_side=None):
        with self.symbol_locks[symbol], _ACCOUNT_RISK_LOCK:
            try:
                if symbol not in self.symbol_data or not self.symbol_data[symbol].get('position_open'):
                    return False
                real_pos = self._force_check_position(symbol)
                if real_pos and real_pos.get('_api_error'):
                    self.log(f"⚠️ {symbol} không xác minh được vị thế thật; không gửi lệnh đóng mù")
                    return False
                if not real_pos:
                    self._reset_symbol_position(symbol)
                    return True

                amt = float(real_pos.get('positionAmt', 0) or 0)
                qty = abs(amt)
                if qty <= 0:
                    self._reset_symbol_position(symbol)
                    return True
                old_side = 'BUY' if amt > 0 else 'SELL'
                close_side = 'SELL' if old_side == 'BUY' else 'BUY'
                data = self.symbol_data[symbol]
                close_roi, close_pnl = self._calc_roi_pnl_for_symbol(symbol, pos=real_pos)
                prev_margin = float(data.get('current_margin') or data.get('margin_used') or 0.0)
                prev_reverse_count = int(data.get('reverse_count', 0) or 0)
                if prev_margin <= 0:
                    prev_margin = qty * float(real_pos.get('entryPrice', 0) or self._get_fresh_price(symbol)) / max(float(self.lev), 1.0)

                step = get_step_size(symbol)
                if step > 0:
                    qty = math.floor(qty / step) * step
                    qty = round(qty, 8)
                if qty <= 0:
                    self.log(f"❌ {symbol} qty đóng không hợp lệ")
                    return False

                cancel_all_orders(symbol, self.api_key, self.api_secret)
                result = place_order(
                    symbol, close_side, qty, self.api_key, self.api_secret,
                    reduce_only=True, client_order_id=f"close_{int(time.time())}_{random.randint(1000,9999)}"
                )
                invalidate_position_cache(symbol, self.api_key)
                if not (result and 'orderId' in result):
                    if not self._sync_symbol_position(symbol, force=True):
                        return True
                    self.log(f"❌ Đóng {symbol} thất bại | {result}")
                    return False

                closed_ok, last_pos = self._wait_until_position_closed(symbol)
                if not closed_ok:
                    remain = abs(float((last_pos or {}).get('positionAmt', 0) or 0))
                    if remain > 0:
                        self.log(f"⚠️ {symbol} vẫn còn qty={remain}; giữ local và kiểm tra lại")
                        self._sync_symbol_position(symbol, force=True)
                        return False

                roi_txt = f" | ROI {close_roi:.2f}%" if close_roi is not None else ''
                pnl_txt = f" | PnL≈{close_pnl:.4f}" if close_pnl is not None else ''
                self.log(f"🔴 Đã đóng {symbol} | {reason}{roi_txt}{pnl_txt}")
                self._record_closed_trade_stats(symbol, close_roi, close_pnl)

                if reverse_side is None:
                    reverse_side = self._reverse_side_after_close(symbol, old_side, reason)
                self._reset_symbol_position(symbol)

                if reverse_side:
                    max_rev = int(_STRATEGY_CONFIG.get('max_reverse_count', 1) or 0)
                    if max_rev > 0 and prev_reverse_count >= max_rev:
                        self.log(f"⛔ {symbol} đã đạt max_reverse_count={max_rev}")
                        self._blacklist_and_stop_symbol(symbol, reason='MAX_REVERSE')
                        return True
                    self.log(f"🔄 Reverse LIVE {symbol}: {old_side} -> {reverse_side}")
                    if self._open_symbol_position(
                        symbol, reverse_side, skip_signal_check=True,
                        margin_override=prev_margin, is_reverse=True,
                        reverse_count=prev_reverse_count + 1
                    ):
                        return True
                    self.log(f"❌ Reverse {symbol} thất bại; dừng coin")
                    self.stop_symbol(symbol, failed=True)
                    return True

                self._blacklist_and_stop_symbol(symbol, reason=reason)
                return True
            except Exception as e:
                self.log(f"❌ Lỗi đóng vị thế {symbol}: {str(e)}")
                return False

    def _blacklist_and_stop_symbol(self, symbol, reason=""):
        if symbol not in self.active_symbols:
            return
        code = self._close_reason_code(reason)
        if code in {'TP', 'SL', 'TRAILING_PROFIT'}:
            duration = int(_STRATEGY_CONFIG.get('blacklist_after_tp_sl_seconds', 180) or 0)
        else:
            duration = int(_STRATEGY_CONFIG.get('cooldown_after_close_seconds', 60) or 0)
        if duration > 0:
            self.bot_coordinator.add_temp_blacklist(symbol, duration=duration)
            self.log(f"⛔ {symbol} blacklist {duration}s do {reason}")
        self.stop_symbol(symbol, failed=False)

    def _open_symbol_position(self, symbol, side, skip_signal_check=False, margin_override=None, is_reverse=False, reverse_count=0):
        with self.symbol_locks[symbol], _ACCOUNT_RISK_LOCK:
            try:
                if float(_STRATEGY_CONFIG.get('trading_enabled', 1.0) or 0.0) < 0.5:
                    self.log("⏸️ TRADING_ENABLED đang tắt")
                    return False
                if self.symbol_data.get(symbol, {}).get('position_open'):
                    return False

                details = self._get_fresh_realtime_signal(symbol, mode='entry', return_details=True)
                details = self._apply_side_balance(details)
                if not skip_signal_check:
                    fresh_side = details.get('signal')
                    if fresh_side is None:
                        self.symbol_data[symbol]['last_entry_check_reason'] = details.get('reason')
                        return False
                    if fresh_side != side:
                        self.log(f"↔️ {symbol} tín hiệu đổi {side}->{fresh_side}; chờ vòng sau")
                        return False
                candle_time = int(details.get('candle_open_time', 0) or 0)
                if candle_time > 0 and _LAST_ENTRY_CANDLE.get(symbol) == candle_time and not is_reverse:
                    self.log(f"⏳ {symbol} đã dùng nến đóng {candle_time}; không vào lặp")
                    return False

                if not set_leverage(symbol, self.lev, self.api_key, self.api_secret):
                    self.log(f"❌ {symbol} không cài được leverage {self.lev}x")
                    self.stop_symbol(symbol, failed=True)
                    return False
                margin_type = str(_STRATEGY_CONFIG.get('margin_type', 'ISOLATED')).upper()
                if margin_type in {'ISOLATED', 'CROSSED'}:
                    set_margin_type_live(symbol, margin_type, self.api_key, self.api_secret)

                total_balance, available_balance = get_total_and_available_balance(self.api_key, self.api_secret)
                margin_balance = get_margin_balance(self.api_key, self.api_secret)
                if margin_balance is None or margin_balance <= 0 or available_balance is None:
                    self.log(f"❌ {symbol} không lấy được số dư")
                    return False
                required_usd = float(margin_override) if margin_override is not None else margin_balance * (self.percent / 100.0)
                per_symbol_cap = margin_balance * float(_STRATEGY_CONFIG.get('max_total_margin_per_symbol_pct', 4.0) or 0.0) / 100.0
                if per_symbol_cap > 0:
                    required_usd = min(required_usd, per_symbol_cap)
                if required_usd <= 0 or required_usd > available_balance:
                    self.log(f"❌ {symbol} margin yêu cầu {required_usd:.4f} > khả dụng {available_balance:.4f}")
                    return False

                current_price = self._get_fresh_price(symbol)
                if current_price <= 0:
                    return False
                step_size = get_step_size(symbol)
                min_qty = get_min_qty_from_cache(symbol)
                min_notional = get_min_notional_from_cache(symbol)
                qty = required_usd * float(self.lev) / current_price
                if step_size > 0:
                    qty = math.floor(qty / step_size) * step_size
                    qty = round(qty, 8)
                proposed_notional = qty * current_price
                if qty < min_qty or proposed_notional < min_notional or qty <= 0:
                    self.log(f"❌ {symbol} qty/notional dưới mức Binance")
                    return False

                risk_ok, risk_reason = self._account_risk_check(symbol, required_usd, proposed_notional, margin_balance, available_balance)
                if not risk_ok:
                    self.log(f"🛑 Chặn OPEN {symbol}: {risk_reason}")
                    return False

                result = place_order(
                    symbol, side, qty, self.api_key, self.api_secret,
                    reduce_only=False,
                    client_order_id=f"{'rev' if is_reverse else 'open'}_{int(time.time())}_{random.randint(1000,9999)}"
                )
                invalidate_position_cache(symbol, self.api_key)
                if not (result and 'orderId' in result):
                    self.log(f"❌ {symbol} lỗi mở lệnh: {result}")
                    return False

                executed_qty = float(result.get('executedQty') or result.get('origQty') or qty)
                avg_price = float(result.get('avgPrice') or 0.0)
                for _ in range(12):
                    ok, pos = get_position_strict(symbol, self.api_key, self.api_secret)
                    if ok and pos and abs(float(pos.get('positionAmt', 0) or 0)) > 0:
                        executed_qty = abs(float(pos.get('positionAmt', 0) or executed_qty))
                        avg_price = float(pos.get('entryPrice', 0) or avg_price or current_price)
                        break
                    time.sleep(0.35)
                if avg_price <= 0:
                    avg_price = current_price
                signed_qty = executed_qty if side == 'BUY' else -executed_qty
                self.symbol_data[symbol].update({
                    'entry': avg_price, 'entry_base': avg_price, 'qty': signed_qty,
                    'side': side, 'position_open': True, 'status': 'open',
                    'last_trade_time': time.time(), 'margin_used': required_usd,
                    'initial_margin': required_usd, 'current_margin': required_usd,
                    'dca_count': 0, 'last_dca_time': 0.0,
                    'reverse_count': int(reverse_count) if is_reverse else 0,
                    'best_roi': 0.0, 'worst_roi': 0.0,
                    'opened_time': time.time(), 'entry_candle_time': candle_time,
                    'signal_score': float(details.get('selected_score', 0.0) or 0.0),
                    'balance_reason': details.get('balance_reason', ''),
                })
                if candle_time > 0:
                    _LAST_ENTRY_CANDLE[symbol] = candle_time
                self.bot_coordinator.bot_has_coin(self.bot_id)
                self.consecutive_failures = 0
                self.log(
                    f"✅ OPEN LIVE {symbol} {side} | entry={avg_price:.8g} | qty={executed_qty:.8g} "
                    f"| margin={required_usd:.4f} | lev={self.lev}x | score={float(details.get('selected_score',0)):.2f}"
                )
                return True
            except Exception as e:
                self.log(f"❌ {symbol} lỗi mở vị thế: {str(e)}")
                return False

    def _account_exposure(self):
        ok, positions = get_positions_strict_all(self.api_key, self.api_secret)
        if not ok:
            return None
        result = {'long_notional': 0.0, 'short_notional': 0.0, 'total_notional': 0.0, 'count': 0, 'symbols': set()}
        for pos in positions:
            amt = float(pos.get('positionAmt', 0) or 0)
            if abs(amt) <= 0:
                continue
            price = float(pos.get('markPrice', 0) or pos.get('entryPrice', 0) or 0)
            notional = abs(amt) * price
            result['count'] += 1
            result['symbols'].add(str(pos.get('symbol', '')).upper())
            if amt > 0:
                result['long_notional'] += notional
            else:
                result['short_notional'] += notional
        result['total_notional'] = result['long_notional'] + result['short_notional']
        return result

    def _apply_side_balance(self, details):
        details = dict(details or {})
        if float(_STRATEGY_CONFIG.get('enable_side_balance', 1.0) or 0.0) < 0.5:
            return details
        exposure = self._account_exposure()
        if exposure is None:
            details['signal'] = None
            details['reason'] = 'Không lấy được exposure tài khoản; chặn tín hiệu'
            return details
        long_n = float(exposure['long_notional']); short_n = float(exposure['short_notional'])
        threshold = max(1.0, float(_STRATEGY_CONFIG.get('side_balance_threshold', 1.25) or 1.25))
        preferred = None
        if long_n > 0 and short_n <= 0:
            preferred = 'SELL'
        elif short_n > 0 and long_n <= 0:
            preferred = 'BUY'
        elif long_n > 0 and short_n > 0:
            if long_n / short_n > threshold:
                preferred = 'SELL'
            elif short_n / long_n > threshold:
                preferred = 'BUY'
        if not preferred:
            return details
        reason = f"Cân bằng LIVE LONG={long_n:.2f}, SHORT={short_n:.2f}, ưu tiên {preferred}"
        mode = str(_STRATEGY_CONFIG.get('side_balance_mode', 'override')).lower()
        current = details.get('signal')
        preferred_score = float(details.get('buy_score' if preferred == 'BUY' else 'sell_score', 0.0) or 0.0)
        if mode == 'filter':
            if current != preferred:
                details['signal'] = None
                details['selected_score'] = preferred_score
                details['reason'] = reason + '; tín hiệu hiện tại bị lọc'
        else:
            min_score = float(_STRATEGY_CONFIG.get('balance_override_min_signal_score', 3.0) or 0.0)
            if preferred_score >= min_score:
                details['signal'] = preferred
                details['side'] = preferred
                details['selected_score'] = preferred_score
                details['score'] = preferred_score
                details['reason'] = reason + f"; override score={preferred_score:.2f}"
            elif current != preferred:
                details['signal'] = None
                details['selected_score'] = preferred_score
                details['reason'] = reason + '; score override chưa đủ'
        details['balance_reason'] = reason
        return details

    def _account_risk_check(self, symbol, requested_margin, proposed_notional, margin_balance, available_balance):
        exposure = self._account_exposure()
        if exposure is None:
            return False, 'API positionRisk lỗi'
        if symbol.upper() in exposure['symbols']:
            return False, 'Tài khoản đã có vị thế symbol này'
        max_positions = int(_STRATEGY_CONFIG.get('max_positions', 3) or 0)
        if max_positions > 0 and exposure['count'] >= max_positions:
            return False, f"Đã đạt max_positions={max_positions}"
        max_total_pct = float(_STRATEGY_CONFIG.get('max_total_notional_pct', 150.0) or 0.0)
        max_total = margin_balance * max_total_pct / 100.0 if max_total_pct > 0 else 0.0
        if max_total > 0 and exposure['total_notional'] + proposed_notional > max_total:
            return False, f"Vượt max total notional {max_total:.2f}"
        cap_pct = float(_STRATEGY_CONFIG.get('max_total_margin_per_symbol_pct', 4.0) or 0.0)
        if cap_pct > 0 and requested_margin > margin_balance * cap_pct / 100.0 + 1e-9:
            return False, 'Vượt margin tối đa mỗi symbol'
        if requested_margin > available_balance:
            return False, 'Không đủ available balance'
        return True, 'OK'

    def _should_dca(self, symbol, roi):
        data = self.symbol_data.get(symbol, {})
        side = data.get('side')
        if side == 'BUY' and float(_STRATEGY_CONFIG.get('enable_dca_long', 1.0) or 0.0) < 0.5:
            return False
        if side == 'SELL' and float(_STRATEGY_CONFIG.get('enable_dca_short', 1.0) or 0.0) < 0.5:
            return False
        count = int(data.get('dca_count', 0) or 0)
        if count >= int(_STRATEGY_CONFIG.get('max_dca_steps', 3) or 0):
            return False
        min_gap = float(_STRATEGY_CONFIG.get('dca_min_seconds_between_adds', 20) or 0)
        if time.time() - float(data.get('last_dca_time', 0) or 0) < min_gap:
            return False
        level = float(_STRATEGY_CONFIG.get('dca_trigger_roi_pct', 25.0) or 0.0) * (count + 1)
        mode = str(_STRATEGY_CONFIG.get('dca_mode', 'loss')).lower()
        return roi <= -level if mode == 'loss' else roi >= level

    def _add_dca(self, symbol, roi):
        with self.symbol_locks[symbol], _ACCOUNT_RISK_LOCK:
            data = self.symbol_data.get(symbol, {})
            if not data.get('position_open') or not self._should_dca(symbol, roi):
                return False
            ok, pos = get_position_strict(symbol, self.api_key, self.api_secret)
            if not ok or not pos:
                return False
            amt = float(pos.get('positionAmt', 0) or 0)
            if abs(amt) <= 0:
                return False
            side = 'BUY' if amt > 0 else 'SELL'
            count = int(data.get('dca_count', 0) or 0)
            step_num = count + 1
            initial_margin = float(data.get('initial_margin') or data.get('margin_used') or 0.0)
            add_margin = initial_margin * (float(_STRATEGY_CONFIG.get('dca_multiplier', 1.10) or 1.0) ** step_num)
            total_balance, available = get_total_and_available_balance(self.api_key, self.api_secret)
            margin_balance = get_margin_balance(self.api_key, self.api_secret)
            if margin_balance is None or available is None or add_margin <= 0:
                return False
            current_margin = float(data.get('current_margin') or data.get('margin_used') or initial_margin)
            cap = margin_balance * float(_STRATEGY_CONFIG.get('max_total_margin_per_symbol_pct', 4.0) or 0.0) / 100.0
            if cap > 0 and current_margin + add_margin > cap:
                self.log(f"⛔ DCA {symbol} bước {step_num} vượt cap margin symbol")
                return False
            price = self._get_fresh_price(symbol)
            if price <= 0 or add_margin > available:
                return False
            step_size = get_step_size(symbol)
            add_qty = add_margin * float(self.lev) / price
            if step_size > 0:
                add_qty = math.floor(add_qty / step_size) * step_size
                add_qty = round(add_qty, 8)
            if add_qty < get_min_qty_from_cache(symbol) or add_qty * price < get_min_notional_from_cache(symbol):
                return False
            exposure = self._account_exposure()
            max_pct = float(_STRATEGY_CONFIG.get('max_total_notional_pct', 150.0) or 0.0)
            max_total = margin_balance * max_pct / 100.0 if max_pct > 0 else 0.0
            if exposure is None or (max_total > 0 and exposure['total_notional'] + add_qty * price > max_total):
                self.log(f"⛔ DCA {symbol} bị chặn bởi tổng notional")
                return False
            result = place_order(
                symbol, side, add_qty, self.api_key, self.api_secret,
                reduce_only=False, client_order_id=f"dca{step_num}_{int(time.time())}_{random.randint(1000,9999)}"
            )
            invalidate_position_cache(symbol, self.api_key)
            if not (result and 'orderId' in result):
                self.log(f"❌ DCA {symbol} thất bại: {result}")
                return False
            time.sleep(0.5)
            ok, new_pos = get_position_strict(symbol, self.api_key, self.api_secret)
            if ok and new_pos and abs(float(new_pos.get('positionAmt', 0) or 0)) > 0:
                new_amt = float(new_pos.get('positionAmt', 0) or 0)
                new_entry = float(new_pos.get('entryPrice', 0) or data.get('entry', price))
                data['qty'] = new_amt
                data['entry'] = new_entry
                data['entry_base'] = new_entry
            else:
                old_qty = abs(float(data.get('qty', 0) or 0))
                new_qty = old_qty + add_qty
                old_entry = float(data.get('entry', price) or price)
                data['entry'] = (old_entry * old_qty + price * add_qty) / max(new_qty, 1e-12)
                data['entry_base'] = data['entry']
                data['qty'] = new_qty if side == 'BUY' else -new_qty
            data['current_margin'] = current_margin + add_margin
            data['margin_used'] = data['current_margin']
            data['dca_count'] = step_num
            data['last_dca_time'] = time.time()
            self.log(
                f"➕ DCA LIVE {symbol} {side} bước {step_num}/{int(_STRATEGY_CONFIG.get('max_dca_steps',3))} "
                f"| add_margin={add_margin:.4f} | avg_entry={float(data.get('entry',0)):.8g}"
            )
            return True

    @staticmethod
    def _close_reason_code(reason):
        text = str(reason or '').upper()
        if text.startswith('TP'):
            return 'TP'
        if text.startswith('SL') or 'EMERGENCY' in text:
            return 'SL'
        if 'TRAIL' in text or 'PROTECT' in text:
            return 'TRAILING_PROFIT'
        if 'OPPOSITE' in text:
            return 'OPPOSITE_SIGNAL'
        if 'MANUAL' in text or 'STOP BY USER' in text:
            return 'MANUAL'
        return text.replace(' ', '_')[:64]

    def _reverse_side_after_close(self, symbol, old_side, reason):
        if self._close_reason_code(reason) not in {'SL', 'TRAILING_PROFIT', 'OPPOSITE_SIGNAL'}:
            return None
        mode = str(_STRATEGY_CONFIG.get('reverse_mode', 'confirmed')).lower()
        if mode == 'none':
            return None
        opposite = 'SELL' if old_side == 'BUY' else 'BUY'
        if mode == 'immediate':
            return opposite
        details = self._get_fresh_realtime_signal(symbol, mode='entry', return_details=True)
        opposite_score = float(details.get('buy_score' if opposite == 'BUY' else 'sell_score', 0.0) or 0.0)
        old_score = float(details.get('buy_score' if old_side == 'BUY' else 'sell_score', 0.0) or 0.0)
        min_score = float(_STRATEGY_CONFIG.get('reverse_min_score', 7.0) or 0.0)
        if opposite_score >= min_score and opposite_score > old_score:
            return opposite
        return None

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
                'position_open': False, 'entry': 0.0, 'entry_base': 0.0,
                'side': None, 'qty': 0.0, 'status': 'closed',
                'margin_used': 0.0, 'initial_margin': 0.0, 'current_margin': 0.0,
                'dca_count': 0, 'last_dca_time': 0.0,
                'best_roi': None, 'worst_roi': None,
                'opened_time': 0.0, 'entry_candle_time': 0,
                'signal_score': 0.0, 'balance_reason': '',
            })
            now = time.time()
            self.symbol_data[symbol]['last_close_time'] = now
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
            self.log("🟢 HỆ THỐNG BOT RELATIVE CANDLE - CLEAN")
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
            sync_binance_time()
            balance = get_balance(self.api_key, self.api_secret)
            if balance is None:
                self.log("❌ Không thể kết nối Binance/API key")
                return False
            if float(_STRATEGY_CONFIG.get('ensure_one_way_mode', 1.0) or 0.0) >= 0.5:
                ok, message = ensure_one_way_mode_live(self.api_key, self.api_secret)
                if not ok:
                    self.log(f"❌ Không bảo đảm được One-way Mode: {message}")
                    return False
            self.log(f"✅ Kết nối Binance LIVE thành công | available={balance:.2f}")
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

            summary = "📊 **THỐNG KÊ CHI TIẾT - BOT RELATIVE CANDLE**\n\n"

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
            "🤖 <b>BOT GIAO DỊCH FUTURES - RELATIVE CANDLE</b>\n\n"
            "🎯 <b>CƠ CHẾ HOẠT ĐỘNG:</b>\n"
            "• Tín hiệu vào lệnh dựa trên trạng thái tương đối của nến hiện tại và nến trước.\n"
            "• Điều kiện mềm: hướng nến và close là chính; volume, range và taker chỉ cộng điểm.\n"
            "• Bot động chọn một coin hợp lệ rồi chờ BUY/SELL theo nến tương đối.\n"
            "• Khi đang có vị thế, bot KHÔNG đảo chiều theo tín hiệu.\n"
            "• Lệnh chỉ thoát bằng TP/SL hoặc bảo vệ lợi nhuận tụt từ đỉnh.\n"
            "• TP/SL trong mục Chiến lược có thể chỉnh sau khi bot đã vào lệnh.\n\n"
            "📌 <b>LƯU Ý:</b> Đây vẫn là chiến lược Futures rủi ro cao; hãy chạy vốn nhỏ để kiểm thử trước."
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
            success_msg = (f"✅ <b>ĐÃ TẠO {created_count} BOT RELATIVE CANDLE</b>\n\n"
                           f"🎯 Chiến lược: {strategy_type}\n💰 Đòn bẩy: {lev}x\n"
                           f"📈 % Số dư: {percent}%\n{tp_info}\n{sl_info}\n"
                           f"🔧 Chế độ: {bot_mode}\n🔢 Số bot: {created_count}\n")
            if bot_mode == 'static' and symbol:
                success_msg += f"🔗 Coin ban đầu: {symbol}\n"
            else:
                success_msg += f"🔗 Coin: Tự động chọn random một coin hợp lệ (USDT/USDC)\n"
            success_msg += "🎯 Tín hiệu nến tương đối; thoát bằng TP/SL và bảo vệ lợi nhuận.\n"
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

        signal_key_map = {
            '✏️ Khung tín hiệu': ('current_interval', 'Khung hợp lệ: 1m, 3m, 5m, 15m, 30m, 1h, 2h, 4h.'),
            '✏️ EMA nhanh': ('ema_fast_period', 'Số chu kỳ EMA nhanh, phải nhỏ hơn EMA chậm.'),
            '✏️ EMA chậm': ('ema_slow_period', 'Số chu kỳ EMA chậm, phải lớn hơn EMA nhanh.'),
            '✏️ Số nến volume TB': ('signal_volume_lookback', 'Số nến đóng dùng tính volume trung bình.'),
            '✏️ Điểm BUY': ('buy_score_threshold', 'Điểm BUY tối thiểu. Tăng số này để BUY khó hơn.'),
            '✏️ Điểm SELL': ('sell_score_threshold', 'Điểm SELL tối thiểu. Tăng số này để SELL khó hơn.'),
            '✏️ Volume BUY x': ('buy_min_volume_ratio', 'Volume ước tính của nến hiện tại / volume trung bình. Ví dụ 1.10 = 110%.'),
            '✏️ Volume SELL x': ('sell_min_volume_ratio', 'Volume ước tính của nến hiện tại / volume trung bình.'),
            '✏️ Khoảng cách điểm BUY': ('buy_min_score_gap', 'Điểm BUY phải hơn điểm SELL ít nhất mức này.'),
            '✏️ Khoảng cách điểm SELL': ('sell_min_score_gap', 'Điểm SELL phải hơn điểm BUY ít nhất mức này.'),
            '✏️ Vị trí close BUY': ('buy_min_close_position', '0-1. BUY yêu cầu close nằm từ vị trí này trở lên trong biên nến.'),
            '✏️ Vị trí close SELL': ('sell_max_close_position', '0-1. SELL yêu cầu close nằm từ vị trí này trở xuống trong biên nến.'),
            '✏️ EMA nghiêm BUY': ('buy_require_ema_trend', '1 = bắt buộc EMA nhanh > EMA chậm và đang tăng; 0 = EMA chỉ tính điểm.'),
            '✏️ EMA nghiêm SELL': ('sell_require_ema_trend', '1 = bắt buộc EMA nhanh < EMA chậm và đang giảm; 0 = EMA chỉ tính điểm.'),
        }

        filter_key_map = {
            '✏️ Min 24h Vol (USDT)': 'min_24h_volume',
            '✏️ Min Price': 'min_coin_price',
            '✏️ Max Price': 'max_coin_price',
            '✏️ Min Trades': 'min_24h_trade_count',
            '✏️ Min Abs Change %': 'min_abs_24h_change_pct',
            '✏️ Max Abs Change %': 'max_abs_24h_change_pct',
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
            elif text == "📡 Cấu hình tín hiệu BUY/SELL":
                self.user_states[chat_id] = {'step': 'waiting_signal_config'}
                send_telegram("📡 Chọn tham số tín hiệu cần chỉnh. BUY đang được đặt khó hơn SELL:", chat_id=chat_id,
                             reply_markup=create_signal_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            elif text == "⚙️ Bộ lọc coin (khối lượng, giá,...)":
                self.user_states[chat_id] = {'step': 'waiting_filter_config'}
                send_telegram("🔧 Chọn tham số bộ lọc coin để chỉnh sửa:", chat_id=chat_id,
                             reply_markup=create_filter_keyboard(),
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

        elif current_step == 'waiting_signal_config':
            if text == "🔙 Quay lại cấu hình chiến lược":
                self.user_states[chat_id] = {'step': 'waiting_strategy_config'}
                send_telegram("🔙 Quay lại menu chiến lược.", chat_id=chat_id,
                             reply_markup=create_strategy_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return
            if text in signal_key_map:
                key, help_text = signal_key_map[text]
                self.user_states[chat_id] = {'step': 'waiting_signal_value', 'strategy_key': key}
                send_telegram(f"✏️ Nhập giá trị mới cho <b>{key}</b>\n{help_text}", chat_id=chat_id,
                             reply_markup=create_signal_value_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("⚠️ Chọn tham số tín hiệu cần chỉnh.", chat_id=chat_id,
                             reply_markup=create_signal_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step == 'waiting_filter_config':
            if text == "🔙 Quay lại cấu hình chiến lược":
                self.user_states[chat_id] = {'step': 'waiting_strategy_config'}
                send_telegram("🔙 Quay lại menu chiến lược.", chat_id=chat_id,
                             reply_markup=create_strategy_config_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                return
            if text in filter_key_map:
                key = filter_key_map[text]
                self.user_states[chat_id] = {'step': 'waiting_filter_value', 'strategy_key': key}
                send_telegram(f"✏️ Nhập giá trị mới cho <b>{key}</b> (0 = tắt lọc):", chat_id=chat_id,
                             reply_markup=create_strategy_value_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            else:
                send_telegram("⚠️ Chọn tham số cần chỉnh.", chat_id=chat_id,
                             reply_markup=create_filter_keyboard(),
                             bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)

        elif current_step in ('waiting_strategy_value', 'waiting_filter_value', 'waiting_signal_value'):
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
                    # Các key số nguyên và ràng buộc riêng cho bộ tín hiệu.
                    int_keys = {'max_reverse_count', 'entry_min_trades', 'exit_min_trades', 'scan_top_coin_limit',
                                'confirm_min_trades', 'max_signal_eval_coins', 'min_24h_trade_count',
                                'target_leverage', 'min_allowed_leverage', 'max_consecutive_losses_before_pause',
                                'max_hold_seconds', 'coin_cooldown_after_loss_sec', 'ema_fast_period',
                                'ema_slow_period', 'signal_volume_lookback'}
                    if key in int_keys:
                        val = int(val)
                        if val < 0 or val > 10000:
                            raise ValueError
                    else:
                        if val < 0:
                            raise ValueError
                        if key in ('buy_taker_ratio_min', 'sell_taker_ratio_min', 'exit_taker_ratio_min',
                                   'absorption_taker_ratio', 'buy_min_close_position', 'sell_max_close_position') and val > 1:
                            raise ValueError
                        if key in ('buy_require_ema_trend', 'sell_require_ema_trend') and val not in (0, 1):
                            raise ValueError
                        if key in ('buy_min_volume_ratio', 'sell_min_volume_ratio') and val > 10:
                            raise ValueError
                        if key in ('buy_score_threshold', 'sell_score_threshold', 'buy_min_score_gap', 'sell_min_score_gap') and val > 50:
                            raise ValueError

                    # Kiểm tra quan hệ EMA trước khi ghi cấu hình.
                    current_cfg = _STRATEGY_CONFIG.get_all()
                    proposed_fast = val if key == 'ema_fast_period' else int(current_cfg.get('ema_fast_period', 9))
                    proposed_slow = val if key == 'ema_slow_period' else int(current_cfg.get('ema_slow_period', 21))
                    if proposed_fast < 2 or proposed_slow < 3 or proposed_fast >= proposed_slow:
                        raise ValueError
                    if key == 'signal_volume_lookback' and not (2 <= val <= 200):
                        raise ValueError
                    _STRATEGY_CONFIG.update(**{key: val})

                # Đổi khung/EMA/lookback cần nạp lại lịch sử và WebSocket cho coin đang chạy.
                if (current_step == 'waiting_signal_value' and self.kline_manager
                        and key in ('current_interval', 'ema_fast_period', 'ema_slow_period', 'signal_volume_lookback')):
                    # BotManager không có symbol_data/_on_kline_update; nạp lại qua từng BaseBot.
                    for bot in list(self.bots.values()):
                        for active_symbol in list(getattr(bot, 'active_symbols', []) or []):
                            try:
                                self.kline_manager.remove_symbol(active_symbol)
                                self.kline_manager.add_symbol(active_symbol, bot._on_kline_update)
                            except Exception as reload_err:
                                logger.error(f"Lỗi nạp lại dữ liệu tín hiệu {active_symbol}: {reload_err}")
                # Quay lại menu tương ứng
                if current_step == 'waiting_filter_value':
                    self.user_states[chat_id] = {'step': 'waiting_filter_config'}
                    send_telegram("✅ Đã cập nhật.\n\n" + get_strategy_config_text(), chat_id=chat_id,
                                 reply_markup=create_filter_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                elif current_step == 'waiting_signal_value':
                    self.user_states[chat_id] = {'step': 'waiting_signal_config'}
                    send_telegram("✅ Đã cập nhật tín hiệu.\n\n" + get_strategy_config_text(), chat_id=chat_id,
                                 reply_markup=create_signal_config_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
                else:
                    self.user_states[chat_id] = {'step': 'waiting_strategy_config'}
                    send_telegram("✅ Đã cập nhật.\n\n" + get_strategy_config_text(), chat_id=chat_id,
                                 reply_markup=create_strategy_config_keyboard(),
                                 bot_token=self.telegram_bot_token, default_chat_id=self.telegram_chat_id)
            except Exception:
                error_keyboard = create_signal_value_keyboard() if current_step == 'waiting_signal_value' else create_strategy_value_keyboard()
                send_telegram("⚠️ Giá trị không hợp lệ. Hãy nhập giá trị phù hợp.", chat_id=chat_id,
                             reply_markup=error_keyboard,
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
                    f"✅ <b>ĐÃ TẠO BOT EMA + VOLUME THÀNH CÔNG</b>\n\n"
                    f"🤖 Chiến lược: BUY/SELL tách riêng theo EMA + volume\n"
                    f"🔧 Chế độ: {bot_mode}\n"
                    f"🔢 Số bot: {bot_count}\n"
                    f"💰 Đòn bẩy: {leverage}x\n"
                    f"📊 % Số dư: {percent}%\n"
                    f"🎯 TP: {tp if tp else 'Tắt'}\n"
                    f"🛡️ SL: {sl if sl else 'Tắt'}\n"
                    f"🔄 Thoát: chỉ TP/SL hoặc bảo vệ lợi nhuận tụt từ đỉnh\n"
                    f"⚖️ Điều kiện tín hiệu: BUY khó hơn SELL, chỉnh riêng trong menu chiến lược\n\n"
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
