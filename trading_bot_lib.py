#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
BOT LIVE TRADING — EMA + VOLUME — POSTGRESQL/RAILWAY
================================================================
File đơn, chia thành các phần:
    Config
    Binance Client (live)
    Database
    Signal Engine
    Balance Manager
    Scanner
    Position / DCA / Reverse Manager (live)
    Statistics
    Telegram
    Main Loop

Đặc điểm chính:
- Giao dịch thật trên Binance Futures (MARKET order).
- BUY và SELL chấm điểm riêng; BUY mặc định khó hơn SELL.
- Không dùng RSI.
- Chỉ dùng nến đã đóng làm tín hiệu chính.
- TP/SL riêng LONG và SHORT theo ROI margin (đóng bằng MARKET khi chạm).
- DCA cho cả LONG và SHORT, lượng nhồi = margin ban đầu * 1.1^n.
- Đảo chiều none/immediate/confirmed sau khi vị thế cũ đã được xác nhận đóng (positionAmt = 0).
- Cân bằng tổng notional LONG/SHORT theo filter hoặc override.
- PostgreSQL là nguồn lưu lịch sử/metadata; Binance là nguồn sự thật vị thế thật.
- Khôi phục vị thế thật sau restart; advisory lock chống hai Railway replica cùng chạy.
- Khi database lỗi: chặn OPEN/DCA; vị thế hiện tại vẫn được theo dõi và đóng được.
- Mọi OPEN/DCA/CLOSE/REVERSE đều có event riêng.

Cài thư viện:
    pip install requests psycopg2-binary python-dotenv

Biến môi trường bắt buộc:
    DATABASE_URL
    BINANCE_API_KEY
    BINANCE_API_SECRET
    (TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID tùy chọn)

File này chạy LIVE TRADING - cẩn thận khi sử dụng!
"""

from __future__ import annotations

import hashlib
import hmac
import json
import logging
import math
import os
import signal as os_signal
import sys
import threading
import time
import traceback
import uuid
from dataclasses import asdict, dataclass, fields
from datetime import datetime, timezone
from decimal import Decimal, ROUND_DOWN
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple
from urllib.parse import urlencode

import requests
from requests import Response

# Thư viện dotenv để đọc file .env
try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

try:
    import psycopg2
    import psycopg2.extras
    from psycopg2.extensions import connection as PGConnection
except Exception:
    psycopg2 = None
    PGConnection = Any


# =============================================================================
# LOGGING + HELPERS
# =============================================================================

LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO").upper()
logging.basicConfig(
    level=getattr(logging, LOG_LEVEL, logging.INFO),
    format="%(asctime)s | %(levelname)s | %(threadName)s | %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("trading_bot.log", encoding="utf-8"),
    ],
)
logger = logging.getLogger("futures-bot")

UTC = timezone.utc
ACTIVE_DB_STATUSES = ("PENDING_OPEN", "ACTIVE", "PENDING_CLOSE", "RECOVERED")
CLOSE_REASONS_BLACKLIST = {"TP", "SL", "TRAILING_PROFIT"}


def utc_now() -> datetime:
    return datetime.now(tz=UTC)


def now_ms() -> int:
    return int(time.time() * 1000)


def safe_float(value: Any, default: float = 0.0) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def safe_int(value: Any, default: int = 0) -> int:
    try:
        return int(float(value))
    except (TypeError, ValueError):
        return default


def env_bool(name: str, default: bool) -> bool:
    raw = os.getenv(name)
    if raw is None:
        return default
    return raw.strip().lower() in {"1", "true", "yes", "y", "on", "bat", "bật"}


def env_float(name: str, default: float) -> float:
    raw = os.getenv(name)
    return default if raw in (None, "") else float(raw)


def env_int(name: str, default: int) -> int:
    raw = os.getenv(name)
    return default if raw in (None, "") else int(float(raw))


def env_optional_float(name: str, default: Optional[float]) -> Optional[float]:
    raw = os.getenv(name)
    if raw is None:
        return default
    if raw.strip().lower() in {"", "none", "null", "off", "false"}:
        return None
    return float(raw)


def env_csv(name: str, default: Sequence[str] = ()) -> Tuple[str, ...]:
    raw = os.getenv(name)
    if not raw:
        return tuple(default)
    return tuple(x.strip().upper() for x in raw.split(",") if x.strip())


def json_text(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, default=str, separators=(",", ":"))


def short_id(prefix: str) -> str:
    # Binance newClientOrderId tối đa 36 ký tự.
    return f"{prefix}_{int(time.time())}_{uuid.uuid4().hex[:8]}"[:36]


def floor_to_step(quantity: float, step: float) -> float:
    if quantity <= 0 or step <= 0:
        return 0.0
    q = Decimal(str(quantity))
    s = Decimal(str(step))
    result = (q / s).to_integral_value(rounding=ROUND_DOWN) * s
    return float(result)


def roi_price(side: str, entry: float, roi_pct: Optional[float], leverage: float, take_profit: bool) -> Optional[float]:
    if roi_pct is None or roi_pct <= 0 or entry <= 0 or leverage <= 0:
        return None
    move = abs(roi_pct) / (100.0 * leverage)
    if side == "BUY":
        return entry * (1.0 + move if take_profit else 1.0 - move)
    return entry * (1.0 - move if take_profit else 1.0 + move)


def normalize_side(position_amt: float) -> Optional[str]:
    if position_amt > 0:
        return "BUY"
    if position_amt < 0:
        return "SELL"
    return None


def reason_code(reason: str) -> str:
    text = (reason or "").upper()
    if text.startswith("TP"):
        return "TP"
    if text.startswith("SL") or "EMERGENCY" in text:
        return "SL"
    if "TRAIL" in text or "PROTECT" in text:
        return "TRAILING_PROFIT"
    if "OPPOSITE" in text:
        return "OPPOSITE_SIGNAL"
    if "MANUAL" in text:
        return "MANUAL"
    return text.replace(" ", "_")[:64] or "UNKNOWN"


# =============================================================================
# CONFIG
# =============================================================================

@dataclass
class BotConfig:
    # Kết nối
    database_url: str = ""
    telegram_bot_token: str = ""
    telegram_chat_id: str = ""
    binance_rest_base: str = "https://fapi.binance.com"
    binance_api_key: str = ""
    binance_api_secret: str = ""
    bot_instance_name: str = "ema-volume-futures-live"
    recv_window_ms: int = 10_000
    request_timeout_sec: int = 15
    dry_run: bool = False   # live trading

    # Tài khoản / rủi ro
    leverage: int = 50
    entry_margin_pct: float = 1.0
    max_positions: int = 3
    max_total_margin_per_symbol_pct: float = 4.0
    max_total_notional_pct: float = 150.0
    margin_type: str = "ISOLATED"
    ensure_one_way_mode: bool = True
    max_daily_loss_pct: float = 0.0  # 0 = tắt

    # TP/SL riêng theo hướng
    long_tp_roi_pct: Optional[float] = 125.0
    long_sl_roi_pct: Optional[float] = 50.0
    short_tp_roi_pct: Optional[float] = 100.0
    short_sl_roi_pct: Optional[float] = 50.0

    # DCA
    enable_dca_long: bool = True
    enable_dca_short: bool = True
    dca_mode: str = "loss"  # loss | profit
    dca_trigger_roi_pct: float = 25.0
    dca_multiplier: float = 1.10
    max_dca_steps: int = 3
    dca_min_seconds_between_adds: int = 20

    # Bảo vệ lợi nhuận
    enable_profit_protect: bool = True
    protect_start_roi_pct: float = 50.0
    protect_pullback_roi_pct: float = 30.0

    # Đảo chiều
    reverse_mode: str = "confirmed"  # none | immediate | confirmed
    reverse_min_score: float = 7.0
    max_reverse_count: int = 1
    reverse_after_close_reasons: Tuple[str, ...] = ("SL", "TRAILING_PROFIT", "OPPOSITE_SIGNAL")

    # Thoát bằng tín hiệu ngược
    enable_exit_on_opposite_signal: bool = False
    opposite_exit_min_score: float = 7.0

    # Cân bằng LONG/SHORT
    enable_side_balance: bool = True
    side_balance_mode: str = "override"  # filter | override
    side_balance_threshold: float = 1.25
    balance_override_min_signal_score: float = 3.0

    # Tín hiệu
    signal_interval: str = "15m"
    ema_fast_period: int = 9
    ema_slow_period: int = 21
    volume_lookback: int = 20
    buy_score_threshold: float = 7.0
    sell_score_threshold: float = 5.0
    buy_min_score_gap: float = 1.0
    sell_min_score_gap: float = 0.4
    buy_volume_ratio: float = 1.50
    sell_volume_ratio: float = 1.10
    buy_min_body_pct: float = 0.15
    sell_min_body_pct: float = 0.08
    buy_close_position_min: float = 0.65
    sell_close_position_max: float = 0.45
    max_signal_candle_range_pct: float = 5.0
    buy_taker_ratio_min: float = 0.55
    sell_taker_ratio_min: float = 0.55
    btc_context_enabled: bool = True
    btc_block_buy_drop_pct: float = 1.0

    # Lọc/scanner
    quote_asset: str = "USDT"
    min_24h_quote_volume: float = 10_000_000.0
    scan_top_n: int = 80
    max_signal_eval_coins: int = 40
    max_abs_24h_change_pct: float = 60.0
    min_abs_24h_change_pct: float = 0.0
    min_coin_price: float = 0.0
    max_coin_price: float = 0.0
    min_24h_trade_count: int = 0
    max_spread_pct: float = 0.25
    excluded_symbols: Tuple[str, ...] = ("BTCUSDT", "ETHUSDT")

    # Cooldown / thời gian vòng lặp
    cooldown_after_close_seconds: int = 60
    blacklist_after_tp_sl_seconds: int = 180
    scan_interval_seconds: int = 20
    manage_interval_seconds: int = 2
    sync_interval_seconds: int = 15
    snapshot_interval_seconds: int = 60
    database_retry_seconds: int = 10
    market_cache_seconds: int = 300
    position_confirm_timeout_seconds: int = 15
    close_confirm_timeout_seconds: int = 20

    # Runtime
    trading_enabled: bool = True
    local_fallback_journal: str = "db_fallback_events.jsonl"

    @classmethod
    def from_env(cls) -> "BotConfig":
        return cls(
            database_url=os.getenv("DATABASE_URL", "").strip(),
            telegram_bot_token=os.getenv("TELEGRAM_BOT_TOKEN", "").strip(),
            telegram_chat_id=os.getenv("TELEGRAM_CHAT_ID", "").strip(),
            binance_rest_base=os.getenv("BINANCE_REST_BASE", "https://fapi.binance.com").rstrip("/"),
            binance_api_key=os.getenv("BINANCE_API_KEY", "").strip(),
            binance_api_secret=os.getenv("BINANCE_API_SECRET", "").strip(),
            bot_instance_name=os.getenv("BOT_INSTANCE_NAME", "ema-volume-futures-live").strip(),
            recv_window_ms=env_int("RECV_WINDOW_MS", 10_000),
            request_timeout_sec=env_int("REQUEST_TIMEOUT_SEC", 15),
            dry_run=False,
            leverage=env_int("LEVERAGE", 50),
            entry_margin_pct=env_float("ENTRY_MARGIN_PCT", 1.0),
            max_positions=env_int("MAX_POSITIONS", 3),
            max_total_margin_per_symbol_pct=env_float("MAX_TOTAL_MARGIN_PER_SYMBOL_PCT", 4.0),
            max_total_notional_pct=env_float("MAX_TOTAL_NOTIONAL_PCT", 150.0),
            margin_type=os.getenv("MARGIN_TYPE", "ISOLATED").upper(),
            ensure_one_way_mode=env_bool("ENSURE_ONE_WAY_MODE", True),
            max_daily_loss_pct=env_float("MAX_DAILY_LOSS_PCT", 0.0),
            long_tp_roi_pct=env_optional_float("LONG_TP_ROI_PCT", 125.0),
            long_sl_roi_pct=env_optional_float("LONG_SL_ROI_PCT", 50.0),
            short_tp_roi_pct=env_optional_float("SHORT_TP_ROI_PCT", 100.0),
            short_sl_roi_pct=env_optional_float("SHORT_SL_ROI_PCT", 50.0),
            enable_dca_long=env_bool("ENABLE_DCA_LONG", True),
            enable_dca_short=env_bool("ENABLE_DCA_SHORT", True),
            dca_mode=os.getenv("DCA_MODE", "loss").lower(),
            dca_trigger_roi_pct=env_float("DCA_TRIGGER_ROI_PCT", 25.0),
            dca_multiplier=env_float("DCA_MULTIPLIER", 1.10),
            max_dca_steps=env_int("MAX_DCA_STEPS", 3),
            dca_min_seconds_between_adds=env_int("DCA_MIN_SECONDS_BETWEEN_ADDS", 20),
            enable_profit_protect=env_bool("ENABLE_PROFIT_PROTECT", True),
            protect_start_roi_pct=env_float("PROTECT_START_ROI_PCT", 50.0),
            protect_pullback_roi_pct=env_float("PROTECT_PULLBACK_ROI_PCT", 30.0),
            reverse_mode=os.getenv("REVERSE_MODE", "confirmed").lower(),
            reverse_min_score=env_float("REVERSE_MIN_SCORE", 7.0),
            max_reverse_count=env_int("MAX_REVERSE_COUNT", 1),
            reverse_after_close_reasons=env_csv(
                "REVERSE_AFTER_CLOSE_REASONS", ("SL", "TRAILING_PROFIT", "OPPOSITE_SIGNAL")
            ),
            enable_exit_on_opposite_signal=env_bool("ENABLE_EXIT_ON_OPPOSITE_SIGNAL", False),
            opposite_exit_min_score=env_float("OPPOSITE_EXIT_MIN_SCORE", 7.0),
            enable_side_balance=env_bool("ENABLE_SIDE_BALANCE", True),
            side_balance_mode=os.getenv("SIDE_BALANCE_MODE", "override").lower(),
            side_balance_threshold=env_float("SIDE_BALANCE_THRESHOLD", 1.25),
            balance_override_min_signal_score=env_float("BALANCE_OVERRIDE_MIN_SIGNAL_SCORE", 3.0),
            signal_interval=os.getenv("SIGNAL_INTERVAL", "15m"),
            ema_fast_period=env_int("EMA_FAST_PERIOD", 9),
            ema_slow_period=env_int("EMA_SLOW_PERIOD", 21),
            volume_lookback=env_int("VOLUME_LOOKBACK", 20),
            buy_score_threshold=env_float("BUY_SCORE_THRESHOLD", 7.0),
            sell_score_threshold=env_float("SELL_SCORE_THRESHOLD", 5.0),
            buy_min_score_gap=env_float("BUY_MIN_SCORE_GAP", 1.0),
            sell_min_score_gap=env_float("SELL_MIN_SCORE_GAP", 0.4),
            buy_volume_ratio=env_float("BUY_VOLUME_RATIO", 1.50),
            sell_volume_ratio=env_float("SELL_VOLUME_RATIO", 1.10),
            buy_min_body_pct=env_float("BUY_MIN_BODY_PCT", 0.15),
            sell_min_body_pct=env_float("SELL_MIN_BODY_PCT", 0.08),
            buy_close_position_min=env_float("BUY_CLOSE_POSITION_MIN", 0.65),
            sell_close_position_max=env_float("SELL_CLOSE_POSITION_MAX", 0.45),
            max_signal_candle_range_pct=env_float("MAX_SIGNAL_CANDLE_RANGE_PCT", 5.0),
            buy_taker_ratio_min=env_float("BUY_TAKER_RATIO_MIN", 0.55),
            sell_taker_ratio_min=env_float("SELL_TAKER_RATIO_MIN", 0.55),
            btc_context_enabled=env_bool("BTC_CONTEXT_ENABLED", True),
            btc_block_buy_drop_pct=env_float("BTC_BLOCK_BUY_DROP_PCT", 1.0),
            quote_asset=os.getenv("QUOTE_ASSET", "USDT").upper(),
            min_24h_quote_volume=env_float("MIN_24H_QUOTE_VOLUME", 10_000_000.0),
            scan_top_n=env_int("SCAN_TOP_N", 80),
            max_signal_eval_coins=env_int("MAX_SIGNAL_EVAL_COINS", 40),
            max_abs_24h_change_pct=env_float("MAX_ABS_24H_CHANGE_PCT", 60.0),
            min_abs_24h_change_pct=env_float("MIN_ABS_24H_CHANGE_PCT", 0.0),
            min_coin_price=env_float("MIN_COIN_PRICE", 0.0),
            max_coin_price=env_float("MAX_COIN_PRICE", 0.0),
            min_24h_trade_count=env_int("MIN_24H_TRADE_COUNT", 0),
            max_spread_pct=env_float("MAX_SPREAD_PCT", 0.25),
            excluded_symbols=env_csv("EXCLUDED_SYMBOLS", ("BTCUSDT", "ETHUSDT")),
            cooldown_after_close_seconds=env_int("COOLDOWN_AFTER_CLOSE_SECONDS", 60),
            blacklist_after_tp_sl_seconds=env_int("BLACKLIST_AFTER_TP_SL_SECONDS", 180),
            scan_interval_seconds=env_int("SCAN_INTERVAL_SECONDS", 20),
            manage_interval_seconds=env_int("MANAGE_INTERVAL_SECONDS", 2),
            sync_interval_seconds=env_int("SYNC_INTERVAL_SECONDS", 15),
            snapshot_interval_seconds=env_int("SNAPSHOT_INTERVAL_SECONDS", 60),
            database_retry_seconds=env_int("DATABASE_RETRY_SECONDS", 10),
            market_cache_seconds=env_int("MARKET_CACHE_SECONDS", 300),
            position_confirm_timeout_seconds=env_int("POSITION_CONFIRM_TIMEOUT_SECONDS", 15),
            close_confirm_timeout_seconds=env_int("CLOSE_CONFIRM_TIMEOUT_SECONDS", 20),
            trading_enabled=env_bool("TRADING_ENABLED", True),
            local_fallback_journal=os.getenv("LOCAL_FALLBACK_JOURNAL", "db_fallback_events.jsonl"),
        )

    def validate(self, require_credentials: bool = True) -> List[str]:
        errors: List[str] = []
        valid_intervals = {"1m", "3m", "5m", "15m", "30m", "1h", "2h", "4h"}
        if not self.database_url:
            errors.append("Thiếu DATABASE_URL")
        if not self.binance_api_key or not self.binance_api_secret:
            errors.append("Thiếu BINANCE_API_KEY hoặc BINANCE_API_SECRET")
        if self.leverage < 1 or self.leverage > 125:
            errors.append("LEVERAGE phải từ 1 đến 125")
        if self.entry_margin_pct <= 0 or self.entry_margin_pct > 100:
            errors.append("ENTRY_MARGIN_PCT phải > 0 và <= 100")
        if self.max_positions < 1:
            errors.append("MAX_POSITIONS phải >= 1")
        if self.ema_fast_period < 2 or self.ema_slow_period <= self.ema_fast_period:
            errors.append("EMA_SLOW_PERIOD phải lớn hơn EMA_FAST_PERIOD >= 2")
        if self.volume_lookback < 2:
            errors.append("VOLUME_LOOKBACK phải >= 2")
        if self.signal_interval not in valid_intervals:
            errors.append(f"SIGNAL_INTERVAL không hợp lệ: {self.signal_interval}")
        if self.dca_mode not in {"loss", "profit"}:
            errors.append("DCA_MODE chỉ nhận loss hoặc profit")
        if self.reverse_mode not in {"none", "immediate", "confirmed"}:
            errors.append("REVERSE_MODE chỉ nhận none, immediate hoặc confirmed")
        if self.side_balance_mode not in {"filter", "override"}:
            errors.append("SIDE_BALANCE_MODE chỉ nhận filter hoặc override")
        if self.margin_type not in {"ISOLATED", "CROSSED"}:
            errors.append("MARGIN_TYPE chỉ nhận ISOLATED hoặc CROSSED")
        if self.dca_multiplier < 1:
            errors.append("DCA_MULTIPLIER phải >= 1")
        if self.max_dca_steps < 0:
            errors.append("MAX_DCA_STEPS phải >= 0")
        return errors

    def update_from_mapping(self, values: Dict[str, Any]) -> None:
        allowed = {f.name: f for f in fields(self)}
        for key, value in values.items():
            if key not in allowed or key in {
                "database_url",
                "telegram_bot_token", "telegram_chat_id",
                "binance_api_key", "binance_api_secret",
            }:
                continue
            current = getattr(self, key)
            try:
                if key.endswith(("_tp_roi_pct", "_sl_roi_pct")) and str(value).strip().lower() in {"none", "null", "off", "false", "0"}:
                    parsed = None
                elif isinstance(current, bool):
                    parsed = str(value).lower() in {"1", "true", "yes", "on"}
                elif isinstance(current, int) and not isinstance(current, bool):
                    parsed = int(float(value))
                elif isinstance(current, float):
                    parsed = float(value)
                elif isinstance(current, tuple):
                    parsed = tuple(str(x).upper() for x in value) if isinstance(value, list) else env_csv("__NONE__", ())
                    if not parsed and isinstance(value, str):
                        parsed = tuple(x.strip().upper() for x in value.split(",") if x.strip())
                elif current is None:
                    parsed = None if str(value).lower() in {"none", "null", "off"} else float(value)
                else:
                    parsed = str(value)
                setattr(self, key, parsed)
            except Exception:
                logger.warning("Bỏ qua cấu hình DB không hợp lệ %s=%r", key, value)

    def public_dict(self) -> Dict[str, Any]:
        data = asdict(self)
        for secret in ("database_url", "telegram_bot_token", "binance_api_key", "binance_api_secret"):
            data.pop(secret, None)
        return data


# =============================================================================
# BINANCE CLIENT (LIVE)
# =============================================================================

class BinanceAPIError(RuntimeError):
    def __init__(self, message: str, status: int = 0, code: Optional[int] = None, payload: Any = None):
        super().__init__(message)
        self.status = status
        self.code = code
        self.payload = payload


class BinanceFuturesClient:
    def __init__(self, config: BotConfig):
        self.config = config
        self.base_url = config.binance_rest_base
        self.api_key = config.binance_api_key
        self.api_secret = config.binance_api_secret
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": "ema-volume-futures-bot/2.0",
            "X-MBX-APIKEY": self.api_key,
        })
        self.time_offset_ms = 0
        self._request_lock = threading.RLock()
        self._last_request_at = 0.0
        self._min_request_interval = 0.05
        self._exchange_info_cache: Optional[Dict[str, Any]] = None
        self._exchange_info_ts = 0.0
        self._symbol_meta: Dict[str, Dict[str, Any]] = {}

    def _rate_limit(self) -> None:
        with self._request_lock:
            delta = time.monotonic() - self._last_request_at
            if delta < self._min_request_interval:
                time.sleep(self._min_request_interval - delta)
            self._last_request_at = time.monotonic()

    def _sign(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """Thêm timestamp, recvWindow và chữ ký HMAC SHA256 vào params."""
        params = params.copy()
        params["timestamp"] = now_ms() + self.time_offset_ms
        params["recvWindow"] = self.config.recv_window_ms
        query = urlencode(sorted(params.items()))
        signature = hmac.new(
            self.api_secret.encode("utf-8"),
            query.encode("utf-8"),
            hashlib.sha256
        ).hexdigest()
        params["signature"] = signature
        return params

    def _decode(self, response: Response) -> Any:
        try:
            return response.json()
        except Exception:
            return {"raw": response.text}

    def request(
        self,
        method: str,
        path: str,
        params: Optional[Dict[str, Any]] = None,
        signed: bool = False,
        retries: int = 3,
    ) -> Any:
        method = method.upper()
        params = dict(params or {})
        headers: Dict[str, str] = {}
        if signed:
            params = self._sign(params)
        else:
            # Public endpoints không cần signature
            params.pop("timestamp", None)
            params.pop("recvWindow", None)

        retry_status = {418, 429, 500, 502, 503, 504}
        last_error: Optional[Exception] = None
        for attempt in range(retries):
            try:
                self._rate_limit()
                kwargs: Dict[str, Any] = {
                    "headers": headers,
                    "timeout": self.config.request_timeout_sec,
                }
                if method in {"GET", "DELETE"}:
                    kwargs["params"] = params
                else:
                    kwargs["data"] = params
                response = self.session.request(method, self.base_url + path, **kwargs)
                payload = self._decode(response)
                if 200 <= response.status_code < 300:
                    return payload
                code = payload.get("code") if isinstance(payload, dict) else None
                msg = payload.get("msg") if isinstance(payload, dict) else str(payload)
                error = BinanceAPIError(
                    f"Binance {method} {path}: HTTP {response.status_code}, code={code}, msg={msg}",
                    status=response.status_code,
                    code=safe_int(code, 0) if code is not None else None,
                    payload=payload,
                )
                if response.status_code in retry_status and attempt < retries - 1:
                    wait = min(8.0, (2 ** attempt) + 0.25)
                    logger.warning("%s; thử lại sau %.2fs", error, wait)
                    time.sleep(wait)
                    continue
                raise error
            except (requests.Timeout, requests.ConnectionError) as exc:
                last_error = exc
                if attempt < retries - 1:
                    time.sleep(min(8.0, 2 ** attempt))
                    continue
                raise BinanceAPIError(f"Lỗi kết nối Binance {method} {path}: {exc}") from exc
        raise BinanceAPIError(f"Không gọi được Binance {method} {path}: {last_error}")

    # ---------- Public endpoints ----------
    def ping(self) -> bool:
        self.request("GET", "/fapi/v1/ping")
        return True

    def sync_time(self) -> int:
        data = self.request("GET", "/fapi/v1/time")
        server_time = safe_int(data.get("serverTime"))
        if server_time <= 0:
            raise BinanceAPIError("Binance không trả serverTime hợp lệ")
        self.time_offset_ms = server_time - now_ms()
        return self.time_offset_ms

    def exchange_info(self, force: bool = False) -> Dict[str, Any]:
        if not force and self._exchange_info_cache and time.time() - self._exchange_info_ts < 3600:
            return self._exchange_info_cache
        data = self.request("GET", "/fapi/v1/exchangeInfo")
        self._exchange_info_cache = data
        self._exchange_info_ts = time.time()
        meta: Dict[str, Dict[str, Any]] = {}
        for item in data.get("symbols", []):
            symbol = item.get("symbol")
            if not symbol:
                continue
            filters = {f.get("filterType"): f for f in item.get("filters", [])}
            lot = filters.get("MARKET_LOT_SIZE") or filters.get("LOT_SIZE") or {}
            notional_filter = filters.get("MIN_NOTIONAL") or filters.get("NOTIONAL") or {}
            price_filter = filters.get("PRICE_FILTER") or {}
            meta[symbol] = {
                "symbol": symbol,
                "status": item.get("status"),
                "contract_type": item.get("contractType"),
                "quote_asset": item.get("quoteAsset"),
                "base_asset": item.get("baseAsset"),
                "step_size": safe_float(lot.get("stepSize"), 0.001),
                "min_qty": safe_float(lot.get("minQty"), 0.001),
                "max_qty": safe_float(lot.get("maxQty"), 1e30),
                "min_notional": safe_float(
                    notional_filter.get("notional", notional_filter.get("minNotional", 5.0)), 5.0
                ),
                "tick_size": safe_float(price_filter.get("tickSize"), 0.00000001),
                "quantity_precision": safe_int(item.get("quantityPrecision"), 8),
                "price_precision": safe_int(item.get("pricePrecision"), 8),
            }
        self._symbol_meta = meta
        return data

    def symbol_meta(self, symbol: str) -> Dict[str, Any]:
        if not self._symbol_meta:
            self.exchange_info()
        if symbol not in self._symbol_meta:
            self.exchange_info(force=True)
        if symbol not in self._symbol_meta:
            raise BinanceAPIError(f"Không tìm thấy metadata symbol {symbol}")
        return self._symbol_meta[symbol]

    def tickers_24h(self) -> List[Dict[str, Any]]:
        return self.request("GET", "/fapi/v1/ticker/24hr")

    def book_tickers(self) -> List[Dict[str, Any]]:
        return self.request("GET", "/fapi/v1/ticker/bookTicker")

    def klines(self, symbol: str, interval: str, limit: int = 100) -> List[List[Any]]:
        return self.request(
            "GET", "/fapi/v1/klines", {"symbol": symbol.upper(), "interval": interval, "limit": limit}
        )

    def mark_price(self, symbol: str) -> float:
        data = self.request("GET", "/fapi/v1/premiumIndex", {"symbol": symbol.upper()})
        return safe_float(data.get("markPrice"))

    # ---------- Private endpoints ----------
    def account_info(self) -> Dict[str, Any]:
        return self.request("GET", "/fapi/v1/account", signed=True)

    def account_balances(self) -> Dict[str, float]:
        info = self.account_info()
        balances = {}
        for asset in info.get("assets", []):
            asset_name = asset.get("asset")
            if asset_name:
                balances[asset_name] = safe_float(asset.get("walletBalance"))
        return balances

    def balance(self, asset: str = "USDT") -> float:
        balances = self.account_balances()
        return balances.get(asset, 0.0)

    def positions(self) -> List[Dict[str, Any]]:
        """Lấy vị thế từ /fapi/v2/positionRisk"""
        return self.request("GET", "/fapi/v2/positionRisk", signed=True)

    def nonzero_positions(self) -> List[Dict[str, Any]]:
        all_positions = self.positions()
        return [p for p in all_positions if abs(safe_float(p.get("positionAmt"))) > 0.0]

    def position(self, symbol: str) -> Optional[Dict[str, Any]]:
        all_positions = self.positions()
        for p in all_positions:
            if p.get("symbol") == symbol.upper():
                return p
        return None

    def position_mode(self) -> Dict[str, Any]:
        return self.request("GET", "/fapi/v1/positionSide/dual", signed=True)

    def ensure_one_way(self) -> None:
        if not self.config.ensure_one_way_mode:
            return
        data = self.position_mode()
        if data.get("dualSidePosition") is True:
            self.request("POST", "/fapi/v1/positionSide/dual", {"dualSidePosition": "false"}, signed=True)
            logger.info("Đã chuyển sang chế độ One-Way")

    def set_margin_type(self, symbol: str, margin_type: str = "ISOLATED") -> None:
        margin_type = margin_type.upper()
        if margin_type not in {"ISOLATED", "CROSSED"}:
            raise ValueError("margin_type phải là ISOLATED hoặc CROSSED")
        try:
            self.request(
                "POST", "/fapi/v1/marginType",
                {"symbol": symbol.upper(), "marginType": margin_type},
                signed=True
            )
        except BinanceAPIError as e:
            # Nếu đã đúng loại, bỏ qua lỗi
            if e.code == -4046:  # "No need to change margin type."
                pass
            else:
                raise

    def set_leverage(self, symbol: str, leverage: int) -> None:
        self.request(
            "POST", "/fapi/v1/leverage",
            {"symbol": symbol.upper(), "leverage": leverage},
            signed=True
        )

    def market_order(self, symbol: str, side: str, quantity: float, reduce_only: bool = False) -> Dict[str, Any]:
        if reduce_only:
            side = side.upper()
            order_type = "MARKET"
            params = {
                "symbol": symbol.upper(),
                "side": side,
                "type": order_type,
                "quantity": self.format_quantity(symbol, quantity),
                "reduceOnly": "true",
            }
        else:
            params = {
                "symbol": symbol.upper(),
                "side": side.upper(),
                "type": "MARKET",
                "quantity": self.format_quantity(symbol, quantity),
            }
        return self.request("POST", "/fapi/v1/order", params, signed=True)

    def query_order(self, symbol: str, order_id: Optional[int] = None, client_order_id: Optional[str] = None) -> Dict[str, Any]:
        params = {"symbol": symbol.upper()}
        if order_id is not None:
            params["orderId"] = order_id
        elif client_order_id is not None:
            params["origClientOrderId"] = client_order_id
        else:
            raise ValueError("Cần orderId hoặc origClientOrderId")
        return self.request("GET", "/fapi/v1/order", params, signed=True)

    def cancel_all_open_orders(self, symbol: str) -> None:
        self.request("DELETE", "/fapi/v1/allOpenOrders", {"symbol": symbol.upper()}, signed=True)

    def user_trades(self, symbol: str, limit: int = 100) -> List[Dict[str, Any]]:
        return self.request(
            "GET", "/fapi/v1/userTrades",
            {"symbol": symbol.upper(), "limit": limit},
            signed=True
        )

    def income_history(self, symbol: Optional[str] = None, limit: int = 100) -> List[Dict[str, Any]]:
        params = {"limit": limit}
        if symbol:
            params["symbol"] = symbol.upper()
        return self.request("GET", "/fapi/v1/income", params, signed=True)

    def format_quantity(self, symbol: str, quantity: float) -> str:
        meta = self.symbol_meta(symbol)
        qty = floor_to_step(quantity, meta["step_size"])
        precision = max(0, safe_int(meta.get("quantity_precision"), 8))
        return f"{qty:.{precision}f}".rstrip("0").rstrip(".") or "0"

    def wait_for_position(self, symbol: str, target_amt: float, timeout_sec: float) -> Optional[Dict[str, Any]]:
        """Chờ đến khi positionAmt khớp với target_amt (hoặc thay đổi) trong timeout."""
        start = time.time()
        while time.time() - start < timeout_sec:
            pos = self.position(symbol)
            if pos and abs(safe_float(pos.get("positionAmt")) - target_amt) < 1e-6:
                return pos
            time.sleep(0.5)
        # Trả về vị thế cuối cùng cho dù chưa khớp
        return self.position(symbol)


# =============================================================================
# DATABASE (POSTGRESQL) - giữ nguyên từ paper
# =============================================================================

class DatabaseUnavailable(RuntimeError):
    pass


class DatabaseManager:
    def __init__(self, config: BotConfig):
        self.config = config
        self.url = config.database_url
        self.available = False
        self.last_error = ""
        self._lock_connection: Optional[PGConnection] = None
        self._lock_key = self._make_lock_key(config.bot_instance_name)
        self._mutex = threading.RLock()
        self.fallback_path = Path(config.local_fallback_journal)

    @staticmethod
    def _make_lock_key(name: str) -> int:
        raw = hashlib.sha256(name.encode("utf-8")).digest()[:8]
        value = int.from_bytes(raw, byteorder="big", signed=False)
        if value >= 2 ** 63:
            value -= 2 ** 64
        return value

    def _connect(self, autocommit: bool = False) -> PGConnection:
        if psycopg2 is None:
            raise DatabaseUnavailable("Chưa cài psycopg2-binary")
        if not self.url:
            raise DatabaseUnavailable("Thiếu DATABASE_URL")
        conn = psycopg2.connect(self.url, connect_timeout=10, application_name=self.config.bot_instance_name)
        conn.autocommit = autocommit
        return conn

    def connect_and_prepare(self) -> None:
        with self._mutex:
            conn = self._connect()
            try:
                with conn.cursor() as cur:
                    cur.execute("SELECT 1")
                conn.commit()
            finally:
                conn.close()
            self.ensure_schema()
            self.available = True
            self.last_error = ""

    def ensure_schema(self) -> None:
        statements = [
            """
            CREATE TABLE IF NOT EXISTS bot_positions (
                id BIGSERIAL PRIMARY KEY,
                instance_name TEXT NOT NULL,
                symbol TEXT NOT NULL,
                side TEXT NOT NULL CHECK (side IN ('BUY','SELL')),
                status TEXT NOT NULL,
                leverage INTEGER NOT NULL,
                margin_type TEXT NOT NULL DEFAULT 'ISOLATED',
                initial_quantity NUMERIC NOT NULL DEFAULT 0,
                current_quantity NUMERIC NOT NULL DEFAULT 0,
                initial_entry_price NUMERIC NOT NULL DEFAULT 0,
                average_entry_price NUMERIC NOT NULL DEFAULT 0,
                exit_price NUMERIC,
                initial_margin NUMERIC NOT NULL DEFAULT 0,
                current_margin NUMERIC NOT NULL DEFAULT 0,
                initial_notional NUMERIC NOT NULL DEFAULT 0,
                current_notional NUMERIC NOT NULL DEFAULT 0,
                tp_roi_pct NUMERIC,
                sl_roi_pct NUMERIC,
                tp_price NUMERIC,
                sl_price NUMERIC,
                dca_mode TEXT,
                dca_multiplier NUMERIC NOT NULL DEFAULT 1,
                dca_count INTEGER NOT NULL DEFAULT 0,
                max_dca_steps INTEGER NOT NULL DEFAULT 0,
                reverse_count INTEGER NOT NULL DEFAULT 0,
                max_reverse_count INTEGER NOT NULL DEFAULT 0,
                best_roi_pct NUMERIC,
                worst_roi_pct NUMERIC,
                last_roi_pct NUMERIC,
                unrealized_pnl NUMERIC NOT NULL DEFAULT 0,
                realized_pnl NUMERIC NOT NULL DEFAULT 0,
                commission NUMERIC NOT NULL DEFAULT 0,
                funding_fee NUMERIC NOT NULL DEFAULT 0,
                net_pnl NUMERIC NOT NULL DEFAULT 0,
                entry_reason TEXT,
                close_reason TEXT,
                signal_score NUMERIC,
                balance_reason TEXT,
                open_order_id TEXT,
                close_order_id TEXT,
                opened_at TIMESTAMPTZ,
                last_added_at TIMESTAMPTZ,
                closed_at TIMESTAMPTZ,
                last_synced_at TIMESTAMPTZ,
                binance_position_json JSONB,
                binance_open_order_json JSONB,
                binance_close_order_json JSONB,
                metadata_incomplete BOOLEAN NOT NULL DEFAULT FALSE,
                is_simulated BOOLEAN NOT NULL DEFAULT FALSE,
                created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
                updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )
            """,
            """
            CREATE TABLE IF NOT EXISTS bot_position_events (
                id BIGSERIAL PRIMARY KEY,
                position_id BIGINT REFERENCES bot_positions(id) ON DELETE SET NULL,
                instance_name TEXT NOT NULL,
                symbol TEXT NOT NULL,
                event_type TEXT NOT NULL,
                side TEXT,
                quantity NUMERIC,
                price NUMERIC,
                margin NUMERIC,
                notional NUMERIC,
                roi_pct NUMERIC,
                pnl NUMERIC,
                commission NUMERIC,
                funding_fee NUMERIC,
                dca_step INTEGER,
                reason TEXT,
                order_id TEXT,
                raw_json JSONB,
                created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )
            """,
            """
            CREATE TABLE IF NOT EXISTS bot_equity_snapshots (
                id BIGSERIAL PRIMARY KEY,
                instance_name TEXT NOT NULL,
                wallet_balance NUMERIC NOT NULL DEFAULT 0,
                available_balance NUMERIC NOT NULL DEFAULT 0,
                unrealized_pnl NUMERIC NOT NULL DEFAULT 0,
                long_notional NUMERIC NOT NULL DEFAULT 0,
                short_notional NUMERIC NOT NULL DEFAULT 0,
                total_notional NUMERIC NOT NULL DEFAULT 0,
                long_positions INTEGER NOT NULL DEFAULT 0,
                short_positions INTEGER NOT NULL DEFAULT 0,
                total_positions INTEGER NOT NULL DEFAULT 0,
                created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )
            """,
            """
            CREATE TABLE IF NOT EXISTS bot_runtime_state (
                instance_name TEXT NOT NULL,
                key TEXT NOT NULL,
                value_json JSONB NOT NULL,
                updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
                PRIMARY KEY (instance_name, key)
            )
            """,
            """
            CREATE UNIQUE INDEX IF NOT EXISTS uq_bot_open_symbol
            ON bot_positions(instance_name, symbol)
            WHERE status IN ('PENDING_OPEN','ACTIVE','PENDING_CLOSE','RECOVERED')
            """,
            "CREATE INDEX IF NOT EXISTS ix_bot_positions_status ON bot_positions(instance_name,status)",
            "CREATE INDEX IF NOT EXISTS ix_bot_positions_closed_at ON bot_positions(instance_name,closed_at)",
            "CREATE INDEX IF NOT EXISTS ix_bot_events_position ON bot_position_events(position_id,created_at)",
            "CREATE INDEX IF NOT EXISTS ix_bot_events_symbol ON bot_position_events(instance_name,symbol,created_at)",
        ]
        conn = self._connect()
        try:
            with conn.cursor() as cur:
                for sql in statements:
                    cur.execute(sql)
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            conn.close()

    def acquire_instance_lock(self) -> bool:
        if self._lock_connection is not None and not self._lock_connection.closed:
            return True
        conn = self._connect(autocommit=True)
        with conn.cursor() as cur:
            cur.execute("SELECT pg_try_advisory_lock(%s)", (self._lock_key,))
            acquired = bool(cur.fetchone()[0])
        if acquired:
            self._lock_connection = conn
            return True
        conn.close()
        return False

    def release_instance_lock(self) -> None:
        conn = self._lock_connection
        self._lock_connection = None
        if conn is None:
            return
        try:
            with conn.cursor() as cur:
                cur.execute("SELECT pg_advisory_unlock(%s)", (self._lock_key,))
        except Exception:
            pass
        finally:
            try:
                conn.close()
            except Exception:
                pass

    def ping(self) -> bool:
        try:
            conn = self._connect()
            try:
                with conn.cursor() as cur:
                    cur.execute("SELECT 1")
                    cur.fetchone()
                conn.commit()
            finally:
                conn.close()
            self.available = True
            self.last_error = ""
            return True
        except Exception as exc:
            self.available = False
            self.last_error = str(exc)
            return False

    def _run(
        self,
        sql: str,
        params: Sequence[Any] = (),
        fetch: str = "none",
        required: bool = True,
    ) -> Any:
        try:
            conn = self._connect()
            try:
                with conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
                    cur.execute(sql, params)
                    if fetch == "one":
                        result = cur.fetchone()
                    elif fetch == "all":
                        result = cur.fetchall()
                    else:
                        result = None
                conn.commit()
                self.available = True
                self.last_error = ""
                return result
            except Exception:
                conn.rollback()
                raise
            finally:
                conn.close()
        except Exception as exc:
            self.available = False
            self.last_error = str(exc)
            if required:
                raise DatabaseUnavailable(str(exc)) from exc
            logger.error("Database lỗi: %s", exc)
            return None

    @staticmethod
    def _json_param(value: Any) -> Any:
        if psycopg2 is None:
            return value
        return psycopg2.extras.Json(value, dumps=lambda obj: json.dumps(obj, ensure_ascii=False, default=str))

    def journal(self, event: Dict[str, Any]) -> None:
        record = {"recorded_at": utc_now().isoformat(), **event}
        try:
            self.fallback_path.parent.mkdir(parents=True, exist_ok=True)
            with self.fallback_path.open("a", encoding="utf-8") as handle:
                handle.write(json_text(record) + "\n")
        except Exception as exc:
            logger.error("Không ghi được fallback journal: %s", exc)

    def set_runtime(self, key: str, value: Any, required: bool = False) -> None:
        self._run(
            """
            INSERT INTO bot_runtime_state(instance_name,key,value_json,updated_at)
            VALUES (%s,%s,%s,NOW())
            ON CONFLICT(instance_name,key)
            DO UPDATE SET value_json=EXCLUDED.value_json, updated_at=NOW()
            """,
            (self.config.bot_instance_name, key, self._json_param(value)),
            required=required,
        )

    def get_runtime(self, key: str, default: Any = None) -> Any:
        row = self._run(
            "SELECT value_json FROM bot_runtime_state WHERE instance_name=%s AND key=%s",
            (self.config.bot_instance_name, key), fetch="one", required=False,
        )
        return default if not row else row.get("value_json", default)

    def create_pending_position(self, data: Dict[str, Any]) -> int:
        row = self._run(
            """
            INSERT INTO bot_positions(
                instance_name,symbol,side,status,leverage,margin_type,
                initial_quantity,current_quantity,initial_entry_price,average_entry_price,
                initial_margin,current_margin,initial_notional,current_notional,
                tp_roi_pct,sl_roi_pct,tp_price,sl_price,
                dca_mode,dca_multiplier,dca_count,max_dca_steps,
                reverse_count,max_reverse_count,best_roi_pct,worst_roi_pct,last_roi_pct,
                entry_reason,signal_score,balance_reason,open_order_id,
                opened_at,last_synced_at,binance_open_order_json,metadata_incomplete,is_simulated
            ) VALUES (
                %s,%s,%s,'PENDING_OPEN',%s,%s,
                %s,%s,%s,%s,%s,%s,%s,%s,
                %s,%s,%s,%s,%s,%s,%s,%s,
                %s,%s,%s,%s,%s,%s,%s,%s,%s,
                %s,NOW(),%s,%s,%s
            ) RETURNING id
            """,
            (
                self.config.bot_instance_name, data["symbol"], data["side"], data["leverage"], data["margin_type"],
                data.get("initial_quantity", 0), data.get("current_quantity", 0),
                data.get("initial_entry_price", 0), data.get("average_entry_price", 0),
                data.get("initial_margin", 0), data.get("current_margin", 0),
                data.get("initial_notional", 0), data.get("current_notional", 0),
                data.get("tp_roi_pct"), data.get("sl_roi_pct"), data.get("tp_price"), data.get("sl_price"),
                data.get("dca_mode"), data.get("dca_multiplier", 1), data.get("dca_count", 0),
                data.get("max_dca_steps", 0), data.get("reverse_count", 0), data.get("max_reverse_count", 0),
                data.get("best_roi_pct"), data.get("worst_roi_pct"), data.get("last_roi_pct"),
                data.get("entry_reason"), data.get("signal_score"), data.get("balance_reason"),
                data.get("open_order_id"), data.get("last_synced_at"),
                self._json_param(data.get("binance_open_order_json")),
                bool(data.get("metadata_incomplete", False)), bool(data.get("is_simulated", False)),
            ),
            fetch="one",
        )
        return int(row["id"])

    def confirm_open(self, position_id: int, data: Dict[str, Any], recovered: bool = False) -> None:
        status = "RECOVERED" if recovered else "ACTIVE"
        self._run(
            """
            UPDATE bot_positions SET
                status=%s,
                initial_quantity=CASE WHEN initial_quantity=0 THEN %s ELSE initial_quantity END,
                current_quantity=%s,
                initial_entry_price=CASE WHEN initial_entry_price=0 THEN %s ELSE initial_entry_price END,
                average_entry_price=%s,
                initial_margin=CASE WHEN initial_margin=0 THEN %s ELSE initial_margin END,
                current_margin=%s,
                initial_notional=CASE WHEN initial_notional=0 THEN %s ELSE initial_notional END,
                current_notional=%s,
                tp_price=%s,sl_price=%s,open_order_id=COALESCE(%s,open_order_id),
                opened_at=COALESCE(opened_at,NOW()),last_synced_at=NOW(),
                binance_position_json=%s,binance_open_order_json=COALESCE(%s,binance_open_order_json),
                updated_at=NOW()
            WHERE id=%s
            """,
            (
                status, data["quantity"], data["quantity"], data["entry_price"], data["entry_price"],
                data["margin"], data["margin"], data["notional"], data["notional"],
                data.get("tp_price"), data.get("sl_price"), data.get("open_order_id"),
                self._json_param(data.get("position_json")), self._json_param(data.get("order_json")), position_id,
            ),
        )

    def active_positions(self) -> List[Dict[str, Any]]:
        rows = self._run(
            """
            SELECT * FROM bot_positions
            WHERE instance_name=%s AND status IN ('PENDING_OPEN','ACTIVE','PENDING_CLOSE','RECOVERED')
            ORDER BY opened_at NULLS LAST,id
            """,
            (self.config.bot_instance_name,), fetch="all", required=False,
        )
        return list(rows or [])

    def active_position(self, symbol: str) -> Optional[Dict[str, Any]]:
        return self._run(
            """
            SELECT * FROM bot_positions
            WHERE instance_name=%s AND symbol=%s
              AND status IN ('PENDING_OPEN','ACTIVE','PENDING_CLOSE','RECOVERED')
            ORDER BY id DESC LIMIT 1
            """,
            (self.config.bot_instance_name, symbol.upper()), fetch="one", required=False,
        )

    def update_position_live(self, position_id: int, data: Dict[str, Any]) -> None:
        self._run(
            """
            UPDATE bot_positions SET
                side=%s,current_quantity=%s,average_entry_price=%s,current_margin=%s,current_notional=%s,
                best_roi_pct=%s,worst_roi_pct=%s,last_roi_pct=%s,unrealized_pnl=%s,
                last_synced_at=NOW(),binance_position_json=%s,updated_at=NOW()
            WHERE id=%s
            """,
            (
                data["side"], data["quantity"], data["entry_price"], data["margin"], data["notional"],
                data.get("best_roi_pct"), data.get("worst_roi_pct"), data.get("last_roi_pct"),
                data.get("unrealized_pnl", 0), self._json_param(data.get("position_json")), position_id,
            ),
            required=False,
        )

    def confirm_dca(self, position_id: int, data: Dict[str, Any]) -> None:
        self._run(
            """
            UPDATE bot_positions SET
                current_quantity=%s,average_entry_price=%s,current_margin=%s,current_notional=%s,
                dca_count=%s,last_added_at=NOW(),last_synced_at=NOW(),
                tp_price=%s,sl_price=%s,binance_position_json=%s,updated_at=NOW()
            WHERE id=%s
            """,
            (
                data["quantity"], data["entry_price"], data["margin"], data["notional"], data["dca_count"],
                data.get("tp_price"), data.get("sl_price"), self._json_param(data.get("position_json")), position_id,
            ),
        )

    def mark_pending_close(self, position_id: int, reason: str, order_id: Optional[str] = None) -> None:
        self._run(
            """
            UPDATE bot_positions SET status='PENDING_CLOSE',close_reason=%s,
                close_order_id=COALESCE(%s,close_order_id),updated_at=NOW()
            WHERE id=%s
            """,
            (reason, order_id, position_id),
            required=False,
        )

    def close_position(self, position_id: int, data: Dict[str, Any]) -> None:
        self._run(
            """
            UPDATE bot_positions SET
                status='CLOSED',exit_price=%s,current_quantity=0,current_notional=0,
                realized_pnl=%s,commission=%s,funding_fee=%s,net_pnl=%s,
                close_reason=%s,close_order_id=COALESCE(%s,close_order_id),
                closed_at=NOW(),last_synced_at=NOW(),
                binance_close_order_json=%s,updated_at=NOW()
            WHERE id=%s
            """,
            (
                data.get("exit_price"), data.get("realized_pnl", 0), data.get("commission", 0),
                data.get("funding_fee", 0), data.get("net_pnl", 0), data.get("close_reason"),
                data.get("close_order_id"), self._json_param(data.get("close_order_json")), position_id,
            ),
        )

    def mark_error(self, position_id: int, reason: str, raw: Any = None) -> None:
        self._run(
            """
            UPDATE bot_positions SET status='ERROR',close_reason=%s,
                binance_close_order_json=%s,updated_at=NOW() WHERE id=%s
            """,
            (reason, self._json_param(raw), position_id), required=False,
        )

    def create_recovered_position(self, pos: Dict[str, Any], config: BotConfig) -> int:
        amt = safe_float(pos.get("positionAmt"))
        side = normalize_side(amt)
        if side is None:
            raise ValueError("Không thể recover vị thế quantity=0")
        entry = safe_float(pos.get("entryPrice"))
        qty = abs(amt)
        leverage = safe_int(pos.get("leverage"), config.leverage)
        notional = qty * entry
        margin = notional / max(leverage, 1)
        tp = config.long_tp_roi_pct if side == "BUY" else config.short_tp_roi_pct
        sl = config.long_sl_roi_pct if side == "BUY" else config.short_sl_roi_pct
        data = {
            "symbol": pos["symbol"], "side": side, "leverage": leverage,
            "margin_type": str(pos.get("marginType", config.margin_type)).upper(),
            "initial_quantity": qty, "current_quantity": qty,
            "initial_entry_price": entry, "average_entry_price": entry,
            "initial_margin": margin, "current_margin": margin,
            "initial_notional": notional, "current_notional": notional,
            "tp_roi_pct": tp, "sl_roi_pct": sl,
            "tp_price": roi_price(side, entry, tp, leverage, True),
            "sl_price": roi_price(side, entry, sl, leverage, False),
            "dca_mode": config.dca_mode, "dca_multiplier": config.dca_multiplier,
            "dca_count": 0, "max_dca_steps": config.max_dca_steps,
            "reverse_count": 0, "max_reverse_count": config.max_reverse_count,
            "entry_reason": "RECOVERED_FROM_BINANCE", "metadata_incomplete": True,
            "last_synced_at": utc_now(), "is_simulated": False,
        }
        position_id = self.create_pending_position(data)
        self.confirm_open(position_id, {
            "quantity": qty, "entry_price": entry, "margin": margin, "notional": notional,
            "tp_price": data["tp_price"], "sl_price": data["sl_price"],
            "position_json": pos, "order_json": None, "open_order_id": None,
        }, recovered=True)
        return position_id

    def add_event(
        self,
        event_type: str,
        symbol: str,
        position_id: Optional[int] = None,
        side: Optional[str] = None,
        quantity: Optional[float] = None,
        price: Optional[float] = None,
        margin: Optional[float] = None,
        notional: Optional[float] = None,
        roi_pct: Optional[float] = None,
        pnl: Optional[float] = None,
        commission: Optional[float] = None,
        funding_fee: Optional[float] = None,
        dca_step: Optional[int] = None,
        reason: Optional[str] = None,
        order_id: Optional[str] = None,
        raw: Any = None,
        required: bool = False,
    ) -> None:
        payload = {
            "position_id": position_id, "instance_name": self.config.bot_instance_name,
            "symbol": symbol.upper(), "event_type": event_type, "side": side,
            "quantity": quantity, "price": price, "margin": margin, "notional": notional,
            "roi_pct": roi_pct, "pnl": pnl, "commission": commission,
            "funding_fee": funding_fee, "dca_step": dca_step, "reason": reason,
            "order_id": order_id, "raw_json": raw,
        }
        try:
            self._run(
                """
                INSERT INTO bot_position_events(
                    position_id,instance_name,symbol,event_type,side,quantity,price,margin,notional,
                    roi_pct,pnl,commission,funding_fee,dca_step,reason,order_id,raw_json
                ) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
                """,
                (
                    position_id, self.config.bot_instance_name, symbol.upper(), event_type, side,
                    quantity, price, margin, notional, roi_pct, pnl, commission, funding_fee,
                    dca_step, reason, order_id, self._json_param(raw),
                ),
                required=required,
            )
        except DatabaseUnavailable:
            self.journal(payload)
            if required:
                raise

    def save_snapshot(self, data: Dict[str, Any]) -> None:
        self._run(
            """
            INSERT INTO bot_equity_snapshots(
                instance_name,wallet_balance,available_balance,unrealized_pnl,
                long_notional,short_notional,total_notional,long_positions,short_positions,total_positions
            ) VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
            """,
            (
                self.config.bot_instance_name, data.get("wallet_balance", 0), data.get("available_balance", 0),
                data.get("unrealized_pnl", 0), data.get("long_notional", 0), data.get("short_notional", 0),
                data.get("total_notional", 0), data.get("long_positions", 0), data.get("short_positions", 0),
                data.get("total_positions", 0),
            ),
            required=False,
        )

    def closed_positions(self, limit: int = 5000) -> List[Dict[str, Any]]:
        rows = self._run(
            """
            SELECT * FROM bot_positions
            WHERE instance_name=%s AND status='CLOSED'
            ORDER BY closed_at ASC NULLS LAST,id ASC LIMIT %s
            """,
            (self.config.bot_instance_name, limit), fetch="all", required=False,
        )
        return list(rows or [])


# =============================================================================
# SIGNAL ENGINE — EMA + VOLUME, KHÔNG RSI (giữ nguyên từ paper)
# =============================================================================

@dataclass
class Candle:
    open_time: int
    open: float
    high: float
    low: float
    close: float
    volume: float
    close_time: int
    quote_volume: float
    trades: int
    taker_buy_base: float
    taker_buy_quote: float

    @classmethod
    def from_kline(cls, row: Sequence[Any]) -> "Candle":
        return cls(
            open_time=safe_int(row[0]),
            open=safe_float(row[1]),
            high=safe_float(row[2]),
            low=safe_float(row[3]),
            close=safe_float(row[4]),
            volume=safe_float(row[5]),
            close_time=safe_int(row[6]),
            quote_volume=safe_float(row[7]),
            trades=safe_int(row[8]),
            taker_buy_base=safe_float(row[9]),
            taker_buy_quote=safe_float(row[10]),
        )

    @property
    def range_value(self) -> float:
        return max(0.0, self.high - self.low)

    @property
    def range_pct(self) -> float:
        return 0.0 if self.open <= 0 else self.range_value / self.open * 100.0

    @property
    def body_pct(self) -> float:
        return 0.0 if self.open <= 0 else abs(self.close - self.open) / self.open * 100.0

    @property
    def close_position(self) -> float:
        return 0.5 if self.range_value <= 0 else (self.close - self.low) / self.range_value

    @property
    def taker_buy_ratio(self) -> float:
        return 0.5 if self.quote_volume <= 0 else max(0.0, min(1.0, self.taker_buy_quote / self.quote_volume))


@dataclass
class SignalDecision:
    symbol: str
    side: Optional[str]
    selected_score: float
    buy_score: float
    sell_score: float
    candle_open_time: int
    candle_close_time: int
    reason: str
    components: Dict[str, Any]
    is_spike: bool = False
    balance_reason: str = ""

    def score_for(self, side: str) -> float:
        return self.buy_score if side == "BUY" else self.sell_score


class SignalEngine:
    def __init__(self, config: BotConfig, client: BinanceFuturesClient):
        self.config = config
        self.client = client
        self._btc_context: Dict[str, Any] = {"ts": 0.0, "bearish": False, "bullish": False, "return_pct": 0.0}

    @staticmethod
    def ema(values: Sequence[float], period: int) -> float:
        clean = [float(v) for v in values if v > 0]
        if not clean:
            return 0.0
        period = max(2, int(period))
        seed_count = min(period, len(clean))
        result = sum(clean[:seed_count]) / seed_count
        alpha = 2.0 / (period + 1.0)
        for value in clean[seed_count:]:
            result = alpha * value + (1 - alpha) * result
        return result

    def closed_candles(self, symbol: str) -> List[Candle]:
        needed = max(self.config.ema_slow_period + 8, self.config.volume_lookback + 8, 40)
        rows = self.client.klines(symbol, self.config.signal_interval, limit=min(500, needed + 5))
        current_server_ms = now_ms() + self.client.time_offset_ms
        candles = [Candle.from_kline(row) for row in rows]
        closed = [c for c in candles if c.close_time < current_server_ms]
        return closed[-needed:]

    def btc_context(self, force: bool = False) -> Dict[str, Any]:
        if not self.config.btc_context_enabled:
            return {"bearish": False, "bullish": False, "return_pct": 0.0}
        if not force and time.time() - safe_float(self._btc_context.get("ts")) < 15:
            return self._btc_context
        try:
            candles = self.closed_candles("BTCUSDT")
            closes = [c.close for c in candles]
            if len(closes) < 3:
                return self._btc_context
            fast = self.ema(closes, self.config.ema_fast_period)
            slow = self.ema(closes, self.config.ema_slow_period)
            last = candles[-1]
            ret = (last.close - last.open) / last.open * 100.0 if last.open > 0 else 0.0
            self._btc_context = {
                "ts": time.time(),
                "bearish": fast < slow and last.close < fast,
                "bullish": fast > slow and last.close > fast,
                "return_pct": ret,
            }
        except Exception as exc:
            logger.warning("Không lấy được BTC context: %s", exc)
        return self._btc_context

    def evaluate(self, symbol: str) -> SignalDecision:
        candles = self.closed_candles(symbol)
        minimum = max(5, min(self.config.ema_fast_period, 5), self.config.volume_lookback + 1)
        if len(candles) < minimum:
            return SignalDecision(symbol, None, 0, 0, 0, 0, 0, "Không đủ nến đóng", {})

        current = candles[-1]
        previous = candles[-2]
        history = candles[:-1]
        closes = [c.close for c in history]
        ema_fast = self.ema(closes + [current.close], self.config.ema_fast_period)
        ema_slow = self.ema(closes + [current.close], self.config.ema_slow_period)
        ema_fast_prev = self.ema(closes, self.config.ema_fast_period)

        volumes = [c.quote_volume for c in history[-self.config.volume_lookback:] if c.quote_volume > 0]
        avg_volume = sum(volumes) / len(volumes) if volumes else 0.0
        volume_ratio = current.quote_volume / avg_volume if avg_volume > 0 else 0.0
        taker_buy_ratio = current.taker_buy_ratio
        taker_sell_ratio = 1.0 - taker_buy_ratio
        spike = current.range_pct > self.config.max_signal_candle_range_pct

        buy_score = 0.0
        sell_score = 0.0
        buy_parts: List[str] = []
        sell_parts: List[str] = []

        if current.close > ema_fast:
            buy_score += 1.5
            buy_parts.append("close>EMAfast +1.5")
        if ema_fast > ema_slow and ema_fast >= ema_fast_prev:
            buy_score += 2.0
            buy_parts.append("EMA tăng +2.0")
        if current.close > previous.high:
            buy_score += 1.5
            buy_parts.append("phá đỉnh +1.5")
        if current.close > current.open and current.body_pct >= self.config.buy_min_body_pct:
            buy_score += 1.0
            buy_parts.append("thân BUY +1.0")
        if volume_ratio >= self.config.buy_volume_ratio:
            buy_score += 2.0
            buy_parts.append("volume BUY +2.0")
        if current.close_position >= self.config.buy_close_position_min:
            buy_score += 1.0
            buy_parts.append("đóng gần đỉnh +1.0")
        if taker_buy_ratio >= self.config.buy_taker_ratio_min:
            buy_score += 0.75
            buy_parts.append("taker BUY +0.75")

        if current.close < ema_fast:
            sell_score += 1.5
            sell_parts.append("close<EMAfast +1.5")
        if ema_fast < ema_slow and ema_fast <= ema_fast_prev:
            sell_score += 1.5
            sell_parts.append("EMA giảm +1.5")
        if current.close < previous.low:
            sell_score += 1.5
            sell_parts.append("phá đáy +1.5")
        if current.close < current.open and current.body_pct >= self.config.sell_min_body_pct:
            sell_score += 1.0
            sell_parts.append("thân SELL +1.0")
        if volume_ratio >= self.config.sell_volume_ratio:
            sell_score += 1.5
            sell_parts.append("volume SELL +1.5")
        if current.close_position <= self.config.sell_close_position_max:
            sell_score += 1.0
            sell_parts.append("đóng gần đáy +1.0")
        if taker_sell_ratio >= self.config.sell_taker_ratio_min:
            sell_score += 0.75
            sell_parts.append("taker SELL +0.75")

        btc = self.btc_context()
        btc_buy_blocked = (
            self.config.btc_context_enabled
            and safe_float(btc.get("return_pct")) <= -abs(self.config.btc_block_buy_drop_pct)
        )
        if btc.get("bearish"):
            sell_score += 0.5
            sell_parts.append("BTC yếu +0.5")
        elif btc.get("bullish"):
            buy_score += 0.5
            buy_parts.append("BTC hỗ trợ +0.5")

        side: Optional[str] = None
        reason = "Không đạt ngưỡng"
        if spike:
            reason = f"Chặn spike: range {current.range_pct:.2f}% > {self.config.max_signal_candle_range_pct:.2f}%"
        else:
            buy_ok = buy_score >= self.config.buy_score_threshold and not btc_buy_blocked
            sell_ok = sell_score >= self.config.sell_score_threshold
            if buy_ok and buy_score - sell_score >= self.config.buy_min_score_gap:
                side = "BUY"
                reason = "; ".join(buy_parts)
            if sell_ok and sell_score - buy_score >= self.config.sell_min_score_gap:
                if side is None or sell_score > buy_score:
                    side = "SELL"
                    reason = "; ".join(sell_parts)
            if buy_ok and sell_ok and abs(buy_score - sell_score) < min(
                self.config.buy_min_score_gap, self.config.sell_min_score_gap
            ):
                side = None
                reason = "BUY/SELL quá gần nhau, chờ nến tiếp theo"
            if btc_buy_blocked and buy_score >= self.config.buy_score_threshold:
                reason = f"BUY bị chặn do BTC giảm {safe_float(btc.get('return_pct')):.2f}%"

        selected_score = buy_score if side == "BUY" else sell_score if side == "SELL" else max(buy_score, sell_score)
        components = {
            "ema_fast": ema_fast,
            "ema_slow": ema_slow,
            "volume_ratio": volume_ratio,
            "body_pct": current.body_pct,
            "range_pct": current.range_pct,
            "close_position": current.close_position,
            "taker_buy_ratio": taker_buy_ratio,
            "taker_sell_ratio": taker_sell_ratio,
            "buy_parts": buy_parts,
            "sell_parts": sell_parts,
            "btc": btc,
            "close": current.close,
        }
        return SignalDecision(
            symbol=symbol,
            side=side,
            selected_score=selected_score,
            buy_score=buy_score,
            sell_score=sell_score,
            candle_open_time=current.open_time,
            candle_close_time=current.close_time,
            reason=reason,
            components=components,
            is_spike=spike,
        )


# =============================================================================
# EXPOSURE / SIDE BALANCE (giữ nguyên)
# =============================================================================

@dataclass
class Exposure:
    long_notional: float = 0.0
    short_notional: float = 0.0
    long_positions: int = 0
    short_positions: int = 0

    @property
    def total_notional(self) -> float:
        return self.long_notional + self.short_notional

    @property
    def total_positions(self) -> int:
        return self.long_positions + self.short_positions


class BalanceManager:
    def __init__(self, config: BotConfig):
        self.config = config

    @staticmethod
    def exposure_from_positions(positions: Sequence[Dict[str, Any]]) -> Exposure:
        result = Exposure()
        for pos in positions:
            amt = safe_float(pos.get("positionAmt", pos.get("current_quantity")))
            if "current_quantity" in pos:
                side = pos.get("side")
                qty = abs(safe_float(pos.get("current_quantity")))
                price = safe_float(pos.get("average_entry_price"))
            else:
                side = normalize_side(amt)
                qty = abs(amt)
                price = safe_float(pos.get("markPrice"), safe_float(pos.get("entryPrice")))
            notional = qty * price
            if side == "BUY":
                result.long_notional += notional
                result.long_positions += 1
            elif side == "SELL":
                result.short_notional += notional
                result.short_positions += 1
        return result

    def preferred_side(self, exposure: Exposure) -> Optional[str]:
        if not self.config.enable_side_balance:
            return None
        long_n = exposure.long_notional
        short_n = exposure.short_notional
        threshold = max(1.0, self.config.side_balance_threshold)
        if long_n <= 0 and short_n <= 0:
            return None
        if short_n <= 0 and long_n > 0:
            return "SELL"
        if long_n <= 0 and short_n > 0:
            return "BUY"
        if long_n / short_n > threshold:
            return "SELL"
        if short_n / long_n > threshold:
            return "BUY"
        return None

    def apply(self, decision: SignalDecision, exposure: Exposure) -> SignalDecision:
        preferred = self.preferred_side(exposure)
        if not preferred:
            return decision
        reason = (
            f"Cân bằng: LONG={exposure.long_notional:.2f}, "
            f"SHORT={exposure.short_notional:.2f}, ưu tiên {preferred}"
        )
        if self.config.side_balance_mode == "filter":
            if decision.side != preferred:
                decision.side = None
                decision.selected_score = decision.score_for(preferred)
                decision.reason = reason + "; tín hiệu hiện tại bị lọc"
                decision.balance_reason = reason
            return decision

        # override: chỉ đổi hướng nếu hướng cần cân bằng vẫn có điểm tối thiểu.
        preferred_score = decision.score_for(preferred)
        if preferred_score >= self.config.balance_override_min_signal_score:
            decision.side = preferred
            decision.selected_score = preferred_score
            decision.reason = reason + f"; override score={preferred_score:.2f}"
            decision.balance_reason = reason
        elif decision.side != preferred:
            decision.side = None
            decision.selected_score = preferred_score
            decision.reason = reason + "; score override chưa đủ"
            decision.balance_reason = reason
        return decision


# =============================================================================
# MARKET SCANNER (giữ nguyên)
# =============================================================================

class MarketScanner:
    def __init__(
        self,
        config: BotConfig,
        client: BinanceFuturesClient,
        signal_engine: SignalEngine,
        balance_manager: BalanceManager,
        database: DatabaseManager,
    ):
        self.config = config
        self.client = client
        self.signal_engine = signal_engine
        self.balance_manager = balance_manager
        self.database = database
        self._market_cache: List[Dict[str, Any]] = []
        self._market_cache_ts = 0.0

    @staticmethod
    def spread_pct(book: Dict[str, Any]) -> float:
        bid = safe_float(book.get("bidPrice"))
        ask = safe_float(book.get("askPrice"))
        mid = (bid + ask) / 2.0
        return 999.0 if bid <= 0 or ask <= 0 or mid <= 0 else (ask - bid) / mid * 100.0

    def _runtime_until(self, prefix: str, symbol: str) -> float:
        value = self.database.get_runtime(f"{prefix}:{symbol}", 0)
        if isinstance(value, dict):
            value = value.get("until", 0)
        return safe_float(value)

    def is_blocked(self, symbol: str) -> bool:
        now = time.time()
        return now < self._runtime_until("cooldown_until", symbol) or now < self._runtime_until("blacklist_until", symbol)

    def market_universe(self, force: bool = False) -> List[Dict[str, Any]]:
        if not force and self._market_cache and time.time() - self._market_cache_ts < self.config.market_cache_seconds:
            return list(self._market_cache)

        self.client.exchange_info()
        tickers = self.client.tickers_24h()
        books = {x.get("symbol"): x for x in self.client.book_tickers() if x.get("symbol")}
        excluded = set(self.config.excluded_symbols)
        result: List[Dict[str, Any]] = []
        for ticker in tickers:
            symbol = str(ticker.get("symbol", "")).upper()
            meta = self.client._symbol_meta.get(symbol)
            if not meta:
                continue
            if meta.get("quote_asset") != self.config.quote_asset:
                continue
            if meta.get("status") != "TRADING" or meta.get("contract_type") != "PERPETUAL":
                continue
            if symbol in excluded:
                continue
            price = safe_float(ticker.get("lastPrice"))
            quote_volume = safe_float(ticker.get("quoteVolume"))
            change = safe_float(ticker.get("priceChangePercent"))
            trade_count = safe_int(ticker.get("count"))
            spread = self.spread_pct(books.get(symbol, {}))
            if price <= 0:
                continue
            if quote_volume < self.config.min_24h_quote_volume:
                continue
            if self.config.min_coin_price > 0 and price < self.config.min_coin_price:
                continue
            if self.config.max_coin_price > 0 and price > self.config.max_coin_price:
                continue
            if self.config.min_24h_trade_count > 0 and trade_count < self.config.min_24h_trade_count:
                continue
            if self.config.max_abs_24h_change_pct > 0 and abs(change) > self.config.max_abs_24h_change_pct:
                continue
            if self.config.min_abs_24h_change_pct > 0 and abs(change) < self.config.min_abs_24h_change_pct:
                continue
            if spread > self.config.max_spread_pct:
                continue
            result.append({
                "symbol": symbol, "price": price, "quote_volume": quote_volume,
                "change_pct": change, "trade_count": trade_count, "spread_pct": spread,
            })
        result.sort(key=lambda x: x["quote_volume"], reverse=True)
        self._market_cache = result[: self.config.scan_top_n]
        self._market_cache_ts = time.time()
        return list(self._market_cache)

    def find_candidate(
        self,
        active_symbols: Iterable[str],
        exposure: Exposure,
    ) -> Optional[SignalDecision]:
        active = {s.upper() for s in active_symbols}
        candidates: List[SignalDecision] = []
        universe = self.market_universe()
        evaluated = 0
        for coin in universe:
            symbol = coin["symbol"]
            if symbol in active or self.is_blocked(symbol):
                continue
            if evaluated >= self.config.max_signal_eval_coins:
                break
            evaluated += 1
            try:
                decision = self.signal_engine.evaluate(symbol)
                decision.components.update(coin)
                decision = self.balance_manager.apply(decision, exposure)
                if decision.side:
                    candidates.append(decision)
            except BinanceAPIError as exc:
                logger.warning("Bỏ qua %s do Binance API: %s", symbol, exc)
            except Exception as exc:
                logger.error("Lỗi đánh tín hiệu %s: %s", symbol, exc)

        if not candidates:
            return None
        candidates.sort(
            key=lambda d: (
                d.selected_score,
                safe_float(d.components.get("quote_volume")),
                -safe_float(d.components.get("spread_pct"), 999),
            ),
            reverse=True,
        )
        return candidates[0]


# =============================================================================
# POSITION / DCA / REVERSE MANAGER (LIVE)
# =============================================================================

class PositionManager:
    """Quản lý vị thế thật trên Binance."""

    def __init__(
        self,
        config: BotConfig,
        client: BinanceFuturesClient,
        database: DatabaseManager,
        signal_engine: SignalEngine,
        balance_manager: BalanceManager,
        notify: Optional[Any] = None,
    ):
        self.config = config
        self.client = client
        self.database = database
        self.signal_engine = signal_engine
        self.balance_manager = balance_manager
        self.notify = notify or (lambda message: logger.info("%s", message))
        self._locks: Dict[str, threading.RLock] = {}
        self._cache: Dict[int, Dict[str, Any]] = {}
        self._last_opposite_check: Dict[str, float] = {}
        self._pending_closures: Dict[int, Dict[str, Any]] = {}

    def symbol_lock(self, symbol: str) -> threading.RLock:
        if symbol not in self._locks:
            self._locks[symbol] = threading.RLock()
        return self._locks[symbol]

    def balances(self) -> Dict[str, float]:
        """Lấy số dư thật từ Binance."""
        try:
            info = self.client.account_info()
            assets = {a["asset"]: a for a in info.get("assets", [])}
            usdt = assets.get("USDT", {})
            wallet = safe_float(usdt.get("walletBalance"))
            available = safe_float(usdt.get("availableBalance"))
            unrealized = safe_float(usdt.get("unrealizedProfit"))
            return {
                "wallet_balance": wallet,
                "available_balance": available,
                "margin_balance": wallet + unrealized,
                "unrealized_pnl": unrealized,
                "maint_margin": safe_float(usdt.get("maintMargin")),
            }
        except BinanceAPIError:
            # Fallback: nếu không lấy được, dùng số dư trong DB (có thể cũ)
            # Ta sẽ trả về số dư cuối cùng đã lưu
            snap = self.database.get_runtime("last_balance", {})
            return {
                "wallet_balance": safe_float(snap.get("wallet_balance", 0)),
                "available_balance": safe_float(snap.get("available_balance", 0)),
                "margin_balance": safe_float(snap.get("margin_balance", 0)),
                "unrealized_pnl": safe_float(snap.get("unrealized_pnl", 0)),
                "maint_margin": 0.0,
            }

    def active_rows(self) -> List[Dict[str, Any]]:
        if self.database.available:
            rows = self.database.active_positions()
            self._cache = {int(row["id"]): dict(row) for row in rows}
        return [dict(v) for v in self._cache.values() if str(v.get("status")) in ACTIVE_DB_STATUSES]

    def active_symbols(self) -> List[str]:
        return [str(row.get("symbol", "")).upper() for row in self.active_rows()]

    def exposure(self) -> Exposure:
        # Lấy vị thế thật từ Binance để tính exposure chính xác
        binance_positions = self.client.nonzero_positions()
        return self.balance_manager.exposure_from_positions(binance_positions)

    def _tp_sl_for_side(self, side: str) -> Tuple[Optional[float], Optional[float]]:
        if side == "BUY":
            return self.config.long_tp_roi_pct, self.config.long_sl_roi_pct
        return self.config.short_tp_roi_pct, self.config.short_sl_roi_pct

    def _position_metrics(self, row: Dict[str, Any], mark_price: float) -> Dict[str, Any]:
        side = str(row.get("side"))
        leverage = max(1, safe_int(row.get("leverage"), self.config.leverage))
        entry = safe_float(row.get("average_entry_price"))
        qty = abs(safe_float(row.get("current_quantity")))
        mark = mark_price if mark_price > 0 else entry
        pnl = (mark - entry) * qty if side == "BUY" else (entry - mark) * qty
        roi = 0.0
        if entry > 0:
            roi = ((mark - entry) / entry if side == "BUY" else (entry - mark) / entry) * 100.0 * leverage
        notional = qty * mark
        margin = safe_float(row.get("current_margin")) or (qty * entry / leverage if leverage > 0 else 0.0)
        best_raw = row.get("best_roi_pct")
        worst_raw = row.get("worst_roi_pct")
        best = roi if best_raw is None else max(safe_float(best_raw), roi)
        worst = roi if worst_raw is None else min(safe_float(worst_raw), roi)
        return {
            "side": side, "quantity": qty, "entry_price": entry, "mark_price": mark,
            "leverage": leverage, "notional": notional, "margin": margin,
            "roi": roi, "unrealized_pnl": pnl,
            "best_roi_pct": best, "worst_roi_pct": worst,
        }

    def _runtime_until(self, prefix: str, symbol: str) -> float:
        value = self.database.get_runtime(f"{prefix}:{symbol.upper()}", 0)
        return safe_float(value.get("until")) if isinstance(value, dict) else safe_float(value)

    def _record_runtime_until(self, prefix: str, symbol: str, seconds: int, reason: str) -> None:
        if seconds <= 0:
            return
        self.database.set_runtime(
            f"{prefix}:{symbol.upper()}",
            {"until": time.time() + seconds, "reason": reason, "set_at": utc_now().isoformat()},
            required=False,
        )

    def _last_entry_candle(self, symbol: str) -> int:
        value = self.database.get_runtime(f"last_entry_candle:{symbol.upper()}", 0)
        return safe_int(value.get("open_time")) if isinstance(value, dict) else safe_int(value)

    def _save_last_entry_candle(self, symbol: str, open_time: int) -> None:
        self.database.set_runtime(
            f"last_entry_candle:{symbol.upper()}",
            {"open_time": int(open_time), "saved_at": utc_now().isoformat()},
            required=False,
        )

    def _daily_loss_reached(self, wallet_balance: float) -> bool:
        if self.config.max_daily_loss_pct <= 0 or wallet_balance <= 0 or not self.database.available:
            return False
        row = self.database._run(
            """
            SELECT COALESCE(SUM(net_pnl),0) AS net FROM bot_positions
            WHERE instance_name=%s AND status='CLOSED' AND closed_at >= date_trunc('day', NOW())
            """,
            (self.config.bot_instance_name,), fetch="one", required=False,
        )
        day_net = safe_float((row or {}).get("net"))
        return day_net <= -(wallet_balance * self.config.max_daily_loss_pct / 100.0)

    def can_open(self, decision: SignalDecision, bypass_cooldown: bool = False) -> Tuple[bool, str, Dict[str, float]]:
        if not self.config.trading_enabled:
            return False, "TRADING_ENABLED=false", {}
        if not self.database.available:
            return False, "Database đang lỗi: chặn mở vị thế mới", {}
        rows = self.active_rows()
        if len(rows) >= self.config.max_positions:
            return False, f"Đã đạt max_positions={self.config.max_positions}", {}
        if decision.symbol in {str(r.get("symbol")).upper() for r in rows}:
            return False, "Symbol đã có vị thế", {}
        if decision.candle_open_time == self._last_entry_candle(decision.symbol):
            return False, "Đã dùng nến này", {}
        if not bypass_cooldown:
            now = time.time()
            for prefix in ("cooldown_until", "blacklist_until"):
                until = self._runtime_until(prefix, decision.symbol)
                if now < until:
                    return False, f"{prefix} còn {until - now:.0f}s", {}
        balances = self.balances()
        wallet = balances["wallet_balance"]
        if wallet <= 0:
            return False, "Số dư USDT <= 0", balances
        if self._daily_loss_reached(wallet):
            return False, "Đã đạt giới hạn lỗ ngày", balances
        exposure = self.exposure()
        requested_margin = wallet * self.config.entry_margin_pct / 100.0
        requested_margin = min(
            requested_margin,
            wallet * self.config.max_total_margin_per_symbol_pct / 100.0,
        )
        proposed_notional = requested_margin * self.config.leverage
        max_total = wallet * self.config.max_total_notional_pct / 100.0
        if max_total > 0 and exposure.total_notional + proposed_notional > max_total:
            return False, "Vượt max_total_notional_pct", balances
        if requested_margin > balances["available_balance"]:
            return False, "Không đủ available balance", balances
        balances["requested_margin"] = requested_margin
        balances["proposed_notional"] = proposed_notional
        return True, "OK", balances

    def open_position(
        self,
        decision: SignalDecision,
        is_reverse: bool = False,
        reverse_count: int = 0,
        bypass_cooldown: bool = False,
    ) -> bool:
        symbol = decision.symbol.upper()
        side = str(decision.side or "").upper()
        if side not in {"BUY", "SELL"}:
            return False
        with self.symbol_lock(symbol):
            ok, reason, balances = self.can_open(decision, bypass_cooldown)
            if not ok:
                logger.info("Không mở %s %s: %s", symbol, side, reason)
                return False

            # Set margin type và leverage trước khi order
            try:
                self.client.set_margin_type(symbol, self.config.margin_type)
                self.client.set_leverage(symbol, self.config.leverage)
            except BinanceAPIError as e:
                logger.error("Lỗi thiết lập margin/leverage cho %s: %s", symbol, e)
                return False

            price = self.client.mark_price(symbol)
            meta = self.client.symbol_meta(symbol)
            margin = balances["requested_margin"]
            qty = floor_to_step(margin * self.config.leverage / price, meta["step_size"])
            notional = qty * price
            if qty < meta["min_qty"] or notional < meta["min_notional"]:
                logger.info("Số lượng/notional quá nhỏ %s: qty=%s, notional=%s", symbol, qty, notional)
                return False

            # Gửi lệnh market
            try:
                order = self.client.market_order(symbol, side, qty, reduce_only=False)
            except BinanceAPIError as e:
                logger.error("Lỗi gửi lệnh market %s %s: %s", symbol, side, e)
                return False

            order_id = order.get("orderId")
            # Chờ vị thế được cập nhật
            pos = self.client.wait_for_position(symbol, qty if side == "BUY" else -qty, self.config.position_confirm_timeout_seconds)
            if not pos or abs(safe_float(pos.get("positionAmt"))) < qty * 0.9:
                logger.warning("Vị thế %s chưa khớp sau khi gửi lệnh, sẽ sync sau", symbol)
                # Vẫn lưu pending, lần sync sau sẽ cập nhật
                # Tạm dùng giá và số lượng từ lệnh
                entry_price = safe_float(order.get("price")) or price
                executed_qty = safe_float(order.get("executedQty")) or qty
                notional_actual = executed_qty * entry_price
                margin_actual = notional_actual / max(self.config.leverage, 1)
            else:
                entry_price = safe_float(pos.get("entryPrice"))
                executed_qty = abs(safe_float(pos.get("positionAmt")))
                notional_actual = executed_qty * entry_price
                margin_actual = notional_actual / max(self.config.leverage, 1)

            tp_roi, sl_roi = self._tp_sl_for_side(side)
            pending = {
                "symbol": symbol, "side": side, "leverage": self.config.leverage,
                "margin_type": self.config.margin_type,
                "initial_quantity": executed_qty, "current_quantity": executed_qty,
                "initial_entry_price": entry_price, "average_entry_price": entry_price,
                "initial_margin": margin_actual, "current_margin": margin_actual,
                "initial_notional": notional_actual, "current_notional": notional_actual,
                "tp_roi_pct": tp_roi, "sl_roi_pct": sl_roi,
                "tp_price": roi_price(side, entry_price, tp_roi, self.config.leverage, True),
                "sl_price": roi_price(side, entry_price, sl_roi, self.config.leverage, False),
                "dca_mode": self.config.dca_mode, "dca_multiplier": self.config.dca_multiplier,
                "dca_count": 0, "max_dca_steps": self.config.max_dca_steps,
                "reverse_count": reverse_count, "max_reverse_count": self.config.max_reverse_count,
                "best_roi_pct": 0.0, "worst_roi_pct": 0.0, "last_roi_pct": 0.0,
                "entry_reason": "REVERSE" if is_reverse else decision.reason,
                "signal_score": decision.selected_score, "balance_reason": decision.balance_reason,
                "open_order_id": str(order_id), "last_synced_at": utc_now(),
                "binance_open_order_json": order,
                "is_simulated": False,
            }
            try:
                position_id = self.database.create_pending_position(pending)
                self.database.add_event(
                    "REVERSE_REQUESTED" if is_reverse else "OPEN_REQUESTED",
                    symbol, position_id=position_id, side=side, quantity=executed_qty, price=entry_price,
                    margin=margin_actual, notional=notional_actual, reason=decision.reason,
                    order_id=str(order_id), raw=order, required=True,
                )
                self.database.confirm_open(position_id, {
                    "quantity": executed_qty, "entry_price": entry_price,
                    "margin": margin_actual, "notional": notional_actual,
                    "tp_price": pending["tp_price"], "sl_price": pending["sl_price"],
                    "position_json": pos, "order_json": order,
                    "open_order_id": str(order_id),
                })
                self.database.add_event(
                    "REVERSE_CONFIRMED" if is_reverse else "OPEN_CONFIRMED",
                    symbol, position_id=position_id, side=side, quantity=executed_qty, price=entry_price,
                    margin=margin_actual, notional=notional_actual, reason=decision.reason,
                    order_id=str(order_id), raw={"pos": pos, "order": order}, required=False,
                )
                self._save_last_entry_candle(symbol, decision.candle_open_time)
                row = self.database.active_position(symbol) or {**pending, "id": position_id, "status": "ACTIVE"}
                self._cache[position_id] = dict(row)
                self.notify(
                    f"🟢 LIVE OPEN {symbol} {side}\nEntry: {entry_price:.8g}\nQuantity: {executed_qty:.8g}\n"
                    f"Leverage: {self.config.leverage}x\nMargin: {margin_actual:.4f} USDT\n"
                    f"Signal: {decision.selected_score:.2f}\nReason: {decision.reason}"
                )
                return True
            except Exception as exc:
                logger.error("LIVE OPEN lỗi %s: %s", symbol, exc)
                return False

    def should_dca(self, row: Dict[str, Any], metrics: Dict[str, Any]) -> bool:
        if not self.database.available:
            return False
        side = metrics["side"]
        if side == "BUY" and not self.config.enable_dca_long:
            return False
        if side == "SELL" and not self.config.enable_dca_short:
            return False
        count = safe_int(row.get("dca_count"))
        if count >= min(safe_int(row.get("max_dca_steps"), self.config.max_dca_steps), self.config.max_dca_steps):
            return False
        last_added = row.get("last_added_at")
        if isinstance(last_added, datetime) and time.time() - last_added.timestamp() < self.config.dca_min_seconds_between_adds:
            return False
        level = self.config.dca_trigger_roi_pct * (count + 1)
        return metrics["roi"] <= -level if self.config.dca_mode == "loss" else metrics["roi"] >= level

    def add_dca(self, row: Dict[str, Any], metrics: Dict[str, Any]) -> bool:
        symbol = str(row["symbol"])
        with self.symbol_lock(symbol):
            count = safe_int(row.get("dca_count"))
            step = count + 1
            add_margin = safe_float(row.get("initial_margin")) * (self.config.dca_multiplier ** step)
            balances = self.balances()
            cap = balances["wallet_balance"] * self.config.max_total_margin_per_symbol_pct / 100.0
            current_margin = safe_float(row.get("current_margin"))
            if current_margin + add_margin > cap or add_margin > balances["available_balance"]:
                return False
            price = metrics["mark_price"]
            meta = self.client.symbol_meta(symbol)
            add_qty = floor_to_step(add_margin * metrics["leverage"] / price, meta["step_size"])
            if add_qty < meta["min_qty"] or add_qty * price < meta["min_notional"]:
                return False
            # Gửi lệnh market thêm
            side = metrics["side"]
            try:
                order = self.client.market_order(symbol, side, add_qty, reduce_only=False)
            except BinanceAPIError as e:
                logger.error("Lỗi DCA market %s: %s", symbol, e)
                return False
            # Chờ vị thế cập nhật
            pos = self.client.wait_for_position(symbol, None, 5)  # không check cụ thể
            if not pos:
                pos = self.client.position(symbol)
            # Cập nhật dữ liệu từ vị thế thực
            new_qty = abs(safe_float(pos.get("positionAmt"))) if pos else 0
            new_entry = safe_float(pos.get("entryPrice")) if pos else metrics["entry_price"]
            new_margin = (new_qty * new_entry) / max(metrics["leverage"], 1)
            new_notional = new_qty * new_entry
            tp = safe_float(row.get("tp_roi_pct")) if row.get("tp_roi_pct") is not None else None
            sl = safe_float(row.get("sl_roi_pct")) if row.get("sl_roi_pct") is not None else None

            order_id = order.get("orderId")
            self.database.add_event(
                "DCA_REQUESTED", symbol, position_id=int(row["id"]), side=side,
                quantity=add_qty, price=price, margin=add_margin, notional=add_qty * price,
                roi_pct=metrics["roi"], dca_step=step, reason=self.config.dca_mode,
                order_id=str(order_id), raw=order, required=True,
            )
            self.database.confirm_dca(int(row["id"]), {
                "quantity": new_qty, "entry_price": new_entry, "margin": new_margin,
                "notional": new_notional, "dca_count": step,
                "tp_price": roi_price(side, new_entry, tp, metrics["leverage"], True),
                "sl_price": roi_price(side, new_entry, sl, metrics["leverage"], False),
                "position_json": pos,
            })
            self.database.add_event(
                "DCA_CONFIRMED", symbol, position_id=int(row["id"]), side=side,
                quantity=add_qty, price=price, margin=add_margin, notional=add_qty * price,
                roi_pct=metrics["roi"], dca_step=step, order_id=str(order_id), raw={"pos": pos, "order": order},
            )
            row.update(
                current_quantity=new_qty, average_entry_price=new_entry,
                current_margin=new_margin, current_notional=new_notional,
                dca_count=step, last_added_at=utc_now(),
            )
            self._cache[int(row["id"])] = row
            self.notify(
                f"➕ LIVE DCA {symbol} {side} bước {step}/{self.config.max_dca_steps}\n"
                f"Add margin: {add_margin:.4f}\nAvg entry: {new_entry:.8g}"
            )
            return True

    def _reverse_decision(self, symbol: str, old_side: str, exit_price: float) -> Optional[SignalDecision]:
        opposite = "SELL" if old_side == "BUY" else "BUY"
        if self.config.reverse_mode == "none":
            return None
        if self.config.reverse_mode == "immediate":
            return SignalDecision(
                symbol, opposite, self.config.reverse_min_score,
                self.config.reverse_min_score if opposite == "BUY" else 0.0,
                self.config.reverse_min_score if opposite == "SELL" else 0.0,
                int(time.time() * 1000), int(time.time() * 1000),
                "Live reverse immediate", {"close": exit_price},
            )
        decision = self.signal_engine.evaluate(symbol)
        if decision.score_for(opposite) >= self.config.reverse_min_score and decision.score_for(opposite) > decision.score_for(old_side):
            decision.side = opposite
            decision.selected_score = decision.score_for(opposite)
            decision.reason = "Live reverse confirmed: " + decision.reason
            return decision
        return None

    def close_position(self, row: Dict[str, Any], close_reason: str, allow_reverse: bool = True) -> bool:
        symbol = str(row["symbol"]).upper()
        position_id = int(row["id"])
        with self.symbol_lock(symbol):
            # Lấy vị thế thật
            pos = self.client.position(symbol)
            if not pos or abs(safe_float(pos.get("positionAmt"))) < 1e-6:
                # Vị thế đã đóng, chỉ cần cập nhật DB
                self.database.close_position(position_id, {
                    "exit_price": safe_float(pos.get("markPrice")) if pos else 0,
                    "realized_pnl": 0, "commission": 0, "funding_fee": 0, "net_pnl": 0,
                    "close_reason": close_reason, "close_order_id": "ALREADY_CLOSED",
                    "close_order_json": {"manual": True},
                })
                self._cache.pop(position_id, None)
                self.notify(f"ℹ️ Vị thế {symbol} đã đóng từ Binance, DB cập nhật")
                return True

            qty = abs(safe_float(pos.get("positionAmt")))
            side = normalize_side(safe_float(pos.get("positionAmt")))
            if not side:
                return False

            # Gửi lệnh đóng toàn bộ (reduceOnly)
            try:
                order = self.client.market_order(symbol, side, qty, reduce_only=True)
            except BinanceAPIError as e:
                logger.error("Lỗi đóng vị thế %s: %s", symbol, e)
                return False

            # Chờ vị thế về 0
            self.client.wait_for_position(symbol, 0.0, self.config.close_confirm_timeout_seconds)
            # Lấy trade để tính phí
            trades = self.client.user_trades(symbol, limit=5)
            # Tìm trade khớp với order
            relevant_trades = [t for t in trades if str(t.get("orderId")) == str(order.get("orderId"))]
            if not relevant_trades:
                # Fallback: dùng thông tin từ order
                realized_pnl = safe_float(order.get("realizedPnl", 0))
                commission = safe_float(order.get("commission", 0))
                exit_price = safe_float(order.get("price")) or safe_float(pos.get("markPrice"))
            else:
                t = relevant_trades[-1]
                realized_pnl = safe_float(t.get("realizedPnl", 0))
                commission = safe_float(t.get("commission", 0))
                exit_price = safe_float(t.get("price"))

            close_data = {
                "exit_price": exit_price,
                "realized_pnl": realized_pnl,
                "commission": commission,
                "funding_fee": 0,  # lấy từ income nếu cần
                "net_pnl": realized_pnl - commission,
                "close_reason": close_reason,
                "close_order_id": str(order.get("orderId")),
                "close_order_json": order,
            }
            if self.database.available:
                self.database.mark_pending_close(position_id, close_reason, str(order.get("orderId")))
                self.database.add_event(
                    "CLOSE_REQUESTED", symbol, position_id=position_id, side=side,
                    quantity=qty, price=exit_price, roi_pct=0,
                    pnl=realized_pnl, reason=close_reason, order_id=str(order.get("orderId")),
                    raw=order,
                )
                self.database.close_position(position_id, close_data)
                self.database.add_event(
                    "CLOSE_CONFIRMED", symbol, position_id=position_id, side=side,
                    quantity=qty, price=exit_price, roi_pct=0,
                    pnl=realized_pnl, commission=commission, funding_fee=0,
                    reason=close_reason, order_id=str(order.get("orderId")), raw=order,
                )
            else:
                self._pending_closures[position_id] = close_data
                self.database.journal({
                    "event_type": "LIVE_CLOSE_PENDING_DB", "position_id": position_id,
                    "symbol": symbol, **close_data,
                })
            self._cache.pop(position_id, None)
            self._record_runtime_until("cooldown_until", symbol, self.config.cooldown_after_close_seconds, close_reason)
            if reason_code(close_reason) in CLOSE_REASONS_BLACKLIST:
                self._record_runtime_until("blacklist_until", symbol, self.config.blacklist_after_tp_sl_seconds, close_reason)
            self.notify(
                f"🔴 LIVE CLOSE {symbol} {side}\nReason: {close_reason}\n"
                f"Exit: {exit_price:.8g}\n"
                f"Realized PnL: {realized_pnl:.4f}\nCommission: {commission:.4f}\n"
                f"Net PnL: {close_data['net_pnl']:.4f} USDT"
            )
            reason_key = reason_code(close_reason)
            if allow_reverse and reason_key in set(self.config.reverse_after_close_reasons):
                reverse_count = safe_int(row.get("reverse_count"))
                if reverse_count < self.config.max_reverse_count:
                    decision = self._reverse_decision(symbol, side, exit_price)
                    if decision:
                        self.open_position(decision, True, reverse_count + 1, True)
            return True

    def reconcile(self) -> None:
        """Đồng bộ vị thế thật từ Binance vào DB."""
        if not self.database.available:
            return

        # Xử lý các pending closures đã được thực hiện khi DB offline
        for position_id, data in list(self._pending_closures.items()):
            try:
                self.database.close_position(position_id, data)
                self._pending_closures.pop(position_id, None)
            except Exception:
                return

        # Lấy tất cả vị thế đang mở trên Binance
        binance_positions = self.client.nonzero_positions()
        active_db = self.database.active_positions()
        db_symbols = {str(r["symbol"]).upper() for r in active_db}
        binance_symbols = {str(p["symbol"]).upper() for p in binance_positions}

        # Cập nhật hoặc tạo mới cho từng vị thế Binance
        for pos in binance_positions:
            symbol = str(pos["symbol"]).upper()
            existing = next((r for r in active_db if str(r["symbol"]).upper() == symbol), None)
            if existing:
                # Cập nhật thông tin
                pos_id = int(existing["id"])
                amt = safe_float(pos.get("positionAmt"))
                side = normalize_side(amt)
                if side is None:
                    continue
                qty = abs(amt)
                entry = safe_float(pos.get("entryPrice"))
                mark = safe_float(pos.get("markPrice"))
                leverage = safe_int(pos.get("leverage"), self.config.leverage)
                notional = qty * mark
                margin = notional / max(leverage, 1)
                roi = ((mark - entry) / entry if side == "BUY" else (entry - mark) / entry) * 100.0 * leverage
                pnl = (mark - entry) * qty if side == "BUY" else (entry - mark) * qty
                self.database.update_position_live(pos_id, {
                    "side": side, "quantity": qty, "entry_price": entry,
                    "margin": margin, "notional": notional,
                    "best_roi_pct": max(safe_float(existing.get("best_roi_pct")), roi),
                    "worst_roi_pct": min(safe_float(existing.get("worst_roi_pct")), roi),
                    "last_roi_pct": roi, "unrealized_pnl": pnl,
                    "position_json": pos,
                })
                self._cache[pos_id] = {**existing, "current_quantity": qty, "average_entry_price": entry,
                                        "current_margin": margin, "current_notional": notional,
                                        "last_roi_pct": roi, "unrealized_pnl": pnl,
                                        "binance_position_json": pos}
            else:
                # Vị thế mới trên Binance chưa có trong DB
                try:
                    self.database.create_recovered_position(pos, self.config)
                    self.notify(f"🔄 RECOVERED {symbol} từ Binance")
                except Exception as e:
                    logger.error("Không recover %s: %s", symbol, e)

        # Đánh dấu vị thế trong DB đã đóng trên Binance (nếu có)
        for row in active_db:
            symbol = str(row["symbol"]).upper()
            if symbol not in binance_symbols and str(row.get("status")) not in ("CLOSED", "ERROR"):
                # Vị thế đã biến mất trên Binance, coi như đã đóng
                try:
                    self.database.close_position(int(row["id"]), {
                        "exit_price": 0, "realized_pnl": 0, "commission": 0,
                        "funding_fee": 0, "net_pnl": 0,
                        "close_reason": "SYNC_CLOSED", "close_order_id": "SYNC",
                        "close_order_json": {"reason": "position not found on Binance"},
                    })
                    self.notify(f"ℹ️ Vị thế {symbol} đã đóng (sync)")
                except Exception:
                    pass

        # Cập nhật số dư vào runtime
        balances = self.balances()
        self.database.set_runtime("last_balance", balances, required=False)

    def manage_all(self) -> None:
        for row in self.active_rows():
            try:
                symbol = str(row["symbol"])
                # Lấy mark price mới nhất
                mark_price = self.client.mark_price(symbol)
                metrics = self._position_metrics(row, mark_price)
                # Cập nhật DB
                self.database.update_position_live(int(row["id"]), {
                    "side": metrics["side"], "quantity": metrics["quantity"],
                    "entry_price": metrics["entry_price"], "margin": metrics["margin"],
                    "notional": metrics["notional"], "best_roi_pct": metrics["best_roi_pct"],
                    "worst_roi_pct": metrics["worst_roi_pct"], "last_roi_pct": metrics["roi"],
                    "unrealized_pnl": metrics["unrealized_pnl"],
                    "position_json": {"markPrice": mark_price},
                })
                row.update(
                    best_roi_pct=metrics["best_roi_pct"], worst_roi_pct=metrics["worst_roi_pct"],
                    last_roi_pct=metrics["roi"], unrealized_pnl=metrics["unrealized_pnl"],
                    current_notional=metrics["notional"],
                )
                self._cache[int(row["id"])] = row
                tp = safe_float(row.get("tp_roi_pct")) if row.get("tp_roi_pct") is not None else None
                sl = safe_float(row.get("sl_roi_pct")) if row.get("sl_roi_pct") is not None else None
                if tp is not None and tp > 0 and metrics["roi"] >= tp:
                    self.close_position(row, f"TP {tp:.2f}%")
                    continue
                if sl is not None and sl > 0 and metrics["roi"] <= -abs(sl):
                    self.close_position(row, f"SL {sl:.2f}%")
                    continue
                if (
                    self.config.enable_profit_protect
                    and metrics["best_roi_pct"] >= self.config.protect_start_roi_pct
                    and metrics["best_roi_pct"] - metrics["roi"] >= self.config.protect_pullback_roi_pct
                ):
                    self.close_position(row, f"TRAILING_PROFIT peak={metrics['best_roi_pct']:.2f}%")
                    continue
                if self.config.enable_exit_on_opposite_signal:
                    last = self._last_opposite_check.get(symbol, 0.0)
                    if time.time() - last >= max(5, self.config.manage_interval_seconds):
                        self._last_opposite_check[symbol] = time.time()
                        decision = self.signal_engine.evaluate(symbol)
                        opposite = "SELL" if metrics["side"] == "BUY" else "BUY"
                        if decision.score_for(opposite) >= self.config.opposite_exit_min_score and decision.score_for(opposite) > decision.score_for(metrics["side"]):
                            self.close_position(row, f"OPPOSITE_SIGNAL {opposite} score={decision.score_for(opposite):.2f}")
                            continue
                if self.should_dca(row, metrics):
                    self.add_dca(row, metrics)
            except Exception as exc:
                logger.error("Lỗi manage live %s: %s\n%s", row.get("symbol"), exc, traceback.format_exc())

    def snapshot(self) -> Dict[str, Any]:
        balances = self.balances()
        exposure = self.exposure()
        data = {
            **balances,
            "long_notional": exposure.long_notional,
            "short_notional": exposure.short_notional,
            "total_notional": exposure.total_notional,
            "long_positions": exposure.long_positions,
            "short_positions": exposure.short_positions,
            "total_positions": exposure.total_positions,
        }
        self.database.save_snapshot(data)
        return data


# =============================================================================
# STATISTICS (giữ nguyên)
# =============================================================================

class StatisticsService:
    def __init__(self, database: DatabaseManager):
        self.database = database

    @staticmethod
    def _group(rows: Sequence[Dict[str, Any]], key_func: Any) -> Dict[str, Dict[str, Any]]:
        groups: Dict[str, List[Dict[str, Any]]] = {}
        for row in rows:
            key = str(key_func(row))
            groups.setdefault(key, []).append(row)
        result: Dict[str, Dict[str, Any]] = {}
        for key, items in groups.items():
            net = [safe_float(x.get("net_pnl")) for x in items]
            wins = [x for x in net if x > 0]
            losses = [x for x in net if x < 0]
            result[key] = {
                "trades": len(items),
                "wins": len(wins),
                "losses": len(losses),
                "win_rate_pct": len(wins) / len(items) * 100.0 if items else 0.0,
                "net_pnl": sum(net),
                "avg_pnl": sum(net) / len(net) if net else 0.0,
            }
        return result

    def report(self) -> Dict[str, Any]:
        rows = self.database.closed_positions()
        net_values = [safe_float(r.get("net_pnl")) for r in rows]
        winners = [v for v in net_values if v > 0]
        losers = [v for v in net_values if v < 0]
        gross_profit = sum(winners)
        gross_loss = abs(sum(losers))
        total = len(rows)
        wins = len(winners)
        losses = len(losers)
        win_rate = wins / total if total else 0.0
        loss_rate = losses / total if total else 0.0
        avg_win = gross_profit / wins if wins else 0.0
        avg_loss = gross_loss / losses if losses else 0.0
        expectancy = win_rate * avg_win - loss_rate * avg_loss
        profit_factor = gross_profit / gross_loss if gross_loss > 0 else (float("inf") if gross_profit > 0 else 0.0)

        cumulative = peak = max_drawdown = 0.0
        for value in net_values:
            cumulative += value
            peak = max(peak, cumulative)
            max_drawdown = max(max_drawdown, peak - cumulative)

        buy_rows = [r for r in rows if r.get("side") == "BUY"]
        sell_rows = [r for r in rows if r.get("side") == "SELL"]
        reverse_rows = [r for r in rows if str(r.get("entry_reason", "")).upper().startswith("REVERSE")]
        balance_rows = [r for r in rows if r.get("balance_reason")]

        def closed_dt(row: Dict[str, Any]) -> datetime:
            value = row.get("closed_at")
            if isinstance(value, datetime):
                return value
            try:
                return datetime.fromisoformat(str(value).replace("Z", "+00:00"))
            except Exception:
                return datetime(1970, 1, 1, tzinfo=UTC)

        def score_bucket(row: Dict[str, Any]) -> str:
            score = safe_float(row.get("signal_score"))
            low = math.floor(score)
            return f"{low}-{low + 0.99:.2f}"

        report = {
            "total_positions": total,
            "buy_positions": len(buy_rows),
            "sell_positions": len(sell_rows),
            "wins": wins,
            "losses": losses,
            "win_rate_pct": win_rate * 100.0,
            "buy_win_rate_pct": (
                sum(1 for r in buy_rows if safe_float(r.get("net_pnl")) > 0) / len(buy_rows) * 100.0
                if buy_rows else 0.0
            ),
            "sell_win_rate_pct": (
                sum(1 for r in sell_rows if safe_float(r.get("net_pnl")) > 0) / len(sell_rows) * 100.0
                if sell_rows else 0.0
            ),
            "gross_profit": gross_profit,
            "gross_loss": gross_loss,
            "net_pnl": sum(net_values),
            "total_commission": sum(safe_float(r.get("commission")) for r in rows),
            "total_funding": sum(safe_float(r.get("funding_fee")) for r in rows),
            "profit_factor": profit_factor,
            "average_win": avg_win,
            "average_loss": avg_loss,
            "expectancy": expectancy,
            "maximum_drawdown": max_drawdown,
            "average_dca_count": (
                sum(safe_int(r.get("dca_count")) for r in rows) / total if total else 0.0
            ),
            "reverse_performance": self._group(reverse_rows, lambda _: "reverse").get("reverse", {}),
            "balance_performance": self._group(balance_rows, lambda _: "balance").get("balance", {}),
            "by_dca_count": self._group(rows, lambda r: safe_int(r.get("dca_count"))),
            "by_symbol": self._group(rows, lambda r: r.get("symbol")),
            "by_day": self._group(rows, lambda r: closed_dt(r).date().isoformat()),
            "by_hour": self._group(rows, lambda r: f"{closed_dt(r).hour:02d}:00"),
            "by_close_reason": self._group(rows, lambda r: reason_code(str(r.get("close_reason", "")))),
            "by_signal_score": self._group(rows, score_bucket),
            "best_roi_before_close": max((safe_float(r.get("best_roi_pct")) for r in rows), default=0.0),
            "worst_roi_before_close": min((safe_float(r.get("worst_roi_pct")) for r in rows), default=0.0),
        }
        return report

    def summary_text(self) -> str:
        r = self.report()
        pf = r["profit_factor"]
        pf_text = "∞" if math.isinf(pf) else f"{pf:.2f}"
        return (
            "📊 THỐNG KÊ POSTGRESQL\n"
            f"Tổng vị thế: {r['total_positions']} | BUY: {r['buy_positions']} | SELL: {r['sell_positions']}\n"
            f"Win rate: {r['win_rate_pct']:.2f}% | BUY: {r['buy_win_rate_pct']:.2f}% | SELL: {r['sell_win_rate_pct']:.2f}%\n"
            f"Gross profit: +{r['gross_profit']:.4f} | Gross loss: -{r['gross_loss']:.4f}\n"
            f"Net PnL: {r['net_pnl']:.4f} USDT\n"
            f"Commission: {r['total_commission']:.4f} | Funding: {r['total_funding']:.4f}\n"
            f"Profit factor: {pf_text} | Expectancy: {r['expectancy']:.4f}\n"
            f"Avg win: {r['average_win']:.4f} | Avg loss: {r['average_loss']:.4f}\n"
            f"Max drawdown: {r['maximum_drawdown']:.4f}\n"
            f"DCA trung bình: {r['average_dca_count']:.2f}"
        )


# =============================================================================
# TELEGRAM (giữ nguyên)
# =============================================================================

class TelegramService:
    def __init__(self, config: BotConfig):
        self.config = config
        self.token = config.telegram_bot_token
        self.chat_id = str(config.telegram_chat_id or "")
        self.base_url = f"https://api.telegram.org/bot{self.token}" if self.token else ""
        self.running = False
        self.offset = 0
        self.thread: Optional[threading.Thread] = None
        self.handlers: Dict[str, Any] = {}

    @property
    def enabled(self) -> bool:
        return bool(self.token and self.chat_id)

    def send(self, message: str) -> None:
        logger.info("TELEGRAM/LOG: %s", message.replace("\n", " | "))
        if not self.enabled:
            return
        try:
            requests.post(
                self.base_url + "/sendMessage",
                json={"chat_id": self.chat_id, "text": message[:4000]},
                timeout=15,
            ).raise_for_status()
        except Exception as exc:
            logger.error("Gửi Telegram lỗi: %s", exc)

    def configure_handlers(self, **handlers: Any) -> None:
        self.handlers.update(handlers)

    def start(self) -> None:
        if not self.enabled or self.running:
            return
        self.running = True
        self.thread = threading.Thread(target=self._poll_loop, daemon=True, name="telegram-poll")
        self.thread.start()

    def stop(self) -> None:
        self.running = False

    def _call(self, name: str, *args: Any) -> Any:
        handler = self.handlers.get(name)
        if not handler:
            return None
        return handler(*args)

    def _handle(self, text: str) -> str:
        text = text.strip()
        command, *rest = text.split(maxsplit=2)
        command = command.lower().split("@")[0]
        if command in {"/start", "/help"}:
            return (
                "Lệnh bot:\n"
                "/status - trạng thái hệ thống\n"
                "/positions - vị thế đang quản lý\n"
                "/stats - thống kê PostgreSQL\n"
                "/config - cấu hình không chứa secret\n"
                "/pause - dừng mở lệnh mới, vẫn quản lý/đóng lệnh\n"
                "/resume - cho phép mở lệnh mới\n"
                "/close SYMBOL - đóng vị thế, không reverse\n"
                "/set ten_tham_so gia_tri - sửa cấu hình runtime"
            )
        if command == "/status":
            return str(self._call("status") or "Không lấy được status")
        if command == "/positions":
            return str(self._call("positions") or "Không có vị thế")
        if command == "/stats":
            return str(self._call("stats") or "Chưa có thống kê")
        if command == "/config":
            return str(self._call("config") or "Không lấy được config")[:4000]
        if command == "/pause":
            return str(self._call("trading", False) or "Đã pause")
        if command == "/resume":
            return str(self._call("trading", True) or "Đã resume")
        if command == "/close":
            if not rest:
                return "Cú pháp: /close SYMBOL"
            return str(self._call("close", rest[0].upper()) or "Không đóng được vị thế")
        if command == "/set":
            if len(rest) < 2:
                return "Cú pháp: /set ten_tham_so gia_tri"
            return str(self._call("set_config", rest[0], rest[1]) or "Không cập nhật được")
        return "Lệnh không hợp lệ. Dùng /help"

    def _poll_loop(self) -> None:
        while self.running:
            try:
                response = requests.get(
                    self.base_url + "/getUpdates",
                    params={"timeout": 25, "offset": self.offset, "allowed_updates": json.dumps(["message"])},
                    timeout=35,
                )
                payload = response.json()
                for update in payload.get("result", []):
                    self.offset = max(self.offset, safe_int(update.get("update_id")) + 1)
                    message = update.get("message") or {}
                    chat = str((message.get("chat") or {}).get("id", ""))
                    if chat != self.chat_id:
                        continue
                    text = str(message.get("text") or "")
                    if text:
                        self.send(self._handle(text))
            except Exception as exc:
                logger.warning("Telegram polling lỗi: %s", exc)
                time.sleep(5)


# =============================================================================
# APPLICATION / MAIN LOOP
# =============================================================================

class TradingBotApplication:
    def __init__(self, config: BotConfig):
        self.config = config
        self.client = BinanceFuturesClient(config)
        self.database = DatabaseManager(config)
        self.telegram = TelegramService(config)
        self.signal_engine = SignalEngine(config, self.client)
        self.balance_manager = BalanceManager(config)
        self.position_manager = PositionManager(
            config, self.client, self.database, self.signal_engine, self.balance_manager, self.notify
        )
        self.scanner = MarketScanner(
            config, self.client, self.signal_engine, self.balance_manager, self.database
        )
        self.statistics = StatisticsService(self.database)
        self.running = False
        self.last_manage = 0.0
        self.last_scan = 0.0
        self.last_sync = 0.0
        self.last_snapshot = 0.0
        self.last_db_retry = 0.0
        self._db_was_available = False
        self.telegram.configure_handlers(
            status=self.status_text,
            positions=self.positions_text,
            stats=self.statistics.summary_text,
            config=self.config_text,
            trading=self.set_trading_enabled,
            close=self.manual_close,
            set_config=self.set_config_value,
        )

    def notify(self, message: str) -> None:
        self.telegram.send(message)

    def load_persisted_config(self) -> None:
        saved = self.database.get_runtime("strategy_config", {})
        if isinstance(saved, dict) and saved:
            self.config.update_from_mapping(saved)
            errors = self.config.validate(require_credentials=False)
            if errors:
                logger.warning("Config DB có lỗi, vẫn dùng phần hợp lệ: %s", "; ".join(errors))
        trading = self.database.get_runtime("trading_enabled", self.config.trading_enabled)
        if isinstance(trading, dict):
            trading = trading.get("enabled", self.config.trading_enabled)
        self.config.trading_enabled = bool(trading)

    def initialize(self) -> None:
        errors = self.config.validate(require_credentials=True)
        if errors:
            raise RuntimeError("; ".join(errors))
        self.database.connect_and_prepare()
        if not self.database.acquire_instance_lock():
            raise RuntimeError(
                "Không lấy được PostgreSQL advisory lock: có thể một Railway replica khác đang chạy."
            )
        self._db_was_available = True
        self.load_persisted_config()
        self.database.set_runtime("bot_status", {"status": "CONNECTING", "at": utc_now().isoformat()}, required=False)

        self.client.sync_time()
        self.client.ping()
        self.client.exchange_info(force=True)
        # Đảm bảo chế độ one-way và margin type mặc định (sẽ set khi mở lệnh)
        self.client.ensure_one_way()
        # Đồng bộ vị thế
        self.position_manager.reconcile()
        self.database.set_runtime("bot_status", {"status": "RUNNING", "at": utc_now().isoformat()}, required=False)
        self.notify(
            "🟢 BOT LIVE KHỞI ĐỘNG\n"
            f"Instance: {self.config.bot_instance_name}\n"
            f"Mode: LIVE TRADING\n"
            f"Database: connected + advisory lock\n"
            f"Trading enabled: {self.config.trading_enabled}"
        )
        self.telegram.start()

    def _recover_database_if_needed(self) -> None:
        if time.time() - self.last_db_retry < self.config.database_retry_seconds:
            return
        self.last_db_retry = time.time()
        healthy = self.database.ping()
        if healthy:
            lock_conn = self.database._lock_connection
            lock_alive = lock_conn is not None and not lock_conn.closed
            if not lock_alive and not self.database.acquire_instance_lock():
                self.notify("⛔ Database hồi phục nhưng không lấy được advisory lock; dừng để tránh chạy trùng")
                self.running = False
                return
            if not self._db_was_available:
                self._db_was_available = True
                self.notify("✅ PostgreSQL đã hồi phục; bắt đầu reconcile Binance + database")
                self.position_manager.reconcile()
        else:
            if self._db_was_available:
                self._db_was_available = False
                self.notify(
                    "⚠️ PostgreSQL mất kết nối: chặn OPEN/DCA, vẫn cho phép CLOSE vị thế hiện tại"
                )

    def run_forever(self) -> None:
        self.initialize()
        self.running = True
        while self.running:
            try:
                self._recover_database_if_needed()
                now = time.time()

                if now - self.last_manage >= self.config.manage_interval_seconds:
                    self.last_manage = now
                    self.position_manager.manage_all()

                if now - self.last_sync >= self.config.sync_interval_seconds:
                    self.last_sync = now
                    if self.database.available:
                        self.position_manager.reconcile()

                if now - self.last_snapshot >= self.config.snapshot_interval_seconds:
                    self.last_snapshot = now
                    if self.database.available:
                        self.position_manager.snapshot()

                if (
                    self.config.trading_enabled
                    and self.database.available
                    and now - self.last_scan >= self.config.scan_interval_seconds
                    and len(self.position_manager.active_rows()) < self.config.max_positions
                ):
                    self.last_scan = now
                    exposure = self.position_manager.exposure()
                    decision = self.scanner.find_candidate(
                        self.position_manager.active_symbols(), exposure
                    )
                    if decision:
                        self.position_manager.open_position(decision)
                    else:
                        logger.info("Scanner: chưa có tín hiệu đủ điều kiện")
                time.sleep(0.5)
            except KeyboardInterrupt:
                break
            except BinanceAPIError as exc:
                logger.error("Binance loop error: %s", exc)
                self.notify(f"⚠️ Binance API lỗi: {exc}")
                time.sleep(3)
            except Exception as exc:
                logger.error("Main loop lỗi: %s\n%s", exc, traceback.format_exc())
                time.sleep(3)
        self.shutdown()

    def shutdown(self) -> None:
        if not self.running and self.database._lock_connection is None:
            return
        self.running = False
        self.telegram.stop()
        try:
            self.database.set_runtime("bot_status", {"status": "STOPPED", "at": utc_now().isoformat()}, required=False)
        except Exception:
            pass
        self.database.release_instance_lock()
        self.notify("⛔ BOT ĐÃ DỪNG")

    def status_text(self) -> str:
        try:
            snap = self.position_manager.snapshot() if self.database.available else {
                "wallet_balance": 0, "available_balance": 0, "unrealized_pnl": 0,
                "long_notional": 0, "short_notional": 0, "total_positions": len(self.position_manager.active_rows()),
            }
            return (
                "🤖 TRẠNG THÁI BOT\n"
                f"Instance: {self.config.bot_instance_name}\n"
                f"Mode: LIVE TRADING\n"
                f"Database: {'OK' if self.database.available else 'ERROR'}\n"
                f"Trading: {'ON' if self.config.trading_enabled else 'PAUSED'}\n"
                f"Positions: {snap.get('total_positions', 0)}/{self.config.max_positions}\n"
                f"Wallet: {snap.get('wallet_balance', 0):.4f}\n"
                f"Available: {snap.get('available_balance', 0):.4f}\n"
                f"Unrealized: {snap.get('unrealized_pnl', 0):.4f}\n"
                f"LONG notional: {snap.get('long_notional', 0):.4f}\n"
                f"SHORT notional: {snap.get('short_notional', 0):.4f}"
            )
        except Exception as exc:
            return f"Không lấy được status: {exc}"

    def positions_text(self) -> str:
        rows = self.position_manager.active_rows()
        if not rows:
            return "📭 Không có vị thế đang quản lý"
        lines = ["📈 VỊ THẾ ĐANG QUẢN LÝ"]
        for row in rows:
            lines.append(
                f"{row.get('symbol')} {row.get('side')} | status={row.get('status')} | "
                f"qty={safe_float(row.get('current_quantity')):.8g} | "
                f"entry={safe_float(row.get('average_entry_price')):.8g} | "
                f"ROI={safe_float(row.get('last_roi_pct')):.2f}% | "
                f"DCA={safe_int(row.get('dca_count'))}/{safe_int(row.get('max_dca_steps'))}"
            )
        return "\n".join(lines)[:4000]

    def config_text(self) -> str:
        return json.dumps(self.config.public_dict(), ensure_ascii=False, indent=2, default=str)[:4000]

    def set_trading_enabled(self, enabled: bool) -> str:
        self.config.trading_enabled = bool(enabled)
        self.database.set_runtime(
            "trading_enabled", {"enabled": self.config.trading_enabled, "at": utc_now().isoformat()}, required=False
        )
        return (
            "▶️ Đã bật mở lệnh mới" if enabled
            else "⏸️ Đã dừng mở lệnh mới; bot vẫn quản lý và đóng vị thế"
        )

    def set_config_value(self, key: str, value: str) -> str:
        blocked = {
            "database_url",
            "telegram_bot_token", "telegram_chat_id",
            "binance_api_key", "binance_api_secret", "dry_run",
        }
        if key not in {f.name for f in fields(self.config)} or key in blocked:
            return f"Không cho phép sửa tham số: {key}"
        old = getattr(self.config, key)
        self.config.update_from_mapping({key: value})
        errors = self.config.validate(require_credentials=False)
        if errors:
            setattr(self.config, key, old)
            return "Giá trị không hợp lệ: " + "; ".join(errors)
        self.database.set_runtime("strategy_config", self.config.public_dict(), required=False)
        return f"✅ {key}: {old!r} → {getattr(self.config, key)!r}"

    def manual_close(self, symbol: str) -> str:
        symbol = symbol.upper()
        row = next((r for r in self.position_manager.active_rows() if str(r.get("symbol")).upper() == symbol), None)
        if not row:
            return f"Không có vị thế {symbol} trong database"
        ok = self.position_manager.close_position(row, "MANUAL_TELEGRAM", allow_reverse=False)
        return f"{'✅' if ok else '❌'} Yêu cầu đóng {symbol}"


def install_signal_handlers(app: TradingBotApplication) -> None:
    def handler(signum: int, _frame: Any) -> None:
        logger.info("Nhận signal %s, đang dừng an toàn", signum)
        app.running = False

    for sig in (os_signal.SIGINT, os_signal.SIGTERM):
        try:
            os_signal.signal(sig, handler)
        except Exception:
            pass


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser(description="EMA + Volume LIVE TRADING PostgreSQL bot")
    parser.add_argument("--check-config", action="store_true", help="Kiểm tra biến môi trường, không kết nối")
    parser.add_argument("--print-config", action="store_true", help="In cấu hình không chứa secret")
    parser.add_argument("--init-db", action="store_true", help="Chỉ tạo/cập nhật schema PostgreSQL")
    args = parser.parse_args()

    config = BotConfig.from_env()
    if args.print_config:
        print(json.dumps(config.public_dict(), ensure_ascii=False, indent=2, default=str))
    if args.check_config:
        errors = config.validate(require_credentials=True)
        if errors:
            print("CONFIG ERROR:")
            for error in errors:
                print("-", error)
            return 2
        print("CONFIG OK")
        return 0
    if args.init_db:
        errors = config.validate(require_credentials=False)
        errors = [e for e in errors if "BINANCE" not in e]
        if errors:
            print("CONFIG ERROR:", "; ".join(errors))
            return 2
        db = DatabaseManager(config)
        db.connect_and_prepare()
        print("DATABASE SCHEMA OK")
        return 0

    app = TradingBotApplication(config)
    install_signal_handlers(app)
    try:
        app.run_forever()
        return 0
    except Exception as exc:
        logger.critical("Bot không thể khởi động: %s\n%s", exc, traceback.format_exc())
        try:
            app.notify(f"❌ BOT KHÔNG THỂ KHỞI ĐỘNG: {exc}")
            app.shutdown()
        except Exception:
            pass
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
