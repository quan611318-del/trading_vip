#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MAIN ENTRY POINT - Live Trading Bot
====================================
File này là đầu vào chính để chạy bot. Nó load biến môi trường từ .env,
khởi tạo cấu hình, bắt tay với database và Binance, rồi chạy vòng lặp chính.

Cách chạy:
    python main.py

Các tham số dòng lệnh (tuỳ chọn):
    --check-config   : Kiểm tra biến môi trường, không kết nối
    --print-config   : In cấu hình (ẩn secret)
    --init-db        : Chỉ tạo schema database, không chạy bot
"""

import sys
import logging
import argparse
import traceback

# Thư viện dotenv để đọc file .env
try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

# Import toàn bộ logic từ file chính
# (Giả sử file logic được đặt cùng thư mục với tên trading_bot_live.py)
from trading_bot_lib import (
    BotConfig,
    TradingBotApplication,
    DatabaseManager,
    install_signal_handlers,
    logger,
)


def parse_arguments():
    parser = argparse.ArgumentParser(description="EMA + Volume LIVE TRADING PostgreSQL bot")
    parser.add_argument(
        "--check-config",
        action="store_true",
        help="Kiểm tra biến môi trường, không kết nối"
    )
    parser.add_argument(
        "--print-config",
        action="store_true",
        help="In cấu hình không chứa secret"
    )
    parser.add_argument(
        "--init-db",
        action="store_true",
        help="Chỉ tạo/cập nhật schema PostgreSQL, không chạy bot"
    )
    return parser.parse_args()


def run_check_config(config: BotConfig) -> int:
    """Chỉ kiểm tra cấu hình, không kết nối gì."""
    errors = config.validate(require_credentials=True)
    if errors:
        print("❌ CONFIG ERROR:")
        for error in errors:
            print(f"  - {error}")
        return 2
    print("✅ CONFIG OK")
    return 0


def run_init_db(config: BotConfig) -> int:
    """Chỉ tạo schema database."""
    errors = config.validate(require_credentials=False)
    # Bỏ qua lỗi thiếu Binance API key khi chỉ init DB
    errors = [e for e in errors if "BINANCE" not in e]
    if errors:
        print("❌ CONFIG ERROR:", "; ".join(errors))
        return 2
    try:
        db = DatabaseManager(config)
        db.connect_and_prepare()
        print("✅ DATABASE SCHEMA OK")
        return 0
    except Exception as e:
        print(f"❌ Không thể tạo schema DB: {e}")
        return 1


def main() -> int:
    # Load biến môi trường từ .env nếu có
    load_dotenv()

    # Parse tham số
    args = parse_arguments()

    # Tạo config từ env
    config = BotConfig.from_env()

    # Xử lý các lệnh đặc biệt
    if args.print_config:
        import json
        print(json.dumps(config.public_dict(), ensure_ascii=False, indent=2, default=str))
        return 0

    if args.check_config:
        return run_check_config(config)

    if args.init_db:
        return run_init_db(config)

    # --- Chạy bot thực sự ---
    logger.info("🚀 Khởi động Live Trading Bot...")
    try:
        app = TradingBotApplication(config)
        install_signal_handlers(app)

        # Khởi chạy vòng lặp chính
        app.run_forever()
        return 0

    except KeyboardInterrupt:
        logger.info("⏹️ Người dùng dừng bot (Ctrl+C).")
        return 0

    except Exception as exc:
        logger.critical("❌ Bot gặp lỗi nghiêm trọng: %s", exc)
        logger.critical(traceback.format_exc())
        # Cố gắng gửi thông báo qua Telegram nếu có thể
        try:
            temp_app = TradingBotApplication(config)
            temp_app.notify(f"❌ BOT CRASH: {exc}")
            temp_app.shutdown()
        except Exception:
            pass
        return 1


if __name__ == "__main__":
    sys.exit(main())
