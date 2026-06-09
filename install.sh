#!/bin/bash

echo "================================"
echo "  🤖 إعداد بوت مراقبة الحجم"
echo "================================"
echo ""

mkdir -p volume_bot && cd volume_bot

# جمع البيانات
read -p "🔑 Binance API Key: " API_KEY
read -p "🔐 Binance Secret: " API_SECRET
read -p "🤖 Telegram Bot Token: " TG_TOKEN
read -p "💬 Telegram Chat ID: " TG_CHAT

# حفظ .env
cat > .env << EOF
BINANCE_API_KEY=$API_KEY
BINANCE_SECRET=$API_SECRET
TELEGRAM_TOKEN=$TG_TOKEN
TELEGRAM_CHAT_ID=$TG_CHAT
EOF

# إنشاء requirements.txt
cat > requirements.txt << 'EOF'
ccxt==4.3.89
pandas==2.2.2
python-telegram-bot==21.5
python-dotenv==1.0.1
EOF

# إنشاء bot.py
cat > bot.py << 'EOF'
import ccxt
import pandas as pd
import asyncio
import logging
from telegram import Bot
from datetime import datetime
import time
import os
from dotenv import load_dotenv

load_dotenv()

BINANCE_API_KEY  = os.getenv("BINANCE_API_KEY")
BINANCE_SECRET   = os.getenv("BINANCE_SECRET")
TELEGRAM_TOKEN   = os.getenv("TELEGRAM_TOKEN")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID")

VOLUME_SPIKE_MULTIPLIER = 3.0
CANDLES_LOOKBACK        = 20
PRICE_CHANGE_MAX        = 5.0
PRICE_CHANGE_MIN        = 2.0
CHECK_INTERVAL          = 60
QUOTE_CURRENCY          = "USDC"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.FileHandler("bot.log"), logging.StreamHandler()]
)
log = logging.getLogger(__name__)

exchange = ccxt.binance({
    "apiKey": BINANCE_API_KEY,
    "secret": BINANCE_SECRET,
    "enableRateLimit": True,
})

bot = Bot(token=TELEGRAM_TOKEN)
alerted_symbols = {}


def get_all_symbols():
    markets = exchange.load_markets()
    return [
        s for s in markets
        if s.endswith(f"/{QUOTE_CURRENCY}")
        and markets[s].get("active")
        and markets[s].get("spot")
    ]


def analyze_symbol(symbol):
    try:
        ohlcv = exchange.fetch_ohlcv(symbol, timeframe="5m", limit=CANDLES_LOOKBACK + 1)
        if len(ohlcv) < CANDLES_LOOKBACK:
            return None

        df = pd.DataFrame(ohlcv, columns=["timestamp", "open", "high", "low", "close", "volume"])
        current_candle  = df.iloc[-1]
        previous_candles = df.iloc[:-1]

        avg_volume     = previous_candles["volume"].mean()
        current_volume = current_candle["volume"]
        if avg_volume == 0:
            return None

        volume_ratio  = current_volume / avg_volume
        price_5_ago   = df.iloc[-6]["close"] if len(df) >= 6 else df.iloc[0]["close"]
        current_price = current_candle["close"]
        price_change_pct = abs((current_price - price_5_ago) / price_5_ago * 100)

        return {
            "symbol": symbol,
            "price": current_price,
            "volume_ratio": volume_ratio,
            "price_change_pct": price_change_pct,
        }
    except Exception as e:
        log.debug(f"خطأ في {symbol}: {e}")
        return None


async def send_alert(data, alert_type):
    emoji = "🟡" if alert_type == "accumulation" else "🚀"
    label = "تجميع صامت" if alert_type == "accumulation" else "بداية حركة"
    msg = (
        f"{emoji} *{label}* | `{data['symbol']}`\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"💰 السعر: `{data['price']:.6f}`\n"
        f"📊 الحجم: `{data['volume_ratio']:.1f}x` من المعتاد\n"
        f"📈 تغير السعر: `{data['price_change_pct']:.2f}%`\n"
        f"🕐 {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"⚠️ _هذا رصد تقني وليس نصيحة مالية_"
    )
    await bot.send_message(chat_id=TELEGRAM_CHAT_ID, text=msg, parse_mode="Markdown")
    log.info(f"تنبيه أُرسل: {data['symbol']} ({label})")


def should_alert(symbol):
    now = time.time()
    if now - alerted_symbols.get(symbol, 0) > 1800:
        alerted_symbols[symbol] = now
        return True
    return False


async def run_scan():
    log.info("🔍 بدء فحص السوق...")
    symbols = get_all_symbols()
    log.info(f"إجمالي العملات: {len(symbols)}")

    accumulation_list, pump_list = [], []

    for i, symbol in enumerate(symbols):
        result = analyze_symbol(symbol)
        if result is None:
            continue
        if result["volume_ratio"] >= VOLUME_SPIKE_MULTIPLIER:
            if result["price_change_pct"] < PRICE_CHANGE_MAX:
                accumulation_list.append(result)
            elif result["price_change_pct"] >= PRICE_CHANGE_MIN:
                pump_list.append(result)
        if i % 10 == 0:
            await asyncio.sleep(0.5)

    accumulation_list.sort(key=lambda x: x["volume_ratio"], reverse=True)
    pump_list.sort(key=lambda x: x["volume_ratio"], reverse=True)

    for data in accumulation_list[:5]:
        if should_alert(data["symbol"]):
            await send_alert(data, "accumulation")
            await asyncio.sleep(1)

    for data in pump_list[:5]:
        if should_alert(data["symbol"]):
            await send_alert(data, "pump")
            await asyncio.sleep(1)

    log.info(f"✅ انتهى الفحص | تجميع: {len(accumulation_list)} | حركة: {len(pump_list)}")


async def main():
    log.info("🤖 البوت شغّال...")
    await bot.send_message(
        chat_id=TELEGRAM_CHAT_ID,
        text="✅ *بوت مراقبة الحجم شغّال*\nسأراقب السوق وأنبهك عند اكتشاف أي حركة مشبوهة 👀",
        parse_mode="Markdown"
    )
    while True:
        try:
            await run_scan()
        except Exception as e:
            log.error(f"خطأ: {e}")
        log.info(f"⏳ انتظار {CHECK_INTERVAL} ثانية...")
        await asyncio.sleep(CHECK_INTERVAL)


if __name__ == "__main__":
    asyncio.run(main())
EOF

# إنشاء service
cat > volume_bot.service << EOF
[Unit]
Description=Binance Volume Spike Bot
After=network.target

[Service]
Type=simple
User=$USER
WorkingDirectory=$(pwd)
ExecStart=$(pwd)/venv/bin/python bot.py
Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
EOF

# تثبيت المكتبات
echo ""
echo "📦 تثبيت المكتبات..."
python3 -m venv venv
source venv/bin/activate
pip install -q -r requirements.txt

# تفعيل السيرفس
sudo cp volume_bot.service /etc/systemd/system/
sudo systemctl enable --now volume_bot

echo ""
echo "✅ البوت شغّال! تحقق منه بـ:"
echo "   sudo systemctl status volume_bot"
