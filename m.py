import ccxt
import pandas as pd
import asyncio
import logging
import sqlite3
import time
import os
from telegram import Bot
from datetime import datetime, timezone
from dotenv import load_dotenv

load_dotenv()

# ──────────────────────────────────────────
# إعدادات
# ──────────────────────────────────────────
BINANCE_API_KEY          = os.getenv("BINANCE_API_KEY")
BINANCE_SECRET           = os.getenv("BINANCE_SECRET")
TELEGRAM_TOKEN           = os.getenv("TELEGRAM_TOKEN")
TELEGRAM_CHAT_ID         = os.getenv("TELEGRAM_CHAT_ID")

QUOTE_CURRENCY           = "USDC"
CHECK_INTERVAL           = 45          # ثانية بين كل فحص
ALERT_COOLDOWN           = 900         # 15 دقيقة بين تنبيهين لنفس العملة
MIN_DAILY_VOLUME         = 500_000     # حجم يومي أدنى بـ USDC
BTC_MAX_MOVE_PCT         = 1.0         # لو BTC تحرك أكثر من هيك = تجميد التنبيهات

# ──────────────────────────────────────────
# Logging
# ──────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.FileHandler("bot.log", encoding="utf-8"),
        logging.StreamHandler()
    ]
)
log = logging.getLogger(__name__)

# ──────────────────────────────────────────
# التهيئة
# ──────────────────────────────────────────
exchange = ccxt.binance({
    "apiKey": BINANCE_API_KEY,
    "secret": BINANCE_SECRET,
    "enableRateLimit": True,
})

bot          = Bot(token=TELEGRAM_TOKEN)
alerted_at   = {}   # symbol -> timestamp آخر تنبيه


# ──────────────────────────────────────────
# قاعدة البيانات
# ──────────────────────────────────────────
def init_db():
    conn = sqlite3.connect("alerts.db")
    conn.execute("""
        CREATE TABLE IF NOT EXISTS alerts (
            id          INTEGER PRIMARY KEY AUTOINCREMENT,
            symbol      TEXT,
            price       REAL,
            score       INTEGER,
            vol_ratio   REAL,
            buy_pct     REAL,
            timestamp   TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS results (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            symbol       TEXT,
            alert_price  REAL,
            check_price  REAL,
            change_pct   REAL,
            checked_at   TEXT
        )
    """)
    conn.commit()
    conn.close()


def save_alert(symbol, price, score, vol_ratio, buy_pct):
    conn = sqlite3.connect("alerts.db")
    conn.execute(
        "INSERT INTO alerts (symbol, price, score, vol_ratio, buy_pct, timestamp) VALUES (?,?,?,?,?,?)",
        (symbol, price, score, vol_ratio, buy_pct, datetime.now().isoformat())
    )
    conn.commit()
    conn.close()


def save_result(symbol, alert_price, check_price):
    change = (check_price - alert_price) / alert_price * 100
    conn   = sqlite3.connect("alerts.db")
    conn.execute(
        "INSERT INTO results (symbol, alert_price, check_price, change_pct, checked_at) VALUES (?,?,?,?,?)",
        (symbol, alert_price, check_price, change, datetime.now().isoformat())
    )
    conn.commit()
    conn.close()
    return change


# ──────────────────────────────────────────
# فحص BTC
# ──────────────────────────────────────────
def btc_is_stable():
    try:
        ohlcv = exchange.fetch_ohlcv("BTC/USDC", "1m", limit=4)
        if len(ohlcv) < 3:
            return True
        first = ohlcv[-3][4]
        last  = ohlcv[-1][4]
        move  = abs((last - first) / first * 100)
        if move > BTC_MAX_MOVE_PCT:
            log.info(f"⚠️ BTC يتحرك {move:.2f}% — تجميد التنبيهات")
            return False
        return True
    except Exception as e:
        log.warning(f"تعذّر فحص BTC: {e}")
        return True


# ──────────────────────────────────────────
# جلب العملات
# ──────────────────────────────────────────
def get_all_symbols():
    markets = exchange.load_markets()
    return [
        s for s in markets
        if s.endswith(f"/{QUOTE_CURRENCY}")
        and markets[s].get("active")
        and markets[s].get("spot")
    ]


# ──────────────────────────────────────────
# التحليل الرئيسي
# ──────────────────────────────────────────
def analyze_symbol(symbol):
    try:
        # ── فلتر الحجم اليومي ──
        ticker = exchange.fetch_ticker(symbol)
        if (ticker.get("quoteVolume") or 0) < MIN_DAILY_VOLUME:
            return None

        # ── جلب شموع 1m ──
        ohlcv = exchange.fetch_ohlcv(symbol, "1m", limit=25)
        if len(ohlcv) < 20:
            return None

        df = pd.DataFrame(ohlcv, columns=["ts", "o", "h", "l", "c", "v"])

        score  = 0
        detail = {}

        # ── شرط 1: تسارع الحجم ──
        v1 = df["v"].iloc[-4]
        v2 = df["v"].iloc[-3]
        v3 = df["v"].iloc[-2]
        v4 = df["v"].iloc[-1]
        vol_ratio = v4 / df["v"].iloc[:-1].mean() if df["v"].iloc[:-1].mean() > 0 else 0

        accelerating = (v1 < v2 < v3 < v4) and vol_ratio >= 2.5
        detail["vol_ratio"]    = round(vol_ratio, 1)
        detail["accelerating"] = accelerating
        if accelerating:
            score += 1

        # ── شرط 2: الشموع تغلق في النص العلوي ──
        strong_closes = 0
        for row in df.iloc[-4:-1].itertuples():
            mid = (row.h + row.l) / 2
            if row.c > mid:
                strong_closes += 1
        detail["strong_closes"] = strong_closes
        if strong_closes >= 2:
            score += 1

        # ── شرط 3: قيعان ترتفع (Higher Lows) ──
        lows        = df["l"].iloc[-6:].values
        higher_lows = all(lows[i] >= lows[i - 1] for i in range(1, len(lows)))
        detail["higher_lows"] = higher_lows
        if higher_lows:
            score += 1

        # ── شرط 4: ضغط شراء في Order Book ──
        ob       = exchange.fetch_order_book(symbol, limit=20)
        bid_vol  = sum(x[1] for x in ob["bids"])
        ask_vol  = sum(x[1] for x in ob["asks"])
        total    = bid_vol + ask_vol
        buy_pct  = (bid_vol / total * 100) if total > 0 else 50
        detail["buy_pct"] = round(buy_pct, 1)
        if buy_pct > 65:
            score += 1

        # ── شرط 5: قريب من الاختراق (Coiling) ──
        resistance      = df["h"].iloc[-20:].max()
        current_price   = df["c"].iloc[-1]
        dist_to_res_pct = (resistance - current_price) / current_price * 100
        detail["dist_to_resistance"] = round(dist_to_res_pct, 2)
        detail["resistance"]         = resistance
        if 0 < dist_to_res_pct < 0.8:
            score += 1

        # ── إرجاع النتيجة فقط إذا score >= 4 ──
        if score < 4:
            return None

        return {
            "symbol":   symbol,
            "price":    current_price,
            "score":    score,
            **detail,
        }

    except Exception as e:
        log.debug(f"خطأ في {symbol}: {e}")
        return None


# ──────────────────────────────────────────
# إرسال التنبيه
# ──────────────────────────────────────────
async def send_alert(data):
    stars     = "⭐" * data["score"]
    acc_emoji = "✅" if data["accelerating"]  else "❌"
    hl_emoji  = "✅" if data["higher_lows"]   else "❌"
    sc_emoji  = "✅" if data["strong_closes"] >= 2 else "❌"
    bp_emoji  = "✅" if data["buy_pct"] > 65  else "❌"
    co_emoji  = "✅" if 0 < data["dist_to_resistance"] < 0.8 else "❌"

    msg = (
        f"⚡️ *تجميع مؤكد* | `{data['symbol']}`\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🏆 القوة: {stars}  ({data['score']}/5)\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{acc_emoji} حجم متسارع:      `{data['vol_ratio']}x`\n"
        f"{sc_emoji} شموع قوية:        `{data['strong_closes']}/3`\n"
        f"{hl_emoji} قيعان ترتفع:      `{'نعم' if data['higher_lows'] else 'لا'}`\n"
        f"{bp_emoji} ضغط شراء:         `{data['buy_pct']}%`\n"
        f"{co_emoji} قريب الاختراق:    `{data['dist_to_resistance']}%`\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🎯 مقاومة: `{data['resistance']:.6f}`\n"
        f"💰 السعر:  `{data['price']:.6f}`\n"
        f"🕐 {datetime.now().strftime('%H:%M:%S')}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"⚠️ _رصد تقني فقط، ليس نصيحة مالية_"
    )

    await bot.send_message(chat_id=TELEGRAM_CHAT_ID, text=msg, parse_mode="Markdown")
    log.info(f"✅ تنبيه أُرسل: {data['symbol']} | score={data['score']}")

    # حفظ في DB
    save_alert(data["symbol"], data["price"], data["score"], data["vol_ratio"], data["buy_pct"])

    # جدولة فحص النتيجة بعد 20 دقيقة
    asyncio.create_task(check_result_later(data["symbol"], data["price"]))


# ──────────────────────────────────────────
# تتبع النتيجة بعد 20 دقيقة
# ──────────────────────────────────────────
async def check_result_later(symbol, alert_price):
    await asyncio.sleep(1200)  # 20 دقيقة
    try:
        ticker      = exchange.fetch_ticker(symbol)
        check_price = ticker["last"]
        change      = save_result(symbol, alert_price, check_price)
        emoji       = "🟢" if change > 0 else "🔴"
        await bot.send_message(
            chat_id=TELEGRAM_CHAT_ID,
            text=(
                f"{emoji} *نتيجة التنبيه* | `{symbol}`\n"
                f"سعر التنبيه: `{alert_price:.6f}`\n"
                f"السعر الآن:  `{check_price:.6f}`\n"
                f"التغير:      `{change:+.2f}%` بعد 20 دقيقة"
            ),
            parse_mode="Markdown"
        )
    except Exception as e:
        log.warning(f"فشل فحص النتيجة لـ {symbol}: {e}")


# ──────────────────────────────────────────
# فحص cooldown
# ──────────────────────────────────────────
def can_alert(symbol):
    now = time.time()
    if now - alerted_at.get(symbol, 0) > ALERT_COOLDOWN:
        alerted_at[symbol] = now
        return True
    return False


# ──────────────────────────────────────────
# الفحص الرئيسي
# ──────────────────────────────────────────
async def run_scan():
    log.info("🔍 بدء الفحص...")

    if not btc_is_stable():
        log.info("⏸️ BTC غير مستقر — تأجيل الفحص")
        return

    symbols = get_all_symbols()
    log.info(f"العملات: {len(symbols)}")

    found = []

    for i, symbol in enumerate(symbols):
        result = analyze_symbol(symbol)
        if result:
            found.append(result)
        if i % 15 == 0:
            await asyncio.sleep(0.3)

    # ترتيب بالأقوى أولاً
    found.sort(key=lambda x: (x["score"], x["vol_ratio"]), reverse=True)

    sent = 0
    for data in found:
        if sent >= 3:   # أقصى 3 تنبيهات بكل فحص
            break
        if can_alert(data["symbol"]):
            await send_alert(data)
            await asyncio.sleep(1.5)
            sent += 1

    log.info(f"✅ انتهى الفحص | إشارات قوية: {len(found)} | أُرسل: {sent}")


# ──────────────────────────────────────────
# الحلقة الرئيسية
# ──────────────────────────────────────────
async def main():
    init_db()
    log.info("🤖 البوت شغّال...")

    await bot.send_message(
        chat_id=TELEGRAM_CHAT_ID,
        text=(
            "✅ *بوت التجميع شغّال*\n"
            "━━━━━━━━━━━━━━━━\n"
            "🎯 الشروط: 4 من 5 لازم تتحقق\n"
            "⏱️ فحص كل 45 ثانية\n"
            "📊 متابعة النتيجة بعد 20 دقيقة\n"
            "━━━━━━━━━━━━━━━━\n"
            "👀 أراقب السوق..."
        ),
        parse_mode="Markdown"
    )

    while True:
        try:
            await run_scan()
        except Exception as e:
            log.error(f"خطأ: {e}")
        log.info(f"⏳ انتظار {CHECK_INTERVAL}ث...")
        await asyncio.sleep(CHECK_INTERVAL)


if __name__ == "__main__":
    asyncio.run(main())
