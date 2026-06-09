import ccxt
import pandas as pd
import numpy as np
import asyncio
import logging
import sqlite3
import time
import os
import feedparser
import json
import hashlib
import statistics
from telegram import Bot
from datetime import datetime, timezone, timedelta
from dotenv import load_dotenv
from collections import defaultdict, deque

load_dotenv()

# ──────────────────────────────────────────
# إعدادات
# ──────────────────────────────────────────
BINANCE_API_KEY      = os.getenv("BINANCE_API_KEY")
BINANCE_SECRET       = os.getenv("BINANCE_SECRET")
TELEGRAM_TOKEN       = os.getenv("TELEGRAM_TOKEN")
TELEGRAM_CHAT_ID     = os.getenv("TELEGRAM_CHAT_ID")

QUOTE_CURRENCY       = "USDC"
CHECK_INTERVAL       = 45
ALERT_COOLDOWN       = 900
MIN_DAILY_VOLUME     = 500_000
BTC_MAX_MOVE_PCT     = 1.0
WHALE_MIN_USDC       = 4_000
WHALE_STRONG_USDC    = 8_000
WHALE_BUY_RATIO      = 0.60
WHALE_MAX_PRICE      = 1_000
EMERGENCY_BTC_DROP   = 4.0
RADAR_INTERVAL       = 3600
MARKET_MOOD_INTERVAL = 14400
MORNING_HOUR         = 8
WEEKLY_DAY           = 6

# Paper Trading
PAPER_CAPITAL        = 1_000
PAPER_RISK_PCT       = 0.02

# ── فلتر الوقت الهادئ ──
QUIET_HOURS_START    = 1
QUIET_HOURS_END      = 5
QUIET_VOLUME_MULT    = 0.5

# ── Smart Cooldown ──
COOLDOWN_SCORE_6     = 300
COOLDOWN_SCORE_5     = 600
COOLDOWN_SCORE_4     = 900

# ── Trailing Stop ──
TRAILING_STOP_PCT    = 0.015
TRAILING_CHECK_SEC   = 60

# ── Volume Profile ──
VOLUME_PROFILE_BINS  = 20

# ── AI Score Weights ──
AI_WEIGHTS = {
    "vol_ratio":     0.20,
    "strong_closes": 0.15,
    "higher_lows":   0.15,
    "buy_pct":       0.15,
    "dist_res":      0.10,
    "whale_signal":  0.15,
    "rsi":           0.05,
    "macd":          0.05,
}

# قطاعات العملات
SECTORS = {
    "AI":      ["FET","AGIX","OCEAN","NMR","RLC","CTXC","RNDR","WLD"],
    "Gaming":  ["AXS","SAND","MANA","ENJ","GALA","IMX","MAGIC","HOOK"],
    "DeFi":    ["UNI","AAVE","COMP","CRV","SNX","BAL","YFI","SUSHI"],
    "Layer1":  ["SOL","AVAX","DOT","ATOM","NEAR","FTM","ONE","ALGO"],
    "Layer2":  ["MATIC","ARB","OP","IMX","ZK","STRK","MANTA","BLUR"],
}

# ──────────────────────────────────────────
# ⚡ إعدادات السرعة — الجديدة
# ──────────────────────────────────────────
# عدد العملات تُفحص بالتوازي في نفس الوقت
PARALLEL_WORKERS     = 30
# حد أقصى للإشارات المرسلة لكل دورة
MAX_ALERTS_PER_SCAN  = 3
# مؤقت كاش للـ markets (5 دقائق)
MARKETS_CACHE_TTL    = 300
# مؤقت كاش للـ ticker (30 ثانية)
TICKER_CACHE_TTL     = 30

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
    "apiKey":          BINANCE_API_KEY,
    "secret":          BINANCE_SECRET,
    "enableRateLimit": True,
})

bot                  = Bot(token=TELEGRAM_TOKEN)
alerted_at           = {}
whale_alerted_at     = {}
breakout_alerted_at  = {}
emergency_mode       = False
last_radar_time      = 0
last_mood_time       = 0
last_morning_date    = None
last_weekly_date     = None
daily_alerts         = []
whale_monitoring     = True

# ── Trailing Stop tracker ──
trailing_stops       = {}

# ── Price history للـ Volume Profile ──
price_history        = defaultdict(deque)

# ── Correlation cache ──
correlation_cache    = {}
correlation_ts       = 0

# ── Performance tracker ──
signal_performance   = defaultdict(list)

# ── Market microstructure ──
spread_history       = defaultdict(list)

# ── Momentum tracker ──
momentum_scores      = {}

# ── Divergence tracker ──
divergence_cache     = {}

# ── Multi-timeframe cache ──
mtf_cache            = {}
mtf_cache_ts         = {}

# ── Heatmap data ──
sector_performance   = defaultdict(list)

# ── Anomaly detection ──
volume_baseline      = defaultdict(list)

# ── Liquidity zones ──
liquidity_zones      = defaultdict(list)

# ── Fear & Greed ──
fear_greed_score     = 50
last_fg_update       = 0

# ──────────────────────────────────────────
# ⚡ كاش السرعة — الجديد
# ──────────────────────────────────────────
_markets_cache = {"data": [], "ts": 0}
_ticker_cache  = {}   # symbol -> (ticker_data, timestamp)
_scan_semaphore = None  # يُهيَّأ في main()


def get_semaphore():
    global _scan_semaphore
    if _scan_semaphore is None:
        _scan_semaphore = asyncio.Semaphore(PARALLEL_WORKERS)
    return _scan_semaphore


async def get_all_symbols_cached():
    """جلب العملات مع كاش 5 دقائق — لا تحميل كل مرة"""
    now = time.time()
    if now - _markets_cache["ts"] < MARKETS_CACHE_TTL and _markets_cache["data"]:
        return _markets_cache["data"]
    symbols = await asyncio.to_thread(get_all_symbols)
    _markets_cache["data"] = symbols
    _markets_cache["ts"]   = now
    log.info(f"🔄 Markets cache updated: {len(symbols)} symbols")
    return symbols


async def fetch_ticker_cached(symbol):
    """جلب ticker مع كاش 30 ثانية"""
    now = time.time()
    if symbol in _ticker_cache:
        data, ts = _ticker_cache[symbol]
        if now - ts < TICKER_CACHE_TTL:
            return data
    ticker = await asyncio.to_thread(exchange.fetch_ticker, symbol)
    _ticker_cache[symbol] = (ticker, now)
    return ticker


# ──────────────────────────────────────────
# قاعدة البيانات
# ──────────────────────────────────────────
def init_db():
    conn = sqlite3.connect("alerts.db")
    conn.execute("""
        CREATE TABLE IF NOT EXISTS alerts (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            symbol       TEXT,
            price        REAL,
            score        INTEGER,
            vol_ratio    REAL,
            buy_pct      REAL,
            rsi          REAL,
            macd_signal  TEXT,
            ai_score     REAL,
            timestamp    TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS results (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            symbol       TEXT,
            alert_price  REAL,
            check_price  REAL,
            change_pct   REAL,
            max_gain     REAL DEFAULT 0,
            checked_at   TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS coin_reputation (
            symbol       TEXT PRIMARY KEY,
            total        INTEGER DEFAULT 0,
            success      INTEGER DEFAULT 0,
            avg_profit   REAL    DEFAULT 0.0,
            max_profit   REAL    DEFAULT 0.0,
            avg_ai_score REAL    DEFAULT 0.0,
            streak       INTEGER DEFAULT 0,
            last_alert   TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS paper_trades (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            symbol       TEXT,
            entry_price  REAL,
            exit_price   REAL,
            qty          REAL,
            pnl          REAL,
            max_gain     REAL DEFAULT 0,
            exit_reason  TEXT DEFAULT 'timeout',
            status       TEXT DEFAULT 'open',
            opened_at    TEXT,
            closed_at    TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS whale_trades (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            symbol       TEXT,
            side         TEXT,
            amount_usdc  REAL,
            price        REAL,
            level        TEXT,
            timestamp    TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS sr_levels (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            symbol       TEXT,
            level_type   TEXT,
            price        REAL,
            strength     INTEGER,
            timestamp    TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS anomalies (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            symbol       TEXT,
            anomaly_type TEXT,
            value        REAL,
            baseline     REAL,
            timestamp    TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS correlation_log (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            symbol1      TEXT,
            symbol2      TEXT,
            correlation  REAL,
            timestamp    TEXT
        )
    """)
    conn.commit()
    conn.close()


def save_alert(symbol, price, score, vol_ratio, buy_pct, rsi=None, macd_signal=None, ai_score=None):
    conn = sqlite3.connect("alerts.db")
    conn.execute(
        "INSERT INTO alerts (symbol,price,score,vol_ratio,buy_pct,rsi,macd_signal,ai_score,timestamp) VALUES (?,?,?,?,?,?,?,?,?)",
        (symbol, price, score, vol_ratio, buy_pct, rsi, macd_signal, ai_score, datetime.now().isoformat())
    )
    conn.execute("""
        INSERT INTO coin_reputation (symbol, total, last_alert, avg_ai_score)
        VALUES (?, 1, ?, ?)
        ON CONFLICT(symbol) DO UPDATE SET
            total        = total + 1,
            last_alert   = excluded.last_alert,
            avg_ai_score = (avg_ai_score * (total-1) + excluded.avg_ai_score) / total
    """, (symbol, datetime.now().isoformat(), ai_score or 0))
    conn.commit()
    conn.close()


def save_result(symbol, alert_price, check_price, max_gain=0):
    change = (check_price - alert_price) / alert_price * 100
    conn   = sqlite3.connect("alerts.db")
    conn.execute(
        "INSERT INTO results (symbol,alert_price,check_price,change_pct,max_gain,checked_at) VALUES (?,?,?,?,?,?)",
        (symbol, alert_price, check_price, change, max_gain, datetime.now().isoformat())
    )
    if change > 0:
        conn.execute("""
            UPDATE coin_reputation SET
                success    = success + 1,
                avg_profit = (avg_profit * (total-1) + ?) / total,
                max_profit = MAX(max_profit, ?),
                streak     = streak + 1
            WHERE symbol = ?
        """, (change, change, symbol))
    else:
        conn.execute("UPDATE coin_reputation SET streak = 0 WHERE symbol = ?", (symbol,))
    conn.commit()
    conn.close()
    signal_performance[symbol].append(change)
    return change


def get_reputation(symbol):
    conn = sqlite3.connect("alerts.db")
    row  = conn.execute(
        "SELECT total, success, avg_profit, last_alert, max_profit, avg_ai_score, streak FROM coin_reputation WHERE symbol=?",
        (symbol,)
    ).fetchone()
    conn.close()
    if not row or row[0] == 0:
        return None
    total, success, avg_profit, last_alert, max_profit, avg_ai_score, streak = row
    rate = success / total * 100
    if rate >= 70:
        badge = "🥇 موثوقة"
    elif rate >= 50:
        badge = "🥈 متوسطة"
    else:
        badge = "🥉 ضعيفة"
    streak_txt = f" 🔥×{streak}" if streak >= 3 else ""
    return {
        "total": total, "success": success,
        "rate": round(rate, 1), "avg_profit": round(avg_profit, 2),
        "max_profit": round(max_profit, 2),
        "avg_ai_score": round(avg_ai_score, 3),
        "last_alert": last_alert, "badge": badge,
        "streak": streak, "streak_txt": streak_txt,
    }


def get_daily_stats():
    conn  = sqlite3.connect("alerts.db")
    today = datetime.now().date().isoformat()
    rows  = conn.execute(
        "SELECT change_pct, symbol, max_gain FROM results WHERE checked_at LIKE ?",
        (f"{today}%",)
    ).fetchall()
    conn.close()
    if not rows:
        return None
    profits = [r[0] for r in rows]
    success = sum(1 for p in profits if p > 0)
    best    = max(rows, key=lambda x: x[0])
    worst   = min(rows, key=lambda x: x[0])
    avg_max = statistics.mean([r[2] for r in rows if r[2]]) if rows else 0
    return {
        "total": len(profits), "success": success,
        "rate": round(success / len(profits) * 100, 1),
        "best_symbol": best[1], "best_pct": round(best[0], 2),
        "worst_symbol": worst[1], "worst_pct": round(worst[0], 2),
        "avg_max_gain": round(avg_max, 2),
    }


def get_weekly_stats():
    conn  = sqlite3.connect("alerts.db")
    since = (datetime.now() - timedelta(days=7)).isoformat()
    rows  = conn.execute(
        "SELECT change_pct, symbol, alert_price, check_price, max_gain FROM results WHERE checked_at >= ?",
        (since,)
    ).fetchall()
    conn.close()
    if not rows:
        return None
    profits = [r[0] for r in rows]
    success = sum(1 for p in profits if p > 0)
    best    = max(rows, key=lambda x: x[0])
    total_gain = sum(profits)
    return {
        "total": len(profits), "success": success,
        "rate": round(success / len(profits) * 100, 1),
        "best_symbol": best[1],
        "best_entry": best[2], "best_exit": best[3],
        "best_pct": round(best[0], 2),
        "total_gain": round(total_gain, 2),
        "avg_max_gain": round(statistics.mean([r[4] for r in rows if r[4]]), 2) if rows else 0,
    }


# ──────────────────────────────────────────
# المؤشرات التقنية
# ──────────────────────────────────────────
def calc_rsi(closes, period=14):
    if len(closes) < period + 1:
        return None
    deltas = np.diff(closes)
    gains  = np.where(deltas > 0, deltas, 0)
    losses = np.where(deltas < 0, -deltas, 0)
    avg_gain = np.mean(gains[:period])
    avg_loss = np.mean(losses[:period])
    if avg_loss == 0:
        return 100.0
    for i in range(period, len(deltas)):
        avg_gain = (avg_gain * (period - 1) + gains[i]) / period
        avg_loss = (avg_loss * (period - 1) + losses[i]) / period
    rs  = avg_gain / avg_loss if avg_loss > 0 else 0
    rsi = 100 - (100 / (1 + rs))
    return round(rsi, 2)


def calc_stoch_rsi(closes, rsi_period=14, stoch_period=14):
    rsi_values = []
    for i in range(rsi_period, len(closes)):
        r = calc_rsi(closes[max(0, i-rsi_period*2):i+1], rsi_period)
        if r is not None:
            rsi_values.append(r)
    if len(rsi_values) < stoch_period:
        return None, None
    recent = rsi_values[-stoch_period:]
    mn, mx = min(recent), max(recent)
    if mx == mn:
        return 50.0, 50.0
    k = (rsi_values[-1] - mn) / (mx - mn) * 100
    d = np.mean([
        (rsi_values[-(i+1)] - mn) / (mx - mn) * 100
        for i in range(min(3, len(rsi_values)))
    ])
    return round(k, 2), round(d, 2)


def calc_ema(values, period):
    ema = [values[0]]
    k   = 2 / (period + 1)
    for v in values[1:]:
        ema.append(v * k + ema[-1] * (1 - k))
    return ema


def calc_macd(closes, fast=12, slow=26, signal=9):
    if len(closes) < slow + signal:
        return None
    ema_fast    = calc_ema(closes, fast)
    ema_slow    = calc_ema(closes, slow)
    macd_line   = [f - s for f, s in zip(ema_fast[slow-fast:], ema_slow)]
    signal_line = calc_ema(macd_line, signal)
    histogram   = [m - s for m, s in zip(macd_line[-len(signal_line):], signal_line)]
    current_hist = histogram[-1]
    prev_hist    = histogram[-2] if len(histogram) > 1 else 0
    macd_cross   = (
        macd_line[-1] > signal_line[-1] and macd_line[-2] <= signal_line[-2]
        if len(macd_line) > 1 and len(signal_line) > 1 else False
    )
    return {
        "macd":      round(macd_line[-1], 6),
        "signal":    round(signal_line[-1], 6),
        "histogram": round(current_hist, 6),
        "prev_hist": round(prev_hist, 6),
        "bullish":   current_hist > 0 and current_hist > prev_hist,
        "cross":     macd_cross,
        "diverging": current_hist > prev_hist,
    }


def calc_bollinger(closes, period=20, std_dev=2):
    if len(closes) < period:
        return None
    recent = closes[-period:]
    mid    = np.mean(recent)
    std    = np.std(recent)
    upper  = mid + std_dev * std
    lower  = mid - std_dev * std
    bw     = (upper - lower) / mid * 100
    price  = closes[-1]
    pct_b  = (price - lower) / (upper - lower) * 100 if upper != lower else 50
    squeeze = bw < 2.0
    return {
        "upper": round(upper, 6), "mid": round(mid, 6), "lower": round(lower, 6),
        "bandwidth": round(bw, 3), "pct_b": round(pct_b, 1),
        "squeeze": squeeze, "above_mid": price > mid,
    }


def calc_fibonacci(df):
    high    = df["h"].max()
    low     = df["l"].min()
    diff    = high - low
    current = df["c"].iloc[-1]
    levels  = {
        "0.0":   round(high, 6),
        "23.6":  round(high - 0.236 * diff, 6),
        "38.2":  round(high - 0.382 * diff, 6),
        "50.0":  round(high - 0.500 * diff, 6),
        "61.8":  round(high - 0.618 * diff, 6),
        "78.6":  round(high - 0.786 * diff, 6),
        "100.0": round(low, 6),
    }
    supports       = {k: v for k, v in levels.items() if v < current}
    nearest_support = max(supports.values()) if supports else low
    dist_to_support = (current - nearest_support) / current * 100
    return {
        "levels": levels,
        "nearest_support": nearest_support,
        "dist_to_support": round(dist_to_support, 2),
        "is_near_support": dist_to_support < 1.0,
    }


def calc_volume_profile(df, bins=VOLUME_PROFILE_BINS):
    prices  = df["c"].values
    volumes = df["v"].values
    mn, mx  = prices.min(), prices.max()
    if mx == mn:
        return None
    bin_size = (mx - mn) / bins
    profile  = defaultdict(float)
    for p, v in zip(prices, volumes):
        bucket = int((p - mn) / bin_size)
        bucket = min(bucket, bins - 1)
        profile[bucket] += v
    poc_bucket = max(profile, key=profile.get)
    poc_price  = round(mn + (poc_bucket + 0.5) * bin_size, 6)
    total_vol  = sum(profile.values())
    target_vol = total_vol * 0.70
    sorted_b   = sorted(profile.items(), key=lambda x: x[1], reverse=True)
    cumvol = 0
    va_buckets = []
    for b, v in sorted_b:
        cumvol += v
        va_buckets.append(b)
        if cumvol >= target_vol:
            break
    va_high = round(mn + (max(va_buckets) + 1) * bin_size, 6)
    va_low  = round(mn + min(va_buckets) * bin_size, 6)
    current = df["c"].iloc[-1]
    return {
        "poc": poc_price,
        "va_high": va_high,
        "va_low": va_low,
        "above_poc": current > poc_price,
        "in_value_area": va_low <= current <= va_high,
        "dist_to_poc": round((current - poc_price) / poc_price * 100, 2),
    }


def detect_rsi_divergence(df):
    closes = df["c"].values.tolist()
    if len(closes) < 30:
        return None
    rsi_values = []
    for i in range(14, len(closes)):
        r = calc_rsi(closes[:i+1])
        if r:
            rsi_values.append(r)
    if len(rsi_values) < 10:
        return None
    price_lows = []
    rsi_lows   = []
    for i in range(1, min(10, len(closes)-1)):
        if closes[-i] < closes[-i-1] and closes[-i] < closes[-i+1] if i > 0 else True:
            price_lows.append((i, closes[-i]))
    for i in range(1, min(10, len(rsi_values)-1)):
        if rsi_values[-i] < rsi_values[-i-1] and rsi_values[-i] < rsi_values[-i+1] if i > 0 else True:
            rsi_lows.append((i, rsi_values[-i]))
    if len(price_lows) >= 2 and len(rsi_lows) >= 2:
        price_falling = price_lows[0][1] < price_lows[1][1]
        rsi_rising    = rsi_lows[0][1] > rsi_lows[1][1]
        if price_falling and rsi_rising:
            return {"type": "bullish", "strength": "قوي 🔥" if rsi_lows[0][1] < 40 else "معتدل"}
    return None


def get_mtf_trend(symbol):
    trends = {}
    for tf in ["1m", "5m", "15m"]:
        try:
            cache_key = f"{symbol}_{tf}"
            now = time.time()
            if now - mtf_cache_ts.get(cache_key, 0) < 120:
                df = mtf_cache.get(cache_key)
            else:
                ohlcv = exchange.fetch_ohlcv(symbol, tf, limit=50)
                if len(ohlcv) < 20:
                    continue
                df = pd.DataFrame(ohlcv, columns=["ts","o","h","l","c","v"])
                mtf_cache[cache_key]    = df
                mtf_cache_ts[cache_key] = now
            ema9  = calc_ema(df["c"].tolist(), 9)[-1]
            ema21 = calc_ema(df["c"].tolist(), 21)[-1]
            trend = "🟢 صاعد" if ema9 > ema21 else "🔴 هابط"
            trends[tf] = trend
        except:
            continue
    aligned = len(set(trends.values())) == 1 and "🟢 صاعد" in trends.values()
    return {"trends": trends, "aligned": aligned, "all_bullish": aligned}


def detect_support_resistance(df):
    highs   = df["h"].values
    lows    = df["l"].values
    closes  = df["c"].values
    current = closes[-1]
    resistances = []
    supports    = []
    for i in range(2, len(highs) - 2):
        if highs[i] > highs[i-1] and highs[i] > highs[i+1] and highs[i] > highs[i-2] and highs[i] > highs[i+2]:
            resistances.append(highs[i])
        if lows[i] < lows[i-1] and lows[i] < lows[i+1] and lows[i] < lows[i-2] and lows[i] < lows[i+2]:
            supports.append(lows[i])
    res_above   = [r for r in resistances if r > current]
    nearest_res = min(res_above) if res_above else df["h"].max()
    sup_below   = [s for s in supports if s < current]
    nearest_sup = max(sup_below) if sup_below else df["l"].min()
    risk_reward = ((nearest_res - current) / (current - nearest_sup)) if (current - nearest_sup) > 0 else 0
    return {
        "resistance":  round(nearest_res, 6),
        "support":     round(nearest_sup, 6),
        "risk_reward": round(risk_reward, 2),
        "good_rr":     risk_reward >= 2.0,
        "dist_to_res": round((nearest_res - current) / current * 100, 2),
        "dist_to_sup": round((current - nearest_sup) / current * 100, 2),
    }


def detect_liquidity_zones(symbol):
    try:
        ob        = exchange.fetch_order_book(symbol, limit=50)
        bids      = ob["bids"]
        asks      = ob["asks"]
        bid_walls = sorted(bids, key=lambda x: x[1], reverse=True)[:3]
        ask_walls = sorted(asks, key=lambda x: x[1], reverse=True)[:3]
        total_bid = sum(x[1] for x in bids[:20])
        total_ask = sum(x[1] for x in asks[:20])
        imbalance = total_bid / total_ask if total_ask > 0 else 1
        return {
            "bid_walls":   [(round(p, 6), round(s, 2)) for p, s in bid_walls],
            "ask_walls":   [(round(p, 6), round(s, 2)) for p, s in ask_walls],
            "imbalance":   round(imbalance, 2),
            "bullish_liq": imbalance > 1.5,
        }
    except:
        return None


def detect_anomaly(symbol, current_vol, current_price):
    anomalies = []
    if len(volume_baseline[symbol]) < 20:
        volume_baseline[symbol].append(current_vol)
        return []
    baseline_mean = statistics.mean(volume_baseline[symbol])
    baseline_std  = statistics.stdev(volume_baseline[symbol]) if len(volume_baseline[symbol]) > 1 else 1
    if baseline_std > 0:
        z_score = (current_vol - baseline_mean) / baseline_std
        if z_score > 3:
            anomalies.append({
                "type": "volume_spike",
                "msg":  f"⚡ شذوذ حجم! Z={z_score:.1f} — {current_vol:.0f} vs معدل {baseline_mean:.0f}",
                "severity": "high" if z_score > 5 else "medium",
            })
    volume_baseline[symbol].append(current_vol)
    if len(volume_baseline[symbol]) > 100:
        volume_baseline[symbol].pop(0)
    return anomalies


def analyze_microstructure(symbol):
    try:
        ob = exchange.fetch_order_book(symbol, limit=10)
        if not ob["bids"] or not ob["asks"]:
            return None
        best_bid = ob["bids"][0][0]
        best_ask = ob["asks"][0][0]
        spread   = (best_ask - best_bid) / best_bid * 100
        spread_history[symbol].append(spread)
        if len(spread_history[symbol]) > 50:
            spread_history[symbol].pop(0)
        avg_spread   = statistics.mean(spread_history[symbol])
        tight_spread = spread < avg_spread * 0.5
        depth_bids   = sum(x[1] * x[0] for x in ob["bids"][:5])
        depth_asks   = sum(x[1] * x[0] for x in ob["asks"][:5])
        depth_ratio  = depth_bids / depth_asks if depth_asks > 0 else 1
        return {
            "spread":       round(spread, 4),
            "avg_spread":   round(avg_spread, 4),
            "tight_spread": tight_spread,
            "depth_ratio":  round(depth_ratio, 2),
            "bullish_depth": depth_ratio > 1.3,
        }
    except:
        return None


def calc_ai_score(data):
    score = 0.0
    if data.get("accelerating"):
        score += AI_WEIGHTS["vol_ratio"] * min(data.get("vol_ratio", 1) / 5, 1)
    strong = data.get("strong_closes", 0) / 3
    score  += AI_WEIGHTS["strong_closes"] * strong
    if data.get("higher_lows"):
        score += AI_WEIGHTS["higher_lows"]
    bp = max(0, (data.get("buy_pct", 50) - 50) / 50)
    score += AI_WEIGHTS["buy_pct"] * bp
    dist = data.get("dist_to_resistance", 5)
    if 0 < dist < 0.8:
        score += AI_WEIGHTS["dist_res"] * (1 - dist / 0.8)
    if data.get("whale_signal"):
        score += AI_WEIGHTS["whale_signal"]
    rsi = data.get("rsi")
    if rsi and 50 < rsi < 70:
        score += AI_WEIGHTS["rsi"] * ((rsi - 50) / 20)
    macd = data.get("macd_data")
    if macd and macd.get("bullish"):
        score += AI_WEIGHTS["macd"]
        if macd.get("cross"):
            score += AI_WEIGHTS["macd"] * 0.5
    if data.get("bb_squeeze"):
        score += 0.05
    if data.get("mtf_aligned"):
        score += 0.05
    if data.get("fib_near_support"):
        score += 0.03
    if data.get("rsi_divergence"):
        score += 0.05
    if data.get("good_rr"):
        score += 0.03
    if data.get("bullish_liq"):
        score += 0.02
    return round(min(score, 1.0), 3)


# ──────────────────────────────────────────
# Trailing Stop
# ──────────────────────────────────────────
async def trailing_stop_loop():
    log.info("📐 بدأ Trailing Stop Loop...")
    while True:
        try:
            symbols_to_remove = []
            for symbol, ts_data in list(trailing_stops.items()):
                try:
                    ticker  = await asyncio.to_thread(exchange.fetch_ticker, symbol)
                    current = ticker["last"]
                    peak    = ts_data["peak"]
                    stop    = ts_data["stop"]
                    entry   = ts_data["entry"]
                    if current > peak:
                        trailing_stops[symbol]["peak"] = current
                        trailing_stops[symbol]["stop"] = current * (1 - TRAILING_STOP_PCT)
                        new_stop = trailing_stops[symbol]["stop"]
                        gain_pct = (current - entry) / entry * 100
                        log.info(f"📐 Trailing {symbol}: peak={current:.6f} | stop={new_stop:.6f} | gain={gain_pct:.2f}%")
                    elif current <= stop:
                        gain_pct = (current - entry) / entry * 100
                        peak_pct = (peak - entry) / entry * 100
                        emoji    = "🟢" if gain_pct > 0 else "🔴"
                        await bot.send_message(
                            chat_id=TELEGRAM_CHAT_ID,
                            text=(
                                f"📐 *Trailing Stop مُفعَّل* | `{symbol}`\n"
                                f"━━━━━━━━━━━━━━━━━━━━\n"
                                f"دخول:    `{entry:.6f}`\n"
                                f"قمة:     `{peak:.6f}` *(+{peak_pct:.2f}%)*\n"
                                f"خروج:    `{current:.6f}`\n"
                                f"{emoji} التغير: `{gain_pct:+.2f}%`\n"
                                f"━━━━━━━━━━━━━━━━━━━━\n"
                                f"⚠️ _رصد تقني فقط_"
                            ),
                            parse_mode="Markdown"
                        )
                        symbols_to_remove.append(symbol)
                        result = paper_close(symbol, current, reason="trailing_stop")
                        if result:
                            await send_paper_update(symbol, result, action="close")
                except Exception as e:
                    log.debug(f"Trailing {symbol}: {e}")
            for s in symbols_to_remove:
                trailing_stops.pop(s, None)
        except Exception as e:
            log.warning(f"خطأ Trailing Stop: {e}")
        await asyncio.sleep(TRAILING_CHECK_SEC)


# ──────────────────────────────────────────
# Fear & Greed
# ──────────────────────────────────────────
def update_fear_greed():
    global fear_greed_score, last_fg_update
    now = time.time()
    if now - last_fg_update < 1800:
        return fear_greed_score
    try:
        ohlcv       = exchange.fetch_ohlcv("BTC/USDC", "1h", limit=24)
        df          = pd.DataFrame(ohlcv, columns=["ts","o","h","l","c","v"])
        btc_24h     = (df["c"].iloc[-1] - df["c"].iloc[0]) / df["c"].iloc[0] * 100
        avg_vol_early = df["v"].iloc[:12].mean()
        avg_vol_late  = df["v"].iloc[12:].mean()
        vol_trend   = avg_vol_late / avg_vol_early if avg_vol_early > 0 else 1
        rsi         = calc_rsi(df["c"].tolist()) or 50
        fg          = 50 + btc_24h * 3 + (vol_trend - 1) * 20 + (rsi - 50) * 0.5
        fg          = max(0, min(100, fg))
        fear_greed_score = round(fg)
        last_fg_update   = now
        return fg
    except:
        return fear_greed_score


def get_fg_label(score):
    if score >= 75:   return f"😈 جشع شديد ({score})"
    if score >= 55:   return f"😏 جشع ({score})"
    if score >= 45:   return f"😐 محايد ({score})"
    if score >= 25:   return f"😨 خوف ({score})"
    return f"😱 خوف شديد ({score})"


# ──────────────────────────────────────────
# Sector Heatmap
# ──────────────────────────────────────────
async def send_sector_heatmap():
    try:
        lines = []
        for sector, coins in SECTORS.items():
            changes = []
            for coin in coins[:4]:
                sym = f"{coin}/{QUOTE_CURRENCY}"
                try:
                    t   = await asyncio.to_thread(exchange.fetch_ticker, sym)
                    pct = t.get("percentage", 0) or 0
                    changes.append(pct)
                except:
                    continue
            if not changes:
                continue
            avg   = round(statistics.mean(changes), 2)
            sector_performance[sector].append(avg)
            emoji = "🟢" if avg > 0 else "🔴" if avg < -1 else "⚪"
            bar   = "█" * min(int(abs(avg)), 5)
            lines.append(f"{emoji} {sector:<8} `{avg:+.2f}%` {bar}")
        if not lines:
            return
        fg  = update_fear_greed()
        msg = (
            f"🗺️ *خريطة القطاعات*\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            + "\n".join(lines) +
            f"\n━━━━━━━━━━━━━━━━━━━━\n"
            f"🌡️ Fear & Greed: {get_fg_label(fg)}\n"
            f"⚠️ _رصد تقني فقط_"
        )
        await bot.send_message(chat_id=TELEGRAM_CHAT_ID, text=msg, parse_mode="Markdown")
    except Exception as e:
        log.warning(f"خطأ Heatmap: {e}")


# ──────────────────────────────────────────
# BTC Correlation
# ──────────────────────────────────────────
def check_btc_correlation(symbol, closes):
    global correlation_cache, correlation_ts
    try:
        now = time.time()
        if now - correlation_ts > 300 or "BTC" not in correlation_cache:
            btc_ohlcv = exchange.fetch_ohlcv("BTC/USDC", "5m", limit=30)
            btc_df    = pd.DataFrame(btc_ohlcv, columns=["ts","o","h","l","c","v"])
            correlation_cache["BTC"] = btc_df["c"].pct_change().dropna().tolist()
            correlation_ts = now
        btc_returns  = correlation_cache["BTC"]
        coin_returns = pd.Series(closes).pct_change().dropna().tolist()
        min_len      = min(len(btc_returns), len(coin_returns))
        if min_len < 10:
            return None
        corr = np.corrcoef(btc_returns[-min_len:], coin_returns[-min_len:])[0, 1]
        return {
            "correlation": round(corr, 3),
            "independent": abs(corr) < 0.3,
            "inverse":     corr < -0.3,
        }
    except:
        return None


# ──────────────────────────────────────────
# Smart Cooldown
# ──────────────────────────────────────────
def get_smart_cooldown(score):
    if score >= 6:   return COOLDOWN_SCORE_6
    elif score >= 5: return COOLDOWN_SCORE_5
    else:            return COOLDOWN_SCORE_4


def can_alert(symbol, score):
    now      = time.time()
    cooldown = get_smart_cooldown(score)
    if now - alerted_at.get(symbol, 0) > cooldown:
        alerted_at[symbol] = now
        return True
    return False


# ──────────────────────────────────────────
# Quiet Hours
# ──────────────────────────────────────────
def is_quiet_hours():
    hour = datetime.utcnow().hour
    return QUIET_HOURS_START <= hour < QUIET_HOURS_END


def get_effective_min_volume():
    return MIN_DAILY_VOLUME * 2 if is_quiet_hours() else MIN_DAILY_VOLUME


# ──────────────────────────────────────────
# Health Check
# ──────────────────────────────────────────
restart_count    = 0
last_health_ping = time.time()


async def health_check_loop():
    global last_health_ping
    while True:
        await asyncio.sleep(1800)
        try:
            await asyncio.to_thread(exchange.fetch_time)
            last_health_ping = time.time()
            log.info("💚 Health check: OK")
        except Exception as e:
            log.error(f"🔴 Health check فشل: {e}")
            await bot.send_message(
                chat_id=TELEGRAM_CHAT_ID,
                text=f"⚠️ *تحذير: مشكلة في الاتصال*\nالخطأ: `{str(e)[:100]}`",
                parse_mode="Markdown"
            )


# ──────────────────────────────────────────
# Max Gain Tracker
# ──────────────────────────────────────────
async def track_max_gain(symbol, alert_price):
    max_gain = 0
    start    = time.time()
    while time.time() - start < 1200:
        try:
            ticker   = await asyncio.to_thread(exchange.fetch_ticker, symbol)
            current  = ticker["last"]
            gain     = (current - alert_price) / alert_price * 100
            if gain > max_gain:
                max_gain = gain
        except:
            pass
        await asyncio.sleep(30)
    return round(max_gain, 2)


# ──────────────────────────────────────────
# Paper Trading
# ──────────────────────────────────────────
def paper_open(symbol, price):
    risk_amount = PAPER_CAPITAL * PAPER_RISK_PCT
    qty         = risk_amount / price
    stop_loss   = price * 0.990
    target      = price * 1.030
    conn        = sqlite3.connect("alerts.db")
    conn.execute(
        "INSERT INTO paper_trades (symbol,entry_price,qty,status,opened_at) VALUES (?,?,?,'open',?)",
        (symbol, price, qty, datetime.now().isoformat())
    )
    conn.commit()
    conn.close()
    trailing_stops[symbol] = {
        "peak":  price,
        "stop":  price * (1 - TRAILING_STOP_PCT),
        "entry": price,
    }
    return {"entry_price": price, "qty": qty, "stop_loss": stop_loss, "target": target, "risk": risk_amount}


def paper_close(symbol, exit_price, reason="timeout"):
    conn = sqlite3.connect("alerts.db")
    row  = conn.execute(
        "SELECT id, entry_price, qty FROM paper_trades WHERE symbol=? AND status='open' ORDER BY id DESC LIMIT 1",
        (symbol,)
    ).fetchone()
    if not row:
        conn.close()
        return None
    trade_id, entry_price, qty = row
    pnl = (exit_price - entry_price) * qty
    conn.execute(
        "UPDATE paper_trades SET exit_price=?, pnl=?, status='closed', exit_reason=?, closed_at=? WHERE id=?",
        (exit_price, pnl, reason, datetime.now().isoformat(), trade_id)
    )
    conn.commit()
    conn.close()
    trailing_stops.pop(symbol, None)
    return {"pnl": round(pnl, 4), "entry": entry_price, "exit": exit_price, "qty": qty, "reason": reason}


def get_paper_summary():
    conn      = sqlite3.connect("alerts.db")
    rows      = conn.execute(
        "SELECT symbol, entry_price, exit_price, pnl, opened_at, exit_reason FROM paper_trades WHERE status='closed'"
    ).fetchall()
    open_rows = conn.execute(
        "SELECT symbol, entry_price, qty, opened_at FROM paper_trades WHERE status='open'"
    ).fetchall()
    conn.close()
    total_pnl = sum(r[3] for r in rows) if rows else 0
    wins      = sum(1 for r in rows if r[3] > 0)
    total     = len(rows)
    rate      = round(wins / total * 100, 1) if total > 0 else 0
    trailing_wins = sum(1 for r in rows if r[5] == "trailing_stop" and r[3] > 0)
    return {
        "closed": total, "wins": wins, "rate": rate,
        "total_pnl": round(total_pnl, 2),
        "open_count": len(open_rows),
        "open_trades": open_rows,
        "trailing_wins": trailing_wins,
    }


async def send_paper_update(symbol, data, action="open"):
    if action == "open":
        msg = (
            f"📝 *Paper Trade — فتح*\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"العملة:  `{symbol}`\n"
            f"دخول:   `{data['entry_price']:.6f}`\n"
            f"كمية:    `{data['qty']:.4f}`\n"
            f"وقف:    `{data['stop_loss']:.6f}`\n"
            f"هدف:    `{data['target']:.6f}`\n"
            f"مخاطرة: `${data['risk']:.2f}`\n"
            f"📐 Trailing Stop: `{data['entry_price'] * (1 - TRAILING_STOP_PCT):.6f}`\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"⚠️ _صفقة وهمية للتتبع فقط_"
        )
    else:
        emoji  = "🟢" if data["pnl"] > 0 else "🔴"
        reason_map = {
            "trailing_stop": "📐 Trailing Stop",
            "timeout":       "⏰ انتهت المدة",
            "target":        "🎯 وصل الهدف",
        }
        reason_text = reason_map.get(data.get("reason","timeout"), "❓")
        msg = (
            f"{emoji} *Paper Trade — إغلاق*\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"العملة:       `{symbol}`\n"
            f"دخول:        `{data['entry']:.6f}`\n"
            f"خروج:        `{data['exit']:.6f}`\n"
            f"ربح/خسارة:   `{data['pnl']:+.4f}$`\n"
            f"سبب الخروج:  {reason_text}\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"⚠️ _صفقة وهمية للتتبع فقط_"
        )
    await bot.send_message(chat_id=TELEGRAM_CHAT_ID, text=msg, parse_mode="Markdown")


# ──────────────────────────────────────────
# مراقبة الحيتان — محسّنة
# ──────────────────────────────────────────
async def whale_monitor_loop():
    log.info("🐋 بدأت مراقبة الحيتان اللحظية...")
    symbols_cache    = []
    symbols_cache_ts = 0

    while True:
        try:
            if not whale_monitoring or emergency_mode:
                await asyncio.sleep(5)
                continue

            now = time.time()
            if now - symbols_cache_ts > 300:
                symbols_cache    = await get_all_symbols_cached()
                symbols_cache_ts = now
                log.info(f"🐋 رادار الحيتان: {len(symbols_cache)} عملة")

            # ⚡ فحص الحيتان بالتوازي
            async def check_whale(symbol):
                try:
                    ticker = await asyncio.to_thread(exchange.fetch_ticker, symbol)
                    price  = ticker.get("last", 0)
                    if price > WHALE_MAX_PRICE:
                        return
                    trades = await asyncio.to_thread(exchange.fetch_trades, symbol, None, 20)
                    if not trades:
                        return
                    wh_now = time.time()
                    for trade in trades:
                        trade_value = trade["amount"] * trade["price"]
                        if trade_value < WHALE_MIN_USDC:
                            continue
                        trade_key = f"{symbol}_{trade['id']}"
                        if trade_key in whale_alerted_at:
                            continue
                        whale_alerted_at[trade_key] = wh_now
                        level       = "strong" if trade_value >= WHALE_STRONG_USDC else "normal"
                        whale_emoji = "🐋" if level == "strong" else "🐟"
                        level_text  = "حوت ضخم" if level == "strong" else "حوت"
                        side        = trade["side"]
                        side_emoji  = "🟢 شراء" if side == "buy" else "🔴 بيع"
                        coin        = symbol.replace("/", "").replace("USDC", "USDC")
                        chart_link  = f"https://www.tradingview.com/chart/?symbol=BINANCE:{coin}"
                        micro       = analyze_microstructure(symbol)
                        micro_txt   = f"\n📊 عمق الشراء: `{micro['depth_ratio']}x` 💪" if micro and micro["bullish_depth"] else ""
                        conn = sqlite3.connect("alerts.db")
                        conn.execute(
                            "INSERT INTO whale_trades (symbol,side,amount_usdc,price,level,timestamp) VALUES (?,?,?,?,?,?)",
                            (symbol, side, round(trade_value, 0), trade["price"], level, datetime.now().isoformat())
                        )
                        conn.commit()
                        conn.close()
                        await bot.send_message(
                            chat_id=TELEGRAM_CHAT_ID,
                            text=(
                                f"{whale_emoji} *{level_text} {side_emoji}*\n"
                                f"━━━━━━━━━━━━━━━━━━━━\n"
                                f"العملة:  `{symbol}`\n"
                                f"المبلغ:  `${trade_value:,.0f}` USDC\n"
                                f"السعر:   `{trade['price']:.6f}`\n"
                                f"{micro_txt}\n"
                                f"━━━━━━━━━━━━━━━━━━━━\n"
                                f"🔗 [افتح الشارت]({chart_link})\n"
                                f"🕐 {datetime.now().strftime('%H:%M:%S')}\n"
                                f"⚠️ _رصد تقني فقط، ليس نصيحة مالية_"
                            ),
                            parse_mode="Markdown",
                            disable_web_page_preview=True
                        )
                        log.info(f"🐋 حوت: {symbol} | {side} | ${trade_value:,.0f}")
                except Exception as e:
                    log.debug(f"خطأ حوت {symbol}: {e}")

            # تقسيم على دفعات
            sem = asyncio.Semaphore(15)
            async def check_whale_limited(s):
                async with sem:
                    await check_whale(s)

            await asyncio.gather(*[check_whale_limited(s) for s in symbols_cache], return_exceptions=True)

        except Exception as e:
            log.warning(f"خطأ في حلقة الحيتان: {e}")

        await asyncio.sleep(3)


# ──────────────────────────────────────────
# مراقبة الاختراقات — محسّنة
# ──────────────────────────────────────────
async def breakout_monitor_loop():
    log.info("🚀 بدأت مراقبة الاختراقات...")

    while True:
        try:
            if emergency_mode:
                await asyncio.sleep(30)
                continue

            symbols = await get_all_symbols_cached()

            async def check_breakout(symbol):
                try:
                    ohlcv = await asyncio.to_thread(exchange.fetch_ohlcv, symbol, "5m", None, 30)
                    if len(ohlcv) < 20:
                        return
                    df         = pd.DataFrame(ohlcv, columns=["ts","o","h","l","c","v"])
                    current    = df["c"].iloc[-1]
                    resistance = df["h"].iloc[-20:-1].max()
                    prev_close = df["c"].iloc[-2]
                    if not (current > resistance and prev_close <= resistance):
                        return
                    avg_vol   = df["v"].iloc[:-1].mean()
                    vol_ratio = df["v"].iloc[-1] / avg_vol if avg_vol > 0 else 0
                    if vol_ratio < 1.5:
                        return
                    now = time.time()
                    if now - breakout_alerted_at.get(symbol, 0) < 3600:
                        return
                    breakout_alerted_at[symbol] = now
                    rsi_val   = calc_rsi(df["c"].tolist())
                    macd_data = calc_macd(df["c"].tolist())
                    bb_data   = calc_bollinger(df["c"].tolist())
                    mtf       = get_mtf_trend(symbol)
                    sr        = detect_support_resistance(df)
                    rsi_txt   = f"RSI: `{rsi_val}`" if rsi_val else ""
                    macd_txt  = "MACD: ✅ صاعد" if macd_data and macd_data["bullish"] else "MACD: ❌"
                    mtf_txt   = "MTF: ✅ كل الإطارات صاعدة" if mtf and mtf["all_bullish"] else "MTF: ⚠️ غير متوافق"
                    rr_txt    = f"R/R: `{sr['risk_reward']}:1`" if sr else ""
                    breakout_pct = (current - resistance) / resistance * 100
                    coin         = symbol.replace("/", "").replace("USDC", "USDC")
                    chart_link   = f"https://www.tradingview.com/chart/?symbol=BINANCE:{coin}"
                    await bot.send_message(
                        chat_id=TELEGRAM_CHAT_ID,
                        text=(
                            f"🚀 *اختراق حقيقي!* | `{symbol}`\n"
                            f"━━━━━━━━━━━━━━━━━━━━\n"
                            f"السعر الآن:  `{current:.6f}`\n"
                            f"المقاومة:    `{resistance:.6f}`\n"
                            f"الاختراق:    `+{breakout_pct:.2f}%` فوق المقاومة\n"
                            f"الحجم:       `{vol_ratio:.1f}x` المعدل 🔥\n"
                            f"━━━━━━━━━━━━━━━━━━━━\n"
                            f"📊 {rsi_txt} | {macd_txt}\n"
                            f"🔀 {mtf_txt}\n"
                            f"⚖️ {rr_txt}\n"
                            f"━━━━━━━━━━━━━━━━━━━━\n"
                            f"🎯 هدف 1:  `{current * 1.015:.6f}`  *(+1.5%)*\n"
                            f"🎯 هدف 2:  `{current * 1.030:.6f}`  *(+3.0%)*\n"
                            f"🛑 وقف:    `{resistance * 0.995:.6f}`  *(تحت المقاومة)*\n"
                            f"━━━━━━━━━━━━━━━━━━━━\n"
                            f"🔗 [افتح الشارت]({chart_link})\n"
                            f"🕐 {datetime.now().strftime('%H:%M:%S')}\n"
                            f"⚠️ _رصد تقني فقط، ليس نصيحة مالية_"
                        ),
                        parse_mode="Markdown",
                        disable_web_page_preview=True
                    )
                    log.info(f"🚀 اختراق: {symbol} @ {current:.6f}")
                    paper_data = paper_open(symbol, current)
                    await send_paper_update(symbol, paper_data, action="open")
                    asyncio.create_task(paper_close_later(symbol, current))
                except Exception as e:
                    log.debug(f"خطأ اختراق {symbol}: {e}")

            sem = asyncio.Semaphore(20)
            async def check_bo_limited(s):
                async with sem:
                    await check_breakout(s)

            await asyncio.gather(*[check_bo_limited(s) for s in symbols], return_exceptions=True)

        except Exception as e:
            log.warning(f"خطأ في حلقة الاختراقات: {e}")

        await asyncio.sleep(30)


async def paper_close_later(symbol, entry_price):
    max_g = await track_max_gain(symbol, entry_price)
    try:
        ticker     = await asyncio.to_thread(exchange.fetch_ticker, symbol)
        exit_price = ticker["last"]
        result     = paper_close(symbol, exit_price, reason="timeout")
        if result:
            result["max_gain"] = max_g
            await send_paper_update(symbol, result, action="close")
            save_result(symbol, entry_price, exit_price, max_g)
    except Exception as e:
        log.warning(f"فشل إغلاق Paper Trade {symbol}: {e}")


# ──────────────────────────────────────────
# فحص BTC
# ──────────────────────────────────────────
def btc_is_stable():
    try:
        ohlcv = exchange.fetch_ohlcv("BTC/USDC", "1m", limit=4)
        if len(ohlcv) < 3:
            return True, 0
        first = ohlcv[-3][4]
        last  = ohlcv[-1][4]
        move  = (last - first) / first * 100
        if move <= -EMERGENCY_BTC_DROP:
            return False, move
        if abs(move) > BTC_MAX_MOVE_PCT:
            return False, move
        return True, move
    except Exception as e:
        log.warning(f"تعذّر فحص BTC: {e}")
        return True, 0


def get_btc_price():
    try:
        t = exchange.fetch_ticker("BTC/USDC")
        return t["last"], t.get("percentage", 0)
    except:
        return None, None


def get_eth_bnb():
    result = {}
    for sym in ["ETH/USDC", "BNB/USDC"]:
        try:
            t = exchange.fetch_ticker(sym)
            result[sym.split("/")[0]] = round(t.get("percentage", 0), 2)
        except:
            result[sym.split("/")[0]] = 0
    return result


def get_all_symbols():
    markets = exchange.load_markets()
    return [
        s for s in markets
        if s.endswith(f"/{QUOTE_CURRENCY}")
        and markets[s].get("active")
        and markets[s].get("spot")
    ]


def detect_whales(symbol):
    try:
        trades = exchange.fetch_trades(symbol, limit=100)
        if not trades:
            return None
        whale_trades = [t for t in trades if t["amount"] * t["price"] >= WHALE_MIN_USDC]
        if len(whale_trades) < 2:
            return None
        buys      = [t for t in whale_trades if t["side"] == "buy"]
        sells     = [t for t in whale_trades if t["side"] == "sell"]
        buy_ratio = len(buys) / len(whale_trades)
        total_buy  = sum(t["amount"] * t["price"] for t in buys)
        total_sell = sum(t["amount"] * t["price"] for t in sells)
        net_flow   = total_buy - total_sell
        slow_acc   = False
        if len(buys) >= 2:
            span     = (buys[-1]["timestamp"] - buys[0]["timestamp"]) / 1000
            slow_acc = span > 30
        return {
            "whale_trades":      len(whale_trades),
            "whale_buy_ratio":   round(buy_ratio * 100, 1),
            "whale_net_flow":    round(net_flow, 0),
            "slow_accumulation": slow_acc,
            "whale_signal":      buy_ratio >= WHALE_BUY_RATIO and slow_acc and net_flow > 0,
        }
    except Exception as e:
        log.debug(f"خطأ حيتان {symbol}: {e}")
        return None


def check_news(symbol):
    coin = symbol.split("/")[0]
    try:
        feed      = feedparser.parse(
            f"https://cryptopanic.com/api/v1/posts/?currencies={coin}&filter=hot&public=true"
        )
        bad_words = ["hack","scam","lawsuit","ban","exploit","rug","fraud","investigation"]
        for entry in feed.entries[:5]:
            title = entry.get("title","").lower()
            if any(w in title for w in bad_words):
                return {"safe": False, "reason": entry.get("title","")}
        return {"safe": True, "reason": None}
    except:
        return {"safe": True, "reason": None}


def detect_wash_trading(symbol):
    try:
        trades    = exchange.fetch_trades(symbol, limit=50)
        if len(trades) < 10:
            return False
        amounts   = [round(t["amount"], 4) for t in trades]
        prices    = [round(t["price"],  6) for t in trades]
        dup_amt   = len(amounts) - len(set(amounts))
        dup_price = len(prices)  - len(set(prices))
        return (dup_amt / len(amounts) > 0.3) and (dup_price / len(prices) > 0.3)
    except:
        return False


def classify_pattern(df, dist_to_res, bb_data=None, rsi_val=None):
    current   = df["c"].iloc[-1]
    vol_trend = df["v"].iloc[-5:].mean() > df["v"].iloc[-15:-5].mean() * 1.5
    price_flat= df["c"].iloc[-5:].std() / current < 0.003
    if bb_data and bb_data.get("squeeze"):
        return "Bollinger Squeeze ⚡️ طاقة مضغوطة"
    if vol_trend and price_flat:
        return "تجميع هادي 🐢"
    if 0 < dist_to_res < 0.5:
        return "اختراق وشيك 🚀"
    if 0.5 <= dist_to_res < 0.8:
        return "قريب الاختراق ⚡️"
    if rsi_val and rsi_val < 40:
        return "مبالغ في البيع 🔄"
    return "تجميع نشط 📈"


sector_signals = {}


def check_domino(symbol, score):
    coin = symbol.split("/")[0]
    for sector, coins in SECTORS.items():
        if coin in coins:
            if sector not in sector_signals:
                sector_signals[sector] = []
            if symbol not in sector_signals[sector] and score >= 4:
                sector_signals[sector].append(symbol)
            return sector
    return None


async def send_domino_alert(sector, symbols):
    lines = "\n".join([f"• `{s}`" for s in symbols])
    msg   = (
        f"🁢 *إشارة دومينو* | قطاع {sector}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"تجمّعت مع بعض:\n{lines}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"💡 القطاع كله بيتحرك = إشارة أقوى\n"
        f"⚠️ _رصد تقني فقط، ليس نصيحة مالية_"
    )
    await bot.send_message(chat_id=TELEGRAM_CHAT_ID, text=msg, parse_mode="Markdown")


def compare_usdc_usdt(symbol, usdc_price):
    usdt_symbol = symbol.replace("USDC", "USDT")
    try:
        t          = exchange.fetch_ticker(usdt_symbol)
        usdt_price = t["last"]
        diff       = (usdc_price - usdt_price) / usdt_price * 100
        return round(diff, 3), usdt_price
    except:
        return None, None


# ──────────────────────────────────────────
# ⚡ التحليل الرئيسي — نسخة Async سريعة
# ──────────────────────────────────────────
def analyze_symbol(symbol):
    """الدالة الأصلية — sync — تُشغَّل في thread منفصل"""
    try:
        ticker = exchange.fetch_ticker(symbol)
        if (ticker.get("quoteVolume") or 0) < get_effective_min_volume():
            return None

        ohlcv = exchange.fetch_ohlcv(symbol, "1m", limit=60)
        if len(ohlcv) < 20:
            return None

        df     = pd.DataFrame(ohlcv, columns=["ts","o","h","l","c","v"])
        score  = 0
        detail = {}
        closes = df["c"].tolist()

        v1, v2, v3, v4 = df["v"].iloc[-4], df["v"].iloc[-3], df["v"].iloc[-2], df["v"].iloc[-1]
        avg_vol   = df["v"].iloc[:-1].mean()
        vol_ratio = v4 / avg_vol if avg_vol > 0 else 0
        acc       = (v1 < v2 < v3 < v4) and vol_ratio >= 2.5
        detail["vol_ratio"]    = round(vol_ratio, 1)
        detail["accelerating"] = acc
        detail["vol_24h"]      = round(ticker.get("quoteVolume", 0))
        if acc:
            score += 1

        strong_closes = sum(1 for row in df.iloc[-4:-1].itertuples() if row.c > (row.h + row.l) / 2)
        detail["strong_closes"] = strong_closes
        if strong_closes >= 2:
            score += 1

        lows        = df["l"].iloc[-6:].values
        higher_lows = all(lows[i] >= lows[i-1] for i in range(1, len(lows)))
        detail["higher_lows"] = higher_lows
        if higher_lows:
            score += 1

        ob      = exchange.fetch_order_book(symbol, limit=20)
        bid_vol = sum(x[1] for x in ob["bids"])
        ask_vol = sum(x[1] for x in ob["asks"])
        total   = bid_vol + ask_vol
        buy_pct = (bid_vol / total * 100) if total > 0 else 50
        detail["buy_pct"] = round(buy_pct, 1)
        if buy_pct > 65:
            score += 1

        resistance      = df["h"].iloc[-20:].max()
        current_price   = df["c"].iloc[-1]
        dist_to_res_pct = (resistance - current_price) / current_price * 100
        detail["dist_to_resistance"] = round(dist_to_res_pct, 2)
        detail["resistance"]         = resistance
        if 0 < dist_to_res_pct < 0.8:
            score += 1

        whale_data = detect_whales(symbol)
        if whale_data and whale_data["whale_signal"]:
            score += 1
            detail.update({k: whale_data[k] for k in whale_data})
        else:
            detail.update({
                "whale_signal":      False,
                "whale_buy_ratio":   whale_data["whale_buy_ratio"] if whale_data else 0,
                "whale_net_flow":    whale_data["whale_net_flow"]  if whale_data else 0,
                "whale_trades":      whale_data["whale_trades"]    if whale_data else 0,
                "slow_accumulation": False,
            })

        if score < 4:
            return None

        if detect_wash_trading(symbol):
            log.info(f"⚠️ تلاعب محتمل في {symbol} — تجاهل")
            return None

        news = check_news(symbol)
        if not news["safe"]:
            log.info(f"⚠️ أخبار سلبية لـ {symbol}: {news['reason']}")
            return None

        rsi_val   = calc_rsi(closes)
        stoch_k, stoch_d = calc_stoch_rsi(closes)
        detail["rsi"]     = rsi_val
        detail["stoch_k"] = stoch_k
        detail["stoch_d"] = stoch_d
        detail["rsi_ok"]  = rsi_val and 45 < rsi_val < 75

        macd_data = calc_macd(closes)
        detail["macd_data"]   = macd_data
        detail["macd_signal"] = "bullish" if macd_data and macd_data["bullish"] else "neutral"

        bb_data = calc_bollinger(closes)
        detail["bb_data"]    = bb_data
        detail["bb_squeeze"] = bb_data["squeeze"] if bb_data else False

        fib_data = calc_fibonacci(df)
        detail["fib_data"]         = fib_data
        detail["fib_near_support"] = fib_data["is_near_support"] if fib_data else False
        detail["nearest_fib"]      = fib_data["nearest_support"] if fib_data else None

        vp_data = calc_volume_profile(df)
        detail["vp_data"] = vp_data

        div_data = detect_rsi_divergence(df)
        detail["rsi_divergence"] = div_data

        mtf_data = get_mtf_trend(symbol)
        detail["mtf_data"]    = mtf_data
        detail["mtf_aligned"] = mtf_data["all_bullish"] if mtf_data else False

        sr_data = detect_support_resistance(df)
        detail["sr_data"] = sr_data
        detail["good_rr"] = sr_data["good_rr"] if sr_data else False

        liq_data = detect_liquidity_zones(symbol)
        detail["liq_data"]    = liq_data
        detail["bullish_liq"] = liq_data["bullish_liq"] if liq_data else False

        micro_data = analyze_microstructure(symbol)
        detail["micro_data"] = micro_data

        anomalies = detect_anomaly(symbol, df["v"].iloc[-1], current_price)
        detail["anomalies"] = anomalies

        corr_data = check_btc_correlation(symbol, closes[-30:])
        detail["corr_data"] = corr_data

        ai_score = calc_ai_score({**detail, "score": score})
        detail["ai_score"] = ai_score

        detail["pattern"]   = classify_pattern(df, dist_to_res_pct, bb_data, rsi_val)
        detail["target1"]   = round(current_price * 1.015, 6)
        detail["target2"]   = round(current_price * 1.030, 6)
        detail["stop_loss"] = round(current_price * 0.990, 6)

        usdc_gap, usdt_price = compare_usdc_usdt(symbol, current_price)
        detail["usdc_gap"]   = usdc_gap
        detail["usdt_price"] = usdt_price
        detail["reputation"] = get_reputation(symbol)

        candle_age       = int((time.time() * 1000 - df["ts"].iloc[-1]) / 1000)
        detail["candle_age"] = candle_age
        detail["sector"]     = check_domino(symbol, score)

        return {"symbol": symbol, "price": current_price, "score": score, **detail}

    except Exception as e:
        log.debug(f"خطأ في {symbol}: {e}")
        return None


# ──────────────────────────────────────────
# ⚡ الدالة الجديدة — تشغيل متوازٍ حقيقي
# ──────────────────────────────────────────
async def analyze_symbol_async(symbol):
    """تشغيل analyze_symbol في thread منفصل = async حقيقي"""
    sem = get_semaphore()
    async with sem:
        return await asyncio.to_thread(analyze_symbol, symbol)


# ──────────────────────────────────────────
# إرسال التنبيه
# ──────────────────────────────────────────
async def send_alert(data):
    stars     = "⭐" * data["score"]
    acc_emoji = "✅" if data["accelerating"]                   else "❌"
    hl_emoji  = "✅" if data["higher_lows"]                    else "❌"
    sc_emoji  = "✅" if data["strong_closes"] >= 2             else "❌"
    bp_emoji  = "✅" if data["buy_pct"] > 65                   else "❌"
    co_emoji  = "✅" if 0 < data["dist_to_resistance"] < 0.8   else "❌"
    wh_emoji  = "🐋" if data["whale_signal"]                   else "❌"

    rsi_val  = data.get("rsi")
    rsi_txt  = f"`{rsi_val}`" if rsi_val else "N/A"
    rsi_state= ""
    if rsi_val:
        if rsi_val < 30:   rsi_state = "🔴 مبالغ بيع"
        elif rsi_val < 50: rsi_state = "⚪ محايد"
        elif rsi_val < 70: rsi_state = "🟢 قوي"
        else:              rsi_state = "⚠️ مبالغ شراء"

    macd = data.get("macd_data")
    if macd:
        macd_txt = "🟢 صاعد" if macd["bullish"] else "🔴 هابط"
        if macd.get("cross"):
            macd_txt += " ⚡تقاطع!"
    else:
        macd_txt = "N/A"

    bb = data.get("bb_data")
    bb_txt = ""
    if bb:
        bb_txt = f"🗜️ BB Squeeze ⚡ طاقة مضغوطة!\n" if bb["squeeze"] else f"📊 BB: `{bb['pct_b']:.0f}%`\n"

    fib = data.get("fib_data")
    fib_txt = ""
    if fib and fib["is_near_support"]:
        fib_txt = f"🔢 Fib دعم: `{fib['nearest_support']:.6f}` *(قريب جداً ✅)*\n"

    vp = data.get("vp_data")
    vp_txt = ""
    if vp:
        poc_txt = "فوق POC 🟢" if vp["above_poc"] else "تحت POC ⚠️"
        vp_txt  = f"📊 VP — POC: `{vp['poc']:.6f}` | {poc_txt}\n"

    div = data.get("rsi_divergence")
    div_txt = f"🔄 RSI Divergence: {div['type']} {div['strength']}\n" if div else ""

    mtf = data.get("mtf_data")
    mtf_txt = ""
    if mtf:
        all_ok   = mtf.get("all_bullish")
        tf_lines = " | ".join([f"{tf}: {trend}" for tf, trend in mtf.get("trends", {}).items()])
        mtf_txt  = f"🔀 MTF: {tf_lines}" + (" ✅ متوافق!\n" if all_ok else "\n")

    sr = data.get("sr_data")
    rr_txt = ""
    if sr:
        rr_emoji = "✅" if sr["good_rr"] else "⚠️"
        rr_txt   = f"⚖️ R/R: `{sr['risk_reward']:.1f}:1` {rr_emoji} | دعم `{sr['support']:.6f}`\n"

    liq = data.get("liq_data")
    liq_txt = ""
    if liq and liq["bullish_liq"]:
        liq_txt = f"💧 سيولة: شراء `{liq['imbalance']}x` البيع 💪\n"

    micro = data.get("micro_data")
    micro_txt = ""
    if micro:
        sp_txt    = "ضيق ✅" if micro["tight_spread"] else "عادي"
        micro_txt = f"🔬 Spread: `{micro['spread']:.4f}%` ({sp_txt}) | Depth: `{micro['depth_ratio']}x`\n"

    anomalies = data.get("anomalies", [])
    anom_txt  = ""
    for a in anomalies:
        anom_txt += f"⚡ {a['msg']}\n"

    corr = data.get("corr_data")
    corr_txt = ""
    if corr:
        if corr["inverse"]:
            corr_txt = f"📐 ارتباط BTC: `{corr['correlation']}` ↕️ معاكس = فرصة مستقلة\n"
        elif corr["independent"]:
            corr_txt = f"📐 ارتباط BTC: `{corr['correlation']}` ◎ مستقل\n"

    ai    = data.get("ai_score", 0)
    ai_bar = "█" * int(ai * 10) + "░" * (10 - int(ai * 10))
    ai_txt = f"🧠 AI Score: `{ai:.2%}` [{ai_bar}]\n"

    if data["whale_signal"]:
        whale_line = (
            f"{wh_emoji} حيتان تشتري:     `{data['whale_trades']} صفقة` | "
            f"شراء `{data['whale_buy_ratio']}%` | "
            f"صافي `+{data['whale_net_flow']:,.0f}` USDC\n"
        )
    else:
        whale_line = f"{wh_emoji} حيتان:           `{data['whale_buy_ratio']}%` شراء\n"

    rep = data.get("reputation")
    if rep:
        rep_line = (
            f"⭐ السمعة: {rep['badge']}{rep['streak_txt']} | "
            f"{rep['success']}/{rep['total']} | "
            f"متوسط `+{rep['avg_profit']}%` | أعلى `+{rep['max_profit']}%`\n"
        )
    else:
        rep_line = "⭐ السمعة: جديدة — لا يوجد تاريخ\n"

    if data.get("usdc_gap") is not None:
        gap_sign  = "+" if data["usdc_gap"] > 0 else ""
        usdt_line = f"💱 USDC vs USDT: `{gap_sign}{data['usdc_gap']}%` | "
        usdt_line += "تدفق شراء من USDC 📥\n" if data["usdc_gap"] > 0.1 else "متوازن\n"
    else:
        usdt_line = ""

    age      = data.get("candle_age", 0)
    age_text = f"{age}ث" if age < 60 else f"{age//60}د {age%60}ث"
    coin     = data["symbol"].replace("/", "").replace("USDC", "USDC")
    chart_link = f"https://www.tradingview.com/chart/?symbol=BINANCE:{coin}"
    quiet_warn = "🌙 _ساعات هادئة — سيولة منخفضة_\n" if is_quiet_hours() else ""
    fg_label   = get_fg_label(fear_greed_score)

    msg = (
        f"⚡️ *تجميع مؤكد* | `{data['symbol']}`\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🏆 القوة: {stars}  ({data['score']}/6)\n"
        f"🏷️ النوع: {data['pattern']}\n"
        f"{ai_txt}"
        f"🌡️ Fear & Greed: {fg_label}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"{acc_emoji} حجم متسارع:      `{data['vol_ratio']}x`\n"
        f"{sc_emoji} شموع قوية:        `{data['strong_closes']}/3`\n"
        f"{hl_emoji} قيعان ترتفع:      `{'نعم' if data['higher_lows'] else 'لا'}`\n"
        f"{bp_emoji} ضغط شراء:         `{data['buy_pct']}%`\n"
        f"{co_emoji} قريب الاختراق:    `{data['dist_to_resistance']}%`\n"
        f"{whale_line}"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"📈 RSI: {rsi_txt} {rsi_state}\n"
        f"📉 MACD: {macd_txt}\n"
        f"{bb_txt}"
        f"{fib_txt}"
        f"{vp_txt}"
        f"{div_txt}"
        f"{mtf_txt}"
        f"{rr_txt}"
        f"{liq_txt}"
        f"{micro_txt}"
        f"{corr_txt}"
        f"{anom_txt}"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"💰 السعر:   `{data['price']:.6f}`\n"
        f"🎯 هدف 1:   `{data['target1']:.6f}`  *(+1.5%)*\n"
        f"🎯 هدف 2:   `{data['target2']:.6f}`  *(+3.0%)*\n"
        f"🛑 وقف:     `{data['stop_loss']:.6f}`  *(-1.0%)*\n"
        f"📐 Trailing:`{data['price'] * (1-TRAILING_STOP_PCT):.6f}` *(-{TRAILING_STOP_PCT*100:.1f}%)*\n"
        f"🎯 مقاومة:  `{data['resistance']:.6f}`\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"📊 حجم 24h: `{data['vol_24h']:,}` USDC\n"
        f"{usdt_line}"
        f"{rep_line}"
        f"⏱️ عمر الإشارة: `{age_text}`\n"
        f"{quiet_warn}"
        f"🔗 [افتح الشارت]({chart_link})\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"🕐 {datetime.now().strftime('%H:%M:%S')}\n"
        f"⚠️ _رصد تقني فقط، ليس نصيحة مالية_"
    )

    await bot.send_message(
        chat_id=TELEGRAM_CHAT_ID, text=msg,
        parse_mode="Markdown", disable_web_page_preview=True
    )
    log.info(f"✅ تنبيه: {data['symbol']} | score={data['score']} | AI={data.get('ai_score',0):.2%}")

    save_alert(
        data["symbol"], data["price"], data["score"],
        data["vol_ratio"], data["buy_pct"],
        rsi=data.get("rsi"), macd_signal=data.get("macd_signal"),
        ai_score=data.get("ai_score")
    )
    daily_alerts.append({"symbol": data["symbol"], "price": data["price"]})

    paper_data = paper_open(data["symbol"], data["price"])
    await send_paper_update(data["symbol"], paper_data, action="open")
    asyncio.create_task(check_result_later(data["symbol"], data["price"]))


# ──────────────────────────────────────────
# تتبع النتيجة
# ──────────────────────────────────────────
async def check_result_later(symbol, alert_price):
    max_gain = await track_max_gain(symbol, alert_price)
    try:
        ticker      = await asyncio.to_thread(exchange.fetch_ticker, symbol)
        check_price = ticker["last"]
        change      = save_result(symbol, alert_price, check_price, max_gain)
        emoji       = "🟢" if change > 0 else "🔴"
        train_msg   = f"\n🚂 *فات القطار!* لا تدخل هلق، انتظر تصحيح ⛔️" if change > 3.0 else ""
        max_note    = f"\nأعلى نقطة وصلت: `+{max_gain:.2f}%` 📈" if max_gain > 0 else ""
        await bot.send_message(
            chat_id=TELEGRAM_CHAT_ID,
            text=(
                f"{emoji} *نتيجة التنبيه* | `{symbol}`\n"
                f"━━━━━━━━━━━━━━━━━━━━\n"
                f"سعر التنبيه: `{alert_price:.6f}`\n"
                f"السعر الآن:  `{check_price:.6f}`\n"
                f"التغير:      `{change:+.2f}%` بعد 20 دقيقة"
                f"{max_note}"
                f"{train_msg}"
            ),
            parse_mode="Markdown"
        )
        result = paper_close(symbol, check_price, reason="timeout")
        if result:
            await send_paper_update(symbol, result, action="close")
    except Exception as e:
        log.warning(f"فشل فحص النتيجة {symbol}: {e}")


# ──────────────────────────────────────────
# وضع الطوارئ
# ──────────────────────────────────────────
async def send_emergency_alert(btc_move):
    global emergency_mode
    emergency_mode = True
    await bot.send_message(
        chat_id=TELEGRAM_CHAT_ID,
        text=(
            f"🚨 *تحذير عام | وضع طوارئ*\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"BTC هبط `{btc_move:.1f}%` بـ 10 دقائق\n\n"
            f"⛔️ البوت أوقف كل الإشارات\n"
            f"⛔️ لا تفتح صفقات جديدة\n"
            f"⏳ سأعود للمراقبة بعد استقرار السوق"
        ),
        parse_mode="Markdown"
    )
    log.warning(f"🚨 وضع طوارئ — BTC: {btc_move:.1f}%")
    await asyncio.sleep(600)
    emergency_mode = False
    await bot.send_message(
        chat_id=TELEGRAM_CHAT_ID,
        text="✅ *عاد البوت للعمل الطبيعي*",
        parse_mode="Markdown"
    )


# ──────────────────────────────────────────
# رادار الساعة
# ──────────────────────────────────────────
async def send_hourly_radar(symbols):
    global last_radar_time
    now = time.time()
    if now - last_radar_time < RADAR_INTERVAL:
        return
    last_radar_time = now

    log.info("📡 جاري إعداد الرادار...")

    async def check_radar(symbol):
        try:
            ohlcv = await asyncio.to_thread(exchange.fetch_ohlcv, symbol, "5m", None, 10)
            if len(ohlcv) < 5:
                return None
            df    = pd.DataFrame(ohlcv, columns=["ts","o","h","l","c","v"])
            avg   = df["v"].iloc[:-1].mean()
            ratio = df["v"].iloc[-1] / avg if avg > 0 else 0
            rsi_v = calc_rsi(df["c"].tolist(), 7)
            if ratio > 2.0:
                return (symbol, round(ratio, 1), rsi_v or 50)
        except:
            return None

    sem = asyncio.Semaphore(20)
    async def check_r_limited(s):
        async with sem:
            return await check_radar(s)

    results = await asyncio.gather(*[check_r_limited(s) for s in symbols[:80]], return_exceptions=True)
    hot     = [r for r in results if r and not isinstance(r, Exception)]

    if not hot:
        return

    hot.sort(key=lambda x: x[1], reverse=True)
    top5  = hot[:5]
    fires = ["🔥🔥🔥", "🔥🔥🔥", "🔥🔥", "🔥🔥", "🔥"]
    lines = "\n".join([
        f"{i+1}. `{s[0]}` — حجم `{s[1]}x` {fires[i]} | RSI `{s[2]:.0f}`"
        for i, s in enumerate(top5)
    ])

    paper     = get_paper_summary()
    paper_line = (
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"📝 Paper Trading:\n"
        f"مغلقة: {paper['closed']} | نجاح: {paper['wins']} ({paper['rate']}%)\n"
        f"ربح وهمي: `{paper['total_pnl']:+.2f}$` | Trailing wins: {paper['trailing_wins']}\n"
        f"مفتوحة: {paper['open_count']}\n"
    ) if paper["closed"] > 0 else ""

    fg_label = get_fg_label(update_fear_greed())

    await bot.send_message(
        chat_id=TELEGRAM_CHAT_ID,
        text=(
            f"🔥 *رادار الساعة {datetime.now().strftime('%H:%M')}*\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"{lines}\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"🌡️ {fg_label}\n"
            f"{paper_line}"
            f"⚠️ _رصد تقني فقط، ليس نصيحة مالية_"
        ),
        parse_mode="Markdown"
    )


# ──────────────────────────────────────────
# مزاج السوق
# ──────────────────────────────────────────
async def send_market_mood():
    global last_mood_time
    now = time.time()
    if now - last_mood_time < MARKET_MOOD_INTERVAL:
        return
    last_mood_time = now

    btc_p, btc_chg = get_btc_price()
    others          = get_eth_bnb()
    stats           = get_daily_stats()
    fg              = update_fear_greed()

    btc_e = "🟢" if (btc_chg or 0) > 0 else "🔴"
    eth_e = "🟢" if others.get("ETH", 0) > 0 else "🔴"
    bnb_e = "🟢" if others.get("BNB", 0) > 0 else "🔴"
    mood  = "🟢 سوق مناسب للتداول" if (btc_chg or 0) > -1 else "🔴 سوق محفوف بالمخاطر"

    alerts_today = len(daily_alerts)
    acc_line  = f"إشارات التجميع اليوم: {alerts_today}\n" if alerts_today else ""
    rate_line = f"نسبة النجاح: {stats['rate']}% | أعلى ربح وهمي: `+{stats.get('avg_max_gain',0):.2f}%`\n" if stats else ""

    try:
        btc_ohlcv = exchange.fetch_ohlcv("BTC/USDC", "1h", limit=20)
        btc_df    = pd.DataFrame(btc_ohlcv, columns=["ts","o","h","l","c","v"])
        btc_rsi   = calc_rsi(btc_df["c"].tolist())
        rsi_line  = f"📈 BTC RSI: `{btc_rsi}` | " + (
            "مبالغ بيع 🔄" if btc_rsi < 30 else
            "قوي 🟢" if 50 < btc_rsi < 70 else "محايد"
        ) + "\n"
    except:
        rsi_line = ""

    await bot.send_message(
        chat_id=TELEGRAM_CHAT_ID,
        text=(
            f"🌡️ *مزاج السوق | {datetime.now().strftime('%H:%M')}*\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"{btc_e} BTC:  `{btc_chg:+.2f}%`\n"
            f"{eth_e} ETH:  `{others.get('ETH',0):+.2f}%`\n"
            f"{bnb_e} BNB:  `{others.get('BNB',0):+.2f}%`\n"
            f"{rsi_line}"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"{acc_line}"
            f"{rate_line}"
            f"🌡️ Fear & Greed: {get_fg_label(fg)}\n"
            f"الحالة: {mood}"
        ),
        parse_mode="Markdown"
    )
    await send_sector_heatmap()


# ──────────────────────────────────────────
# تقارير الصباح والأسبوع
# ──────────────────────────────────────────
async def send_morning_report():
    global last_morning_date
    now  = datetime.now()
    date = now.date()
    if now.hour != MORNING_HOUR or last_morning_date == date:
        return
    last_morning_date = date

    stats = get_daily_stats()
    if not stats:
        return

    btc_p, btc_chg = get_btc_price()
    btc_note        = "BTC فوق المعدل = سوق إيجابي 🟢" if (btc_chg or 0) > 0 else "BTC تحت الضغط = كن حذراً 🔴"
    paper           = get_paper_summary()
    paper_line = (
        f"📝 Paper Trading أمس:\n"
        f"صفقات: {paper['closed']} | نجاح: {paper['wins']} ({paper['rate']}%)\n"
        f"إجمالي وهمي: `{paper['total_pnl']:+.2f}$`\n"
        f"Trailing Stop wins: {paper['trailing_wins']}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
    ) if paper["closed"] > 0 else ""

    conn = sqlite3.connect("alerts.db")
    top_coins = conn.execute(
        "SELECT symbol, success*1.0/total as rate, avg_profit FROM coin_reputation WHERE total >= 3 ORDER BY rate DESC, avg_profit DESC LIMIT 3"
    ).fetchall()
    conn.close()
    top_txt = ""
    if top_coins:
        top_txt = "🏆 أفضل العملات:\n" + "\n".join([
            f"  `{r[0]}` — نجاح `{r[1]*100:.0f}%` | متوسط `+{r[2]:.2f}%`"
            for r in top_coins
        ]) + "\n━━━━━━━━━━━━━━━━━━━━\n"

    await bot.send_message(
        chat_id=TELEGRAM_CHAT_ID,
        text=(
            f"🌅 *تقرير الصباح | {now.strftime('%A %d %B')}*\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"📊 إحصائيات أمس:\n"
            f"✅ إشارات صحيحة: {stats['success']}/{stats['total']} ({stats['rate']}%)\n"
            f"🏆 أفضل إشارة: `{stats['best_symbol']}` `+{stats['best_pct']}%`\n"
            f"💀 أسوأ إشارة:  `{stats['worst_symbol']}` `{stats['worst_pct']}%`\n"
            f"📈 متوسط أعلى ربح: `+{stats.get('avg_max_gain',0):.2f}%`\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"{paper_line}"
            f"{top_txt}"
            f"💡 {btc_note}\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"⚠️ _رصد تقني فقط، ليس نصيحة مالية_"
        ),
        parse_mode="Markdown"
    )
    daily_alerts.clear()


async def send_weekly_report():
    global last_weekly_date
    now  = datetime.now()
    date = now.date()
    if now.weekday() != WEEKLY_DAY or last_weekly_date == date:
        return
    last_weekly_date = date

    stats = get_weekly_stats()
    if not stats:
        return

    sector_txt = ""
    if sector_performance:
        sector_avg  = {s: statistics.mean(v) for s, v in sector_performance.items() if v}
        best_sector = max(sector_avg, key=sector_avg.get) if sector_avg else None
        if best_sector:
            sector_txt = f"🏆 أفضل قطاع: {best_sector} `{sector_avg[best_sector]:+.2f}%`\n"

    await bot.send_message(
        chat_id=TELEGRAM_CHAT_ID,
        text=(
            f"🏆 *تقرير الأسبوع*\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"الفائز: `{stats['best_symbol']}`\n"
            f"دخول:  `{stats['best_entry']:.6f}`\n"
            f"خرج:   `{stats['best_exit']:.6f}`\n"
            f"الربح: `+{stats['best_pct']}%` 🚀\n"
            f"متوسط أعلى ربح: `+{stats.get('avg_max_gain',0):.2f}%`\n"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"إجمالي الأسبوع:\n"
            f"✅ ناجحة: {stats['success']} | ❌ فاشلة: {stats['total']-stats['success']}\n"
            f"دقة البوت: `{stats['rate']}%`\n"
            f"{sector_txt}"
            f"━━━━━━━━━━━━━━━━━━━━\n"
            f"⚠️ _رصد تقني فقط، ليس نصيحة مالية_"
        ),
        parse_mode="Markdown"
    )


# ──────────────────────────────────────────
# ⚡ الفحص الرئيسي — بالتوازي الكامل
# ──────────────────────────────────────────
async def run_scan():
    global emergency_mode
    scan_start = time.time()
    log.info("🔍 بدء الفحص المتوازي...")

    stable, btc_move = await asyncio.to_thread(btc_is_stable)
    if not stable:
        if btc_move <= -EMERGENCY_BTC_DROP:
            await send_emergency_alert(btc_move)
        else:
            log.info(f"⏸️ BTC غير مستقر ({btc_move:.2f}%) — تأجيل")
        return

    if emergency_mode:
        return

    update_fear_greed()

    # ⚡ جلب العملات من الكاش
    symbols = await get_all_symbols_cached()
    log.info(f"العملات: {len(symbols)} — بدء الفحص المتوازي ({PARALLEL_WORKERS} في نفس الوقت)")

    # ⚡ فحص كل العملات بالتوازي
    tasks   = [analyze_symbol_async(s) for s in symbols]
    results = await asyncio.gather(*tasks, return_exceptions=True)

    found = [
        r for r in results
        if r and not isinstance(r, Exception)
    ]

    # ترتيب بالـ AI Score
    found.sort(key=lambda x: (x.get("ai_score", 0), x["score"], x["vol_ratio"]), reverse=True)

    scan_time = round(time.time() - scan_start, 1)
    log.info(f"⚡ الفحص انتهى في {scan_time}ث | وجد {len(found)} إشارة")

    sent = 0
    for data in found:
        if sent >= MAX_ALERTS_PER_SCAN:
            break
        if can_alert(data["symbol"], data["score"]):
            await send_alert(data)
            await asyncio.sleep(1.5)
            sent += 1

    for sector, syms in sector_signals.items():
        if len(syms) >= 3:
            await send_domino_alert(sector, syms)
            sector_signals[sector] = []

    log.info(f"✅ انتهى | إشارات: {len(found)} | أُرسل: {sent} | وقت: {scan_time}ث")

    await send_hourly_radar(symbols)
    await send_market_mood()
    await send_morning_report()
    await send_weekly_report()


# ──────────────────────────────────────────
# الحلقة الرئيسية
# ──────────────────────────────────────────
async def main():
    # تهيئة الـ semaphore في نفس event loop
    global _scan_semaphore
    _scan_semaphore = asyncio.Semaphore(PARALLEL_WORKERS)

    init_db()
    log.info("🤖 البوت شغّال — نسخة ⚡ سريعة...")

    await bot.send_message(
        chat_id=TELEGRAM_CHAT_ID,
        text=(
            "✅ *بوت التجميع الذكي — نسخة ⚡ Ultra Fast* 🚀\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            f"⚡ فحص متوازٍ: `{PARALLEL_WORKERS}` عملة بنفس الوقت\n"
            f"🔄 كاش Markets: كل `{MARKETS_CACHE_TTL}` ثانية\n"
            f"📡 وقت الدورة: ثوانٍ بدل دقائق!\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            "📊 *المؤشرات التقنية:*\n"
            "  ├ RSI + Stochastic RSI ✅\n"
            "  ├ MACD + Histogram ✅\n"
            "  ├ Bollinger Bands + Squeeze ✅\n"
            "  ├ Fibonacci Retracement ✅\n"
            "  ├ Volume Profile (POC + VA) ✅\n"
            "  ├ RSI Divergence ✅\n"
            "  ├ Multi-Timeframe (1m/5m/15m) ✅\n"
            "  ├ Support & Resistance ✅\n"
            "  ├ Liquidity Zones ✅\n"
            "  └ Market Microstructure ✅\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            "👀 أراقب السوق..."
        ),
        parse_mode="Markdown"
    )

    await asyncio.gather(
        whale_monitor_loop(),
        breakout_monitor_loop(),
        trailing_stop_loop(),
        health_check_loop(),
        main_scan_loop(),
    )


async def main_scan_loop():
    global restart_count
    while True:
        try:
            await run_scan()
        except Exception as e:
            restart_count += 1
            log.error(f"خطأ رئيسي #{restart_count}: {e}")
            if restart_count % 5 == 0:
                try:
                    await bot.send_message(
                        chat_id=TELEGRAM_CHAT_ID,
                        text=f"⚠️ *البوت أعاد التشغيل* (#{restart_count})\n`{str(e)[:100]}`",
                        parse_mode="Markdown"
                    )
                except:
                    pass
        log.info(f"⏳ انتظار {CHECK_INTERVAL}ث...")
        await asyncio.sleep(CHECK_INTERVAL)


if __name__ == "__main__":
    asyncio.run(main())
