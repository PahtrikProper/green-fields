# ================================================================
# SmartLearner v4.0 — Pattern-Evolution Edition
# ================================================================

import os
import sys
import json
import time
import math
import random
import threading
from datetime import datetime, timedelta
import requests
import websocket
import copy

# ================================================================
# CONSTANTS
# ================================================================

BINANCE_REST = "https://api.binance.com"
DEFAULT_SYMBOL = "SOLUSDT"
STREAM_INTERVAL = "1m"
AGGREGATION_MINUTES = 12
BACKTEST_DAYS = 3

INTERVAL_MS = {"1m": 60_000}

BINANCE_API_KEY = "YOUR_KEY"
BINANCE_API_SECRET = "YOUR_SECRET"

# LOCKED TAKE PROFIT
FORCED_TP = 0.0038    # 0.38% TP always

# ================================================================
# LOGGER
# ================================================================

def log(msg):
    ts = datetime.utcnow().strftime("%H:%M:%S")
    print(f"[{ts}] {msg}", flush=True)

# ================================================================
# BASIC MATH UTILITIES
# ================================================================

def mean(values):
    return sum(values) / len(values) if values else 0.0

def median(values):
    if not values:
        return 0.0
    s = sorted(values)
    n = len(s)
    mid = n // 2
    return s[mid] if n % 2 else (s[mid - 1] + s[mid]) / 2

def std(values):
    if not values:
        return 0.0
    m = mean(values)
    return math.sqrt(sum((x - m)**2 for x in values) / len(values))

def percentile(values, pct):
    if not values:
        return 0.0
    s = sorted(values)
    k = int((pct / 100.0) * (len(s) - 1))
    return s[k]

def diff(values):
    if len(values) < 2:
        return [0]
    return [values[i] - values[i-1] for i in range(1, len(values))]

# ================================================================
# SAFE REST GETTER
# ================================================================

def safe_get_json(url, params=None):
    try:
        r = requests.get(url, params=params, timeout=10)
        r.raise_for_status()
        return r.json()
    except Exception as exc:
        log(f"REST error: {exc}")
        return None

# ================================================================
# 1m → 12m AGGREGATION
# ================================================================

def aggregate_to_12m(candles_1m):
    buckets = {}

    for c in candles_1m:
        ts = c["time"]
        if not isinstance(ts, datetime):
            ts = datetime.fromtimestamp(float(ts))

        block = (ts.minute // AGGREGATION_MINUTES) * AGGREGATION_MINUTES
        bucket_ts = ts.replace(minute=block, second=0, microsecond=0)

        if bucket_ts not in buckets:
            buckets[bucket_ts] = {
                "time": bucket_ts,
                "open": c["open"],
                "high": c["high"],
                "low": c["low"],
                "close": c["close"],
                "volume": c["volume"],
            }
        else:
            b = buckets[bucket_ts]
            b["high"] = max(b["high"], c["high"])
            b["low"] = min(b["low"], c["low"])
            b["close"] = c["close"]
            b["volume"] += c["volume"]

    return [buckets[k] for k in sorted(buckets.keys())]

# ================================================================
# HISTORICAL FETCH
# ================================================================

def fetch_historical(symbol=DEFAULT_SYMBOL, interval=STREAM_INTERVAL):
    log(f"Fetching {BACKTEST_DAYS} days of {symbol} (1m)…")

    end = datetime.utcnow()
    start = end - timedelta(days=BACKTEST_DAYS)

    end_ms = int(end.timestamp() * 1000)
    cur = int(start.timestamp() * 1000)

    url = BINANCE_REST + "/api/v3/klines"
    candles = []

    while cur < end_ms:
        raw = safe_get_json(url, {
            "symbol": symbol.upper(),
            "interval": interval,
            "startTime": cur,
            "endTime": end_ms,
            "limit": 1000
        })

        if not raw:
            break

        for r in raw:
            ts = datetime.fromtimestamp(r[0] / 1000)
            if ts >= start:
                candles.append({
                    "time": ts,
                    "open": float(r[1]),
                    "high": float(r[2]),
                    "low": float(r[3]),
                    "close": float(r[4]),
                    "volume": float(r[5]),
                })

        if len(raw) < 1000:
            break

        cur = raw[-1][0] + INTERVAL_MS[interval]

    log(f"Fetched {len(candles)}×1m candles. Aggregating…")

    candles_12m = aggregate_to_12m(candles)
    log(f"Aggregated into {len(candles_12m)}×12m candles.")

    return candles_12m
# ================================================================
# MICROSTRUCTURE DETECTORS
# ================================================================

def _detect_mm_flicker(candles, idx):
    if idx < 4:
        return 0.0

    seq = []
    for i in range(idx - 4, idx + 1):
        o = candles[i]["open"]
        c = candles[i]["close"]
        if c > o: seq.append(1)
        elif c < o: seq.append(-1)
        else: seq.append(0)

    flips = sum(
        1 for i in range(1, 5)
        if seq[i] != 0 and seq[i] != seq[i - 1]
    )
    return flips / 4.0


def _detect_equal_body_cluster(candles, idx):
    if idx < 5:
        return 0.0

    bodies = [
        abs(candles[i]["close"] - candles[i]["open"])
        for i in range(idx - 5, idx + 1)
    ]

    maxb = max(bodies)
    if maxb < 1e-12:
        return 0.0

    cv = std(bodies) / (mean(bodies) + 1e-12)
    return max(0, 1 - cv)


def _wick_parts(o, h, l, c):
    rng = max(h - l, 1e-12)
    upper = (h - max(o, c)) / rng
    lower = (min(o, c) - l) / rng
    return upper, lower


def _detect_arbitrage_reversal(candles, idx):
    if idx < 2:
        return False

    c1, c2, c3 = candles[idx - 2], candles[idx - 1], candles[idx]
    u1, l1w = _wick_parts(c1["open"], c1["high"], c1["low"], c1["close"])
    u2, l2w = _wick_parts(c2["open"], c2["high"], c2["low"], c2["close"])
    u3, l3w = _wick_parts(c3["open"], c3["high"], c3["low"], c3["close"])

    step1 = (u1 > 0.45 or l1w > 0.45)
    step2 = (u2 > 0.45 or l2w > 0.45) and ((u1 > 0.45) != (u2 > 0.45))
    step3 = abs(c3["close"] - c3["open"]) < (c3["high"] - c3["low"]) * 0.3

    return step1 and step2 and step3


def _detect_quote_refresh(candles, idx):
    if idx < 3:
        return False

    ranges = []
    bodies = []
    for i in range(idx - 3, idx):
        o = candles[i]["open"]
        c = candles[i]["close"]
        h = candles[i]["high"]
        l = candles[i]["low"]
        ranges.append(h - l)
        bodies.append(abs(c - o))

    last_rng = candles[idx]["high"] - candles[idx]["low"]
    smalls = sum(1 for b, r in zip(bodies, ranges) if b < r * 0.3)

    return smalls >= 2 and last_rng > mean(ranges) * 1.3

# ================================================================
# STRUCTURE CLASSIFICATION
# ================================================================

def classify_structure(candles, idx):
    if idx < 2:
        return "range"

    start = max(0, idx - 6)
    window = candles[start : idx + 1]

    rngs = [(c["high"] - c["low"]) for c in window]
    median_rng = median(rngs) or 1e-12
    last_rng = rngs[-1]

    if last_rng < median_rng * 0.5:
        return "compression"
    if last_rng > median_rng * 1.6:
        return "expansion"

    if _detect_arbitrage_reversal(candles, idx):
        return "arb_reversal"
    if _detect_quote_refresh(candles, idx):
        return "mm_quote_refresh"

    dirs = []
    for c in window:
        if c["close"] > c["open"]: dirs.append(1)
        elif c["close"] < c["open"]: dirs.append(-1)
        else: dirs.append(0)

    if abs(sum(dirs[-5:])) >= 3:
        return "directional"

    return "range"

# ================================================================
# FEATURE EXTRACTION (with hard sanitisation)
# ================================================================

def extract_pa_features(candles, idx):
    c = candles[idx]

    # --- HARD SANITISATION ---
    try:
        o = float(c["open"])
        h = float(c["high"])
        l = float(c["low"])
        cl = float(c["close"])
        vol = float(c["volume"])
    except Exception:
        log(f"[SANITY ERROR] Bad candle at idx {idx}: {c}")
        return {
            "open": 0, "high": 0, "low": 0, "close": 0,
            "range": 1,
            "body_pct": 0,
            "wick_upper_pct": 0,
            "wick_lower_pct": 0,
            "wick_balance": 0,
            "vol_regime": "normal",
            "volume_pct": 1,
            "flicker": 0,
            "cluster": 0,
            "arb_sig": 0,
            "mm_sig": 0,
            "micro_trend": 0,
            "structure": "range",
            "pattern_key": f"BAD:{idx}"
        }

    rng = max(h - l, 1e-12)
    body_pct = abs(cl - o) / rng
    wick_upper = (h - max(o, cl)) / rng
    wick_lower = (min(o, cl) - l) / rng
    wick_balance = wick_upper - wick_lower

    start = max(0, idx - 50)
    vols = []
    for i in range(start, idx + 1):
        try:
            vols.append(float(candles[i]["volume"]))
        except:
            vols.append(0)

    med_vol = median(vols) or 1.0
    volume_pct = vol / med_vol

    if volume_pct < 0.7: vol_regime = "compression"
    elif volume_pct < 1.3: vol_regime = "normal"
    elif volume_pct < 2.0: vol_regime = "expanded"
    else: vol_regime = "extreme"

    flicker = _detect_mm_flicker(candles, idx)
    cluster = _detect_equal_body_cluster(candles, idx)
    arb = _detect_arbitrage_reversal(candles, idx)
    mm = _detect_quote_refresh(candles, idx)

    closes = []
    for i in range(max(0, idx - 4), idx + 1):
        try:
            closes.append(float(candles[i]["close"]))
        except:
            closes.append(cl)

    diffs = diff(closes)
    microtrend = sum(1 if d > 0 else -1 if d < 0 else 0 for d in diffs)

    structure = classify_structure(candles, idx)

    seq_flag = 1 if cl > o else -1 if cl < o else 0

    pattern_key = (
        f"seq:{seq_flag}"
        f"|vr:{vol_regime}"
        f"|wick:{wick_balance:+.2f}"
        f"|struct:{structure}"
        f"|flick:{flicker:.2f}"
        f"|clust:{cluster:.2f}"
        f"|arb:{int(arb)}"
        f"|mm:{int(mm)}"
    )

    return {
        "open": o, "high": h, "low": l, "close": cl,
        "range": rng,
        "body_pct": body_pct,
        "wick_upper_pct": wick_upper,
        "wick_lower_pct": wick_lower,
        "wick_balance": wick_balance,
        "vol_regime": vol_regime,
        "volume_pct": volume_pct,
        "flicker": flicker,
        "cluster": cluster,
        "arb_sig": arb,
        "mm_sig": mm,
        "micro_trend": microtrend,
        "structure": structure,
        "pattern_key": pattern_key
    }

# ================================================================
# PATTERN MEMORY
# ================================================================

class PatternMemory:
    def __init__(self, path="pattern_memory_pa.json", decay=0.995):
        self.path = path
        self.decay = decay
        self.memory = self._load()

    def _default_entry(self):
        return {
            "wins": 0.0,
            "losses": 0.0,
            "avg_return": 0.0,
            "returns": [],
            "positive_returns": [],
            "negative_returns": [],
            "bars_held": [],
            "flicker_sum": 0.0,
            "flicker_count": 0.0,
            "cluster_sum": 0.0,
            "cluster_count": 0.0,
            "arb_success": 0.0,
            "arb_fail": 0.0,
            "mm_success": 0.0,
            "mm_fail": 0.0,
            "volume_counts": {},
            "structure_counts": {},
            "occurrences": 0.0,
            "pattern_strength": 0.0,
            "confidence": 0.0,
            "last_seen_ts": time.time(),
        }

    def _load(self):
        if not os.path.exists(self.path):
            return {}
        try:
            with open(self.path, "r") as f:
                data = json.load(f)
        except:
            return {}

        cleaned = {}
        for k, e in data.items():
            if not isinstance(e, dict):
                cleaned[k] = self._default_entry()
                continue

            base = self._default_entry()
            for key, val in e.items():
                if key in ("returns","positive_returns","negative_returns","bars_held"):
                    base[key] = val if isinstance(val, list) else []
                else:
                    base[key] = val
            cleaned[k] = base

        return cleaned

    def save(self):
        try:
            with open(self.path, "w") as f:
                json.dump(self.memory, f, indent=2)
        except Exception as e:
            log(f"[PatternMemory] Save error: {e}")
# ================================================================
# PATTERN MEMORY UPDATE
# ================================================================

    def update(self, key, trade_return, feat, bars_held):
        e = self.memory.get(key, self._default_entry())

        # Win/loss tracking
        if trade_return >= 0:
            e["wins"] += 1
            e["positive_returns"].append(trade_return)
        else:
            e["losses"] += 1
            e["negative_returns"].append(trade_return)

        e["bars_held"].append(bars_held)
        e["returns"].append(trade_return)
        e["occurrences"] += 1

        # Smoothed average return
        pr = e["avg_return"]
        e["avg_return"] = pr + (trade_return - pr) / e["occurrences"]

        # Microstructure signals
        e["flicker_sum"] += feat.get("flicker", 0)
        e["flicker_count"] += 1

        e["cluster_sum"] += feat.get("cluster", 0)
        e["cluster_count"] += 1

        if feat.get("arb_sig"):
            if trade_return >= 0: e["arb_success"] += 1
            else: e["arb_fail"] += 1

        if feat.get("mm_sig"):
            if trade_return >= 0: e["mm_success"] += 1
            else: e["mm_fail"] += 1

        # Volume / structure counters
        vr = feat.get("vol_regime", "normal")
        st = feat.get("structure", "range")

        e["volume_counts"][vr] = e["volume_counts"].get(vr, 0) + 1
        e["structure_counts"][st] = e["structure_counts"].get(st, 0) + 1

        # Confidence & strength (base formula)
        wins = e["wins"]
        losses = e["losses"]
        total = max(wins + losses, 1)
        win_rate = wins / total

        bot_factor = 1.0
        if feat.get("arb_sig"):
            bot_factor += (e["arb_success"] - e["arb_fail"]) / max(e["arb_success"]+e["arb_fail"], 1)
        if feat.get("mm_sig"):
            bot_factor += (e["mm_success"] - e["mm_fail"]) / max(e["mm_success"]+e["mm_fail"], 1)

        e["pattern_strength"] = win_rate * e["occurrences"] * bot_factor
        e["confidence"] = e["pattern_strength"]

        e["last_seen_ts"] = time.time()
        self.memory[key] = e


# ================================================================
# TRADE RETURN EVALUATION
# ================================================================

def evaluate_trade(exit_price, entry_price):
    if entry_price <= 0:
        return 0.0
    return (exit_price - entry_price) / entry_price

class CandleStream:
    def __init__(self, symbol=DEFAULT_SYMBOL, interval="1m", on_candle=None):
        self.symbol = symbol.lower()
        self.interval = interval
        self.on_candle = on_candle
        self._ws = None
        self._thread = None
        self._stop = threading.Event()
        self._bucket = None
        self._last_emitted = None

    def start(self):
        self._stop.clear()
        stream = f"{self.symbol}@kline_{self.interval}"
        url = f"wss://stream.binance.com:9443/ws/{stream}"

        self._ws = websocket.WebSocketApp(
            url,
            on_message=self._on_msg,
            on_error=self._on_err,
            on_close=self._on_close
        )

        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()
        log("Live stream started.")

    def stop(self):
        self._stop.set()
        if self._ws:
            try: self._ws.close()
            except: pass
        if self._thread:
            self._thread.join(timeout=2)
        log("Live stream stopped.")

    def _run(self):
        while not self._stop.is_set():
            try:
                self._ws.run_forever(ping_interval=20, ping_timeout=10)
            except Exception as exc:
                log(f"WS error: {exc}")
            time.sleep(1)

    def _on_msg(self, _, msg):
        try:
            data = json.loads(msg)
            k = data.get("k", {})
            if not k or not k.get("x", False):
                return

            ts = datetime.fromtimestamp(k["t"] / 1000)
            block = (ts.minute // AGGREGATION_MINUTES) * AGGREGATION_MINUTES
            bucket_ts = ts.replace(minute=block, second=0, microsecond=0)

            candle = {
                "time": bucket_ts,
                "open": float(k["o"]),
                "high": float(k["h"]),
                "low": float(k["l"]),
                "close": float(k["c"]),
                "volume": float(k["v"]),
            }

            if self._bucket is None:
                self._bucket = candle
                return

            if candle["time"] != self._bucket["time"]:
                if self._bucket["time"] != self._last_emitted:
                    if self.on_candle:
                        self.on_candle(self._bucket)
                    self._last_emitted = self._bucket["time"]
                self._bucket = candle
                return

            b = self._bucket
            b["high"] = max(b["high"], candle["high"])
            b["low"] = min(b["low"], candle["low"])
            b["close"] = candle["close"]
            b["volume"] += candle["volume"]

        except Exception as exc:
            log(f"WS parsing error: {exc}")

    def _on_err(self, _, e):
        log(f"Websocket error: {e}")

    def _on_close(self, *_):
        if not self._stop.is_set():
            log("Websocket closed unexpectedly")
class LivePaperTrader:
    def __init__(self, params, memory, stats):
        self.params = params
        self.memory = memory
        self.stats = stats
        self.reset()

    def reset(self):
        self.position = None
        self.entry_price = 0.0
        self.entry_feat = None
        self.entry_idx = -1
        self.last_ts = None

    def process_live(self, candles):
        if len(candles) < 5:
            return

        idx = len(candles) - 1
        ts = candles[idx]["time"]

        if self.last_ts and ts <= self.last_ts:
            return

        in_pos = (self.position == "LONG")

        d = evaluate_entry_and_exit(
            candles, idx, in_pos,
            self.entry_price, self.entry_idx,
            self.params, self.memory
        )

        # BUY
        if d and d[0] == "BUY":
            self.position = "LONG"
            self.entry_price = d[1]
            self.entry_feat = d[2]
            self.entry_idx = idx
            log(f"[PAPER] BUY {self.entry_price:.4f}")

        # SELL
        elif d and d[0] == "SELL" and self.entry_feat:
            exit_price = d[1]
            reason = d[2]
            bars_held = d[3]
            ret = evaluate_trade(exit_price, self.entry_price)

            self.memory.update(self.entry_feat["pattern_key"], ret, self.entry_feat, bars_held)
            self.stats.record_trade(ret * 100)

            log(f"[PAPER] SELL {exit_price:.4f} ({reason}) → {ret*100:+.2f}%")
            self.reset()

        self.last_ts = ts
class LiveTradeExecutor:
    def __init__(self, symbol=DEFAULT_SYMBOL, base_asset=None, quote_asset=None,
                 api_key=None, api_secret=None):

        from binance.client import Client

        self.symbol = symbol.upper()
        self.api_key = api_key or BINANCE_API_KEY
        self.api_secret = api_secret or BINANCE_API_SECRET
        self.client = Client(self.api_key, self.api_secret)

        if base_asset and quote_asset:
            self.base = base_asset
            self.quote = quote_asset
        else:
            if self.symbol.endswith("USDT"):
                self.base = self.symbol[:-4]
                self.quote = "USDT"
            else:
                self.base = self.symbol[:-3]
                self.quote = self.symbol[-3:]

    def _filters(self):
        info = self.client.get_symbol_info(self.symbol)
        lot = next(f for f in info["filters"] if f["filterType"] == "LOT_SIZE")
        return float(lot["stepSize"]), float(lot["minQty"])

    def _round_qty(self, qty, step):
        return math.floor(qty / step) * step

    def market_buy(self):
        bal = float(self.client.get_asset_balance(self.quote)["free"])
        if bal < 5:
            raise ValueError("Not enough quote to buy.")
        order = self.client.order_market_buy(
            symbol=self.symbol,
            quoteOrderQty=bal
        )
        return order

    def market_sell(self):
        step, min_qty = self._filters()
        bal = float(self.client.get_asset_balance(self.base)["free"])
        qty = self._round_qty(bal, step)
        if qty < min_qty:
            raise ValueError("Not enough asset to sell.")
        order = self.client.order_market_sell(
            symbol=self.symbol,
            quantity=qty
        )
        return order
class LiveAutoTrader:
    def __init__(self, params, memory, executor):
        self.params = params
        self.memory = memory
        self.executor = executor
        self.reset()

    def reset(self):
        self.position = None
        self.entry_price = 0.0
        self.entry_feat = None
        self.entry_idx = -1
        self.last_ts = None

    def process_live(self, candles):
        if len(candles) < 5:
            return

        idx = len(candles) - 1
        ts = candles[idx]["time"]

        if self.last_ts and ts <= self.last_ts:
            return

        in_pos = (self.position == "LONG")

        d = evaluate_entry_and_exit(
            candles, idx, in_pos,
            self.entry_price, self.entry_idx,
            self.params, self.memory
        )

        # BUY
        if d and d[0] == "BUY":
            try:
                self.executor.market_buy()
            except Exception as exc:
                log(f"[LIVE ERROR] BUY FAILED: {exc}")
                return

            self.position = "LONG"
            self.entry_price = d[1]
            self.entry_feat = d[2]
            self.entry_idx = idx

            log(f"[LIVE] BUY at {self.entry_price:.4f}")

        # SELL
        elif d and d[0] == "SELL" and self.entry_feat:
            exit_price = d[1]
            reason = d[2]
            bars_held = d[3]

            try:
                self.executor.market_sell()
            except Exception as exc:
                log(f"[LIVE ERROR] SELL FAILED: {exc}")
                return

            ret = evaluate_trade(exit_price, self.entry_price)
            self.memory.update(self.entry_feat["pattern_key"], ret, self.entry_feat, bars_held)

            log(f"[LIVE] SELL {exit_price:.4f} ({reason}) → {ret*100:+.2f}%")

            self.reset()

        self.last_ts = ts
class SmartLearnerApp:
    def __init__(self):
        log("SmartLearner v4.0 — starting…")

        self.memory = PatternMemory()
        self.paper_stats = PaperStats("paper_stats.json")

        self.params = {
            "tp_pct": FORCED_TP,
            "sl_pct": 0.006,
            "min_occurrences": 2,
            "min_confidence": 0.0,
        }

        self.candles = fetch_historical(DEFAULT_SYMBOL, STREAM_INTERVAL)
        if not self.candles:
            log("ERROR: failed to load history")
            sys.exit(1)

        log(f"Loaded {len(self.candles)} candles.")

        trades, metrics = run_pa_strategy(
            self.candles[:], self.params, self.memory
        )
        log(f"Initial backtest: {metrics}")

        self.live_candles = self.candles[:]
        self.stream = None
        self.paper_tr
# ================================================================
# PATTERN MEMORY (FULL)
# ================================================================

class PatternMemory:
    def __init__(self, path="pattern_memory_pa.json", decay=0.995):
        self.path = path
        self.decay = decay
        self.memory = self._load()

    def _default_entry(self):
        return {
            "wins": 0.0,
            "losses": 0.0,
            "avg_return": 0.0,
            "returns": [],
            "positive_returns": [],
            "negative_returns": [],
            "bars_held": [],
            "flicker_sum": 0.0,
            "flicker_count": 0.0,
            "cluster_sum": 0.0,
            "cluster_count": 0.0,
            "arb_success": 0.0,
            "arb_fail": 0.0,
            "mm_success": 0.0,
            "mm_fail": 0.0,
            "volume_counts": {},
            "structure_counts": {},
            "occurrences": 0.0,
            "pattern_strength": 0.0,
            "confidence": 0.0,
            "last_seen_ts": time.time(),
        }

    def _load(self):
        if not os.path.exists(self.path):
            return {}
        try:
            with open(self.path, "r") as f:
                data = json.load(f)
        except:
            return {}

        cleaned = {}
        for k, e in data.items():
            if not isinstance(e, dict):
                cleaned[k] = self._default_entry()
                continue

            base = self._default_entry()
            for key, val in e.items():
                if key in ("returns", "positive_returns", "negative_returns", "bars_held"):
                    base[key] = val if isinstance(val, list) else []
                else:
                    base[key] = val
            cleaned[k] = base

        return cleaned

    def save(self):
        try:
            with open(self.path, "w") as f:
                json.dump(self.memory, f, indent=2)
        except Exception as e:
            log(f"[PatternMemory] Save error: {e}")

    def decay_all(self):
        now = time.time()
        dead = []
        for k, e in list(self.memory.items()):
            age_days = (now - e.get("last_seen_ts", now)) / 86400
            factor = self.decay ** max(age_days, 0)

            for fld in (
                "wins", "losses", "avg_return",
                "pattern_strength", "occurrences",
                "flicker_sum", "cluster_sum",
                "arb_success", "arb_fail",
                "mm_success", "mm_fail",
            ):
                e[fld] = e.get(fld, 0.0) * factor

            for arr in ("returns", "positive_returns", "negative_returns", "bars_held"):
                if isinstance(e.get(arr), list):
                    e[arr] = e[arr][-500:]

            if e.get("occurrences", 0) < 0.5:
                dead.append(k)

            e["last_seen_ts"] = now

        for k in dead:
            self.memory.pop(k, None)

    def lookup(self, key):
        # <-- THIS is what StrategyContext.pattern_allows_entry calls
        return self.memory.get(key, self._default_entry())

    def update(self, key, trade_return, feat, bars_held):
        e = self.memory.get(key, self._default_entry())

        # Win/loss tracking
        if trade_return >= 0:
            e["wins"] += 1
            e["positive_returns"].append(trade_return)
        else:
            e["losses"] += 1
            e["negative_returns"].append(trade_return)

        e["bars_held"].append(bars_held)
        e["returns"].append(trade_return)
        e["occurrences"] += 1

        # Smoothed average return
        pr = e["avg_return"]
        e["avg_return"] = pr + (trade_return - pr) / e["occurrences"]

        # Microstructure signals
        e["flicker_sum"] += feat.get("flicker", 0)
        e["flicker_count"] += 1

        e["cluster_sum"] += feat.get("cluster", 0)
        e["cluster_count"] += 1

        if feat.get("arb_sig"):
            if trade_return >= 0: e["arb_success"] += 1
            else: e["arb_fail"] += 1

        if feat.get("mm_sig"):
            if trade_return >= 0: e["mm_success"] += 1
            else: e["mm_fail"] += 1

        # Volume / structure counters
        vr = feat.get("vol_regime", "normal")
        st = feat.get("structure", "range")
        e["volume_counts"][vr] = e["volume_counts"].get(vr, 0) + 1
        e["structure_counts"][st] = e["structure_counts"].get(st, 0) + 1

        # Confidence & strength
        wins = e["wins"]
        losses = e["losses"]
        total = max(wins + losses, 1)
        win_rate = wins / total

        bot_factor = 1.0
        if feat.get("arb_sig"):
            bot_factor += (e["arb_success"] - e["arb_fail"]) / max(e["arb_success"]+e["arb_fail"], 1)
        if feat.get("mm_sig"):
            bot_factor += (e["mm_success"] - e["mm_fail"]) / max(e["mm_success"]+e["mm_fail"], 1)

        e["pattern_strength"] = win_rate * e["occurrences"] * bot_factor
        e["confidence"] = e["pattern_strength"]
        e["last_seen_ts"] = time.time()

        self.memory[key] = e

# ================================================================
# STRATEGY CONTEXT (pattern-driven entry engine)
# ================================================================

class StrategyContext:
    def __init__(self, memory, params):
        self.memory = memory
        self.params = params

    def pattern_allows_entry(self, feat):
        entry = self.memory.lookup(feat["pattern_key"])

        occurrences = entry.get("occurrences", 0)
        wins = entry.get("wins", 0)
        losses = entry.get("losses", 0)
        total = max(wins + losses, 1)
        win_rate = wins / total
        conf = entry.get("confidence", 0)

        flick = feat["flicker"]
        cluster = feat["cluster"]
        arb = feat["arb_sig"]
        mm = feat["mm_sig"]
        volume_pct = feat["volume_pct"]
        structure = feat["structure"]
        micro = feat["micro_trend"]

        # Basic history rule
        if occurrences < self.params.get("min_occurrences", 2):
            return True, conf, win_rate

        # Reject low volume regions
        if volume_pct < 0.5:
            return False, conf, win_rate

        # Arb reversal boosts
        if arb and entry.get("arb_success", 0) >= entry.get("arb_fail", 0):
            return True, conf + 1.2, win_rate + 0.05

        # MM quote refresh boosts
        if mm and entry.get("mm_success", 0) >= entry.get("mm_fail", 0):
            return True, conf + 1.0, win_rate + 0.03

        # Flicker breakout
        if flick > 0.6:
            return True, conf + flick, win_rate + 0.04

        # Cluster compression breakout
        if cluster > 0.5:
            return True, conf + cluster, win_rate + 0.02

        # Structure signals
        if structure in ("arb_reversal", "mm_quote_refresh") and micro > 0:
            return True, conf + 0.3, win_rate + 0.02

        # Confidence fallback
        if conf > self.params.get("min_confidence", 0):
            return True, conf, win_rate

        return False, conf, win_rate


# ================================================================
# ENTRY / EXIT DECISION WRAPPER
# ================================================================

def evaluate_entry_and_exit(
    candles, idx,
    in_position,
    entry_price,
    entry_idx,
    params,
    memory
):
    feat = extract_pa_features(candles, idx)
    ctx = StrategyContext(memory, params)
    allow, conf, win_rate = ctx.pattern_allows_entry(feat)

    feat["confidence"] = conf
    feat["win_rate"] = win_rate

    price = candles[idx]["close"]

    # -------------------------------
    # ENTRY LOGIC
    # -------------------------------
    if not in_position and allow:
        bot_power = (
            feat["flicker"] * 0.4 +
            feat["cluster"] * 0.3 +
            (1 if feat["arb_sig"] else 0) * 0.6 +
            (1 if feat["mm_sig"] else 0) * 0.5
        )

        if (
            bot_power > 0.45
            or feat["structure"] in ("arb_reversal", "mm_quote_refresh")
            or feat["vol_regime"] in ("normal", "expanded")
        ):
            return ("BUY", price, feat)

    # -------------------------------
    # EXIT LOGIC — FORCED 0.38% TP
    # -------------------------------
    if in_position:
        move = (price - entry_price) / entry_price

        tp = FORCED_TP                     # always 0.38%
        sl = params.get("sl_pct", 0.006)   # adjustable

        if move >= tp:
            return ("SELL", price, "TP", idx - entry_idx)
        if move <= -sl:
            return ("SELL", price, "SL", idx - entry_idx)

    return None
# ================================================================
# BACKTEST RUNNER — PURE PYTHON
# ================================================================

def run_pa_strategy(candles, params, memory, governor=None):
    trades = []
    in_position = False
    entry_price = 0.0
    entry_idx = 0
    entry_feat = None
    total = len(candles)

    for i in range(total):
        if governor and (i % 50 == 0):
            governor.pace()

        d = evaluate_entry_and_exit(
            candles,
            i,
            in_position,
            entry_price,
            entry_idx,
            params,
            memory
        )

        if not d:
            continue

        # BUY
        if d[0] == "BUY":
            in_position = True
            entry_price = d[1]
            entry_feat = d[2]
            entry_idx = i

            trades.append({
                "type": "BUY",
                "time": candles[i]["time"],
                "price": entry_price,
                "pattern_key": entry_feat["pattern_key"],
                "confidence": entry_feat["confidence"],
                "win_rate": entry_feat["win_rate"],
            })

        # SELL
        elif d[0] == "SELL" and entry_feat:
            exit_price = d[1]
            reason = d[2]
            bars_held = d[3]

            trades.append({
                "type": "SELL",
                "time": candles[i]["time"],
                "price": exit_price,
                "reason": reason,
                "pattern_key": entry_feat["pattern_key"],
                "bars_held": bars_held,
            })

            ret = evaluate_trade(exit_price, entry_price)
            memory.update(entry_feat["pattern_key"], ret, entry_feat, bars_held)

            in_position = False
            entry_feat = None

    metrics = compute_metrics(trades)
    return trades, metrics


# ================================================================
# BACKTEST METRICS
# ================================================================

def compute_metrics(trades):
    wins = 0
    pnl = 1.0
    count = 0

    for i in range(0, len(trades), 2):
        if i + 1 >= len(trades):
            break

        buy = trades[i]
        sell = trades[i + 1]

        if buy["type"] != "BUY" or sell["type"] != "SELL":
            continue

        ret = evaluate_trade(sell["price"], buy["price"])
        pnl *= (1 + ret)
        count += 1
        if ret > 0:
            wins += 1

    return {
        "total_pnl": (pnl - 1) * 100,
        "win_rate": (wins / count * 100) if count else 0.0,
        "num_trades": count,
    }


# ================================================================
# CPU GOVERNOR
# ================================================================

class CpuGovernor:
    def __init__(self, target_utilization=0.8):
        self.target = max(0.05, min(float(target_utilization), 1.0))
        self._last = time.perf_counter()

    def pace(self):
        now = time.perf_counter()
        elapsed = now - self._last
        self._last = now

        intended = elapsed / self.target
        delay = intended - elapsed
        if delay > 0:
            time.sleep(delay)


# ================================================================
# EVOLUTIONARY MUTATION ENGINE
# ================================================================

def mutate_pattern_memory(base_mem, intensity=0.08):
    mem = copy.deepcopy(base_mem)

    for key, e in mem.items():

        # Confidence mutation
        e["confidence"] *= random.uniform(1 - intensity, 1 + intensity)

        # Pattern strength mutation
        e["pattern_strength"] *= random.uniform(1 - intensity, 1 + intensity)

        # Win/loss drift
        if random.random() < 0.3:
            e["wins"] *= random.uniform(0.95, 1.05)
        if random.random() < 0.3:
            e["losses"] *= random.uniform(0.95, 1.05)

        # Flicker/cluster drift
        if "flicker_sum" in e:
            e["flicker_sum"] *= random.uniform(1 - intensity, 1 + intensity)
        if "cluster_sum" in e:
            e["cluster_sum"] *= random.uniform(1 - intensity, 1 + intensity)

        # Arb/MM reinforcement shifts
        if random.random() < 0.2:
            e["arb_success"] += random.uniform(-0.3, +0.3)
        if random.random() < 0.2:
            e["mm_success"] += random.uniform(-0.3, +0.3)

        # Selective forgetting of weak patterns
        if e.get("occurrences", 0) < 2 and random.random() < 0.15:
            e["confidence"] *= 0.8
            e["pattern_strength"] *= 0.8

        # Volume/structure mutation
        if random.random() < 0.1:
            for vr in e["volume_counts"]:
                e["volume_counts"][vr] *= random.uniform(0.9, 1.1)
        if random.random() < 0.1:
            for st in e["structure_counts"]:
                e["structure_counts"][st] *= random.uniform(0.9, 1.1)

        # Ensure sane values
        e["confidence"] = max(0.0, float(e["confidence"]))
        e["pattern_strength"] = max(0.0, float(e["pattern_strength"]))

    return mem


# ================================================================
# MUTATION SCORING FUNCTION
# ================================================================

def score_memory(candles, mutated_memory, params):
    class TempMem:
        def __init__(self, data):
            self.memory = data
        def lookup(self, key):
            return self.memory.get(key, {})
        def update(self, *args, **kwargs):
            pass

    _, metrics = run_pa_strategy(
        candles, params, TempMem(mutated_memory)
    )

    pnl = metrics["total_pnl"]
    win = metrics["win_rate"]
    trades = metrics["num_trades"]

    # Weighted score
    return pnl * 1.8 + win * 1.2 + trades * 0.8


# ================================================================
# SMARTLEARN — PATTERN EVOLUTION ENGINE
# ================================================================

class SmartLearnWorker:
    def __init__(self, candles, memory, iterations=500, intensity=0.08):
        self.candles = candles
        self.memory = memory
        self.iter = iterations
        self.intensity = intensity
        self.abort = False

    def stop(self):
        self.abort = True

    def run(self):
        log(f"Pattern-Evolution SmartLearn started — {self.iter} iterations")

        base = copy.deepcopy(self.memory.memory)
        params = {
            "tp_pct": FORCED_TP, 
            "sl_pct": 0.006,
            "min_occurrences": 2,
            "min_confidence": 0
        }

        best_score = score_memory(self.candles, base, params)
        best_mem = base

        for i in range(1, self.iter + 1):
            if self.abort:
                log("SmartLearn aborted.")
                break

            mutated = mutate_pattern_memory(best_mem, self.intensity)
            s = score_memory(self.candles, mutated, params)

            if s > best_score:
                best_score = s
                best_mem = mutated

            if i % 20 == 0:
                log(f"Iteration {i}/{self.iter} — best_score {best_score:.2f}")

        log("Pattern evolution complete.")
        return best_mem, best_score


# ================================================================
# SMARTLEARN CYCLE MANAGER
# ================================================================

class SmartLearnCycleManager:
    def __init__(self, candles, memory, cycles=5, iterations=500, intensity=0.08):
        self.candles = candles
        self.memory = memory
        self.cycles = cycles
        self.iter = iterations
        self.intensity = intensity
        self.active = False

    def start(self):
        self.active = True

        for c in range(1, self.cycles + 1):
            if not self.active:
                break

            log(f"=== Evolution Cycle {c}/{self.cycles} ===")

            worker = SmartLearnWorker(
                self.candles,
                self.memory,
                iterations=self.iter,
                intensity=self.intensity
            )

            best_mem, best_score = worker.run()

            # commit improved memory
            self.memory.memory = best_mem
            self.memory.save()

            log(f"[Cycle {c}] Best Score: {best_score:.2f}")

        log("All SmartLearn evolution cycles completed.")

    def stop(self):
        self.active = False
        log("Stopping SmartLearn…")
# ================================================================
# LIVE CANDLESTREAM — AGGREGATES LIVE 1m → 12m
# ================================================================

class CandleStream:
    def __init__(self, symbol=DEFAULT_SYMBOL, interval="1m", on_candle=None):
        self.symbol = symbol.lower()
        self.interval = interval
        self.on_candle = on_candle

        self._ws = None
        self._thread = None
        self._stop = threading.Event()

        self._bucket = None
        self._last_emitted = None

    def start(self):
        self._stop.clear()
        stream = f"{self.symbol}@kline_{self.interval}"
        url = f"wss://stream.binance.com:9443/ws/{stream}"

        self._ws = websocket.WebSocketApp(
            url,
            on_message=self._on_msg,
            on_error=self._on_err,
            on_close=self._on_close
        )

        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()
        log("Live stream started.")

    def stop(self):
        self._stop.set()
        if self._ws:
            try: self._ws.close()
            except: pass
        if self._thread:
            self._thread.join(timeout=2)
        log("Live stream stopped.")

    def _run(self):
        while not self._stop.is_set():
            try:
                self._ws.run_forever(ping_interval=20, ping_timeout=10)
            except Exception as exc:
                log(f"WS error, retrying: {exc}")
            if self._stop.is_set():
                break
            time.sleep(1)

    def _on_msg(self, _, msg):
        try:
            data = json.loads(msg)
            k = data.get("k", {})
            if not k or not k.get("x", False):
                return

            ts = datetime.fromtimestamp(k["t"] / 1000)
            block = (ts.minute // AGGREGATION_MINUTES) * AGGREGATION_MINUTES
            bucket_ts = ts.replace(minute=block, second=0, microsecond=0)

            candle = {
                "time": bucket_ts,
                "open": float(k["o"]),
                "high": float(k["h"]),
                "low": float(k["l"]),
                "close": float(k["c"]),
                "volume": float(k["v"]),
            }

            # New bucket?
            if self._bucket is None:
                self._bucket = candle
                return

            if candle["time"] != self._bucket["time"]:
                # flush previous bucket
                if self._bucket["time"] != self._last_emitted:
                    if self.on_candle:
                        self.on_candle(self._bucket)
                    self._last_emitted = self._bucket["time"]
                self._bucket = candle
                return

            # update current bucket
            b = self._bucket
            b["high"] = max(b["high"], candle["high"])
            b["low"] = min(b["low"], candle["low"])
            b["close"] = candle["close"]
            b["volume"] += candle["volume"]

        except Exception as exc:
            log(f"WS parsing error: {exc}")

    def _on_err(self, _, e):
        log(f"Websocket error: {e}")

    def _on_close(self, *_):
        if not self._stop.is_set():
            log("Websocket closed unexpectedly")


# ================================================================
# LIVE PAPER TRADER
# ================================================================

class LivePaperTrader:
    def __init__(self, params, memory, stats):
        self.params = params
        self.memory = memory
        self.stats = stats
        self.reset()

    def reset(self):
        self.position = None
        self.entry_price = 0.0
        self.entry_feat = None
        self.entry_idx = -1
        self.last_ts = None

    def process_live(self, candles):
        if len(candles) < 5:
            return

        idx = len(candles) - 1
        ts = candles[idx]["time"]

        if self.last_ts and ts <= self.last_ts:
            return

        in_pos = (self.position == "LONG")

        d = evaluate_entry_and_exit(
            candles, idx, in_pos,
            self.entry_price, self.entry_idx,
            self.params, self.memory
        )

        # BUY
        if d and d[0] == "BUY":
            self.position = "LONG"
            self.entry_price = d[1]
            self.entry_feat = d[2]
            self.entry_idx = idx
            log(f"[PAPER] BUY {self.entry_price:.4f}")

        # SELL
        elif d and d[0] == "SELL" and self.entry_feat:
            exit_price = d[1]
            reason = d[2]
            bars_held = d[3]
            ret = evaluate_trade(exit_price, self.entry_price)

            self.memory.update(self.entry_feat["pattern_key"], ret, self.entry_feat, bars_held)
            self.stats.record_trade(ret * 100)

            log(f"[PAPER] SELL {exit_price:.4f} ({reason}) → {ret*100:+.2f}%")

            self.reset()

        self.last_ts = ts


# ================================================================
# LIVE TRADER — BINANCE EXECUTION ENGINE
# ================================================================

class LiveTradeExecutor:
    def __init__(self, symbol=DEFAULT_SYMBOL, base_asset=None, quote_asset=None,
                 api_key=None, api_secret=None):

        try:
            from binance.client import Client
        except:
            raise ImportError("python-binance not installed")

        self.symbol = symbol.upper()
        self.api_key = api_key or BINANCE_API_KEY
        self.api_secret = api_secret or BINANCE_API_SECRET

        self.client = Client(self.api_key, self.api_secret)

        if base_asset and quote_asset:
            self.base = base_asset
            self.quote = quote_asset
        else:
            if self.symbol.endswith("USDT"):
                self.base = self.symbol[:-4]
                self.quote = "USDT"
            else:
                self.base = self.symbol[:-3]
                self.quote = self.symbol[-3:]

    def _filters(self):
        info = self.client.get_symbol_info(self.symbol)
        lot = next(f for f in info["filters"] if f["filterType"] == "LOT_SIZE")
        return float(lot["stepSize"]), float(lot["minQty"])

    def _round(self, qty, step):
        return math.floor(qty / step) * step

    # MARKET BUY entire balance
    def market_buy(self):
        step, _ = self._filters()
        bal = float(self.client.get_asset_balance(self.quote)["free"])

        if bal < 5:
            raise ValueError("Not enough quote to buy.")

        order = self.client.order_market_buy(
            symbol=self.symbol,
            quoteOrderQty=bal
        )

        qty = float(order.get("executedQty", 0))
        qty = self._round(qty, step)

        log(f"[LIVE] BUY qty={qty}")
        return order, qty

    def limit_sell(self, qty, price):
        order = self.client.order_limit_sell(
            symbol=self.symbol,
            quantity=qty,
            price=f"{price:.4f}"
        )
        log(f"[LIVE] LIMIT SELL placed at {price:.4f}")
        return order

    def cancel(self, order_id):
        try:
            self.client.cancel_order(symbol=self.symbol, orderId=order_id)
        except:
            pass

    def market_sell(self, qty):
        order = self.client.order_market_sell(
            symbol=self.symbol,
            quantity=qty
        )
        log(f"[LIVE] MARKET SELL qty={qty}")
        return order


# ================================================================
# LIVE AUTO TRADER (AUTO-TP + SL OVERRIDE)
# ================================================================

class LiveAutoTrader:
    def __init__(self, params, memory, executor):
        self.params = params
        self.memory = memory
        self.executor = executor
        self.reset()

    def reset(self):
        self.position = None
        self.entry_price = 0.0
        self.entry_feat = None
        self.entry_idx = -1
        self.limit_order_id = None
        self.qty = 0
        self.last_ts = None

    def process_live(self, candles):
        if len(candles) < 5:
            return

        idx = len(candles) - 1
        ts = candles[idx]["time"]

        if self.last_ts and ts <= self.last_ts:
            return
        self.last_ts = ts

        in_pos = (self.position == "LONG")

        d = evaluate_entry_and_exit(
            candles, idx, in_pos,
            self.entry_price, self.entry_idx,
            self.params, self.memory
        )

        # -----------------------------
        # BUY → confirm → place TP LIMIT
        # -----------------------------
        if d and d[0] == "BUY":
            try:
                order, qty = self.executor.market_buy()
                self.qty = qty
            except Exception as exc:
                log(f"[LIVE ERROR] BUY FAILED: {exc}")
                return

            self.position = "LONG"
            self.entry_price = d[1]
            self.entry_feat = d[2]
            self.entry_idx = idx

            tp_price = self.entry_price * (1 + FORCED_TP)
            o = self.executor.limit_sell(qty, tp_price)
            self.limit_order_id = o["orderId"]

            log(f"[LIVE] BUY {self.entry_price:.4f} / TP {tp_price:.4f}")

        # -----------------------------
        # SELL logic — SL overrides TP
        # -----------------------------
        elif d and d[0] == "SELL" and self.entry_feat:
            exit_price = d[1]
            reason = d[2]
            bars_held = d[3]

            # Cancel TP if exists
            if self.limit_order_id:
                self.executor.cancel(self.limit_order_id)
                self.limit_order_id = None

            # MARKET SELL
            try:
                self.executor.market_sell(self.qty)
            except Exception as exc:
                log(f"[LIVE ERROR] SELL FAILED: {exc}")
                return

            ret = evaluate_trade(exit_price, self.entry_price)
            self.memory.update(self.entry_feat["pattern_key"], ret, self.entry_feat, bars_held)

            log(f"[LIVE] EXIT {exit_price:.4f} ({reason}) → {ret*100:+.2f}%")

            self.reset()

# ================================================================
# PAPER STATS — TRACK PAPER TRADING PERFORMANCE
# ================================================================

class PaperStats:
    def __init__(self, path="paper_stats.json"):
        self.path = path
        self.data = {
            "trades": 0,
            "wins": 0,
            "losses": 0,
            "pnl_history": [],
            "last_update": None,
        }
        self._load()

    def _load(self):
        try:
            if os.path.exists(self.path):
                with open(self.path, "r") as f:
                    self.data = json.load(f)
        except:
            pass

    def save(self):
        try:
            with open(self.path, "w") as f:
                json.dump(self.data, f, indent=2)
        except:
            pass

    def record_trade(self, pnl_pct):
        """
        pnl_pct is percentage return for a completed trade
        example: +0.52 or -0.33
        """
        self.data["trades"] += 1
        if pnl_pct > 0:
            self.data["wins"] += 1
        else:
            self.data["losses"] += 1

        self.data["pnl_history"].append(pnl_pct)
        self.data["last_update"] = datetime.utcnow().isoformat()

        self.save()

    def summary(self):
        t = self.data["trades"]
        w = self.data["wins"]
        l = self.data["losses"]
        avg = sum(self.data["pnl_history"]) / len(self.data["pnl_history"]) if self.data["pnl_history"] else 0

        return {
            "trades": t,
            "wins": w,
            "losses": l,
            "win_rate": (w / t * 100) if t else 0,
            "avg_return": avg,
            "last_update": self.data["last_update"],
        }

# ================================================================
# SMARTLEARNER APPLICATION MAIN CLASS
# ================================================================

class SmartLearnerApp:
    def __init__(self):
        log("SmartLearner v4.0 — Pattern Evolution Engine starting…")

        # Memory + paper stats
        self.memory = PatternMemory()
        self.paper_stats = PaperStats("paper_stats.json")

        # Default params (TP locked)
        self.params = {
            "tp_pct": FORCED_TP,
            "sl_pct": 0.006,
            "min_occurrences": 2,
            "min_confidence": 0.0,
        }

        # Load historical
        self.candles = fetch_historical(DEFAULT_SYMBOL, STREAM_INTERVAL)
        if not self.candles:
            log("ERROR: no historical data.")
            sys.exit(1)

        log(f"Loaded {len(self.candles)} candles.")

        # Initial backtest
        trades, metrics = run_pa_strategy(self.candles[:], self.params, self.memory)
        log(f"Initial PnL: {metrics['total_pnl']:.2f}% "
            f"| Trades: {metrics['num_trades']}")

        self.live_candles = self.candles[:]
        self.stream = None
        self.paper_trader = None
        self.live_trader = None

    # ----------------------------------------------
    # LIVE CALLBACK
    # ----------------------------------------------

    def on_live_candle(self, c):
        # insert or update candle
        for i in range(len(self.live_candles)):
            if self.live_candles[i]["time"] == c["time"]:
                self.live_candles[i] = c
                break
        else:
            self.live_candles.append(c)
            self.live_candles.sort(key=lambda x: x["time"])

        if self.paper_trader:
            self.paper_trader.process_live(self.live_candles)

        if self.live_trader:
            self.live_trader.process_live(self.live_candles)

    # ----------------------------------------------
    # SMARTLEARN PATTERN EVOLUTION
    # ----------------------------------------------

    def start_smartlearn(self):
        log("Starting PATTERN-EVOLUTION SmartLearn…")

        cycles = 5
        iterations = 500
        intensity = 0.08

        scm = SmartLearnCycleManager(
            self.candles[:],
            self.memory,
            cycles=cycles,
            iterations=iterations,
            intensity=intensity
        )
        scm.start()

        log("SmartLearn complete.")

    # ----------------------------------------------
    # PAPER TRADING
    # ----------------------------------------------

    def start_paper(self):
        if self.stream is None:
            self.stream = CandleStream(
                DEFAULT_SYMBOL, STREAM_INTERVAL,
                on_candle=self.on_live_candle
            )
            self.stream.start()

        self.paper_trader = LivePaperTrader(
            self.params, self.memory, self.paper_stats
        )

        log("Paper trading started.")

    def stop_paper(self):
        self.paper_trader = None
        log("Paper trading stopped.")

    # ----------------------------------------------
    # LIVE TRADING
    # ----------------------------------------------

    def start_live(self):
        try:
            if DEFAULT_SYMBOL.endswith("USDT"):
                base = DEFAULT_SYMBOL[:-4]
                quote = "USDT"
            else:
                base = DEFAULT_SYMBOL[:-3]
                quote = DEFAULT_SYMBOL[-3:]

            executor = LiveTradeExecutor(
                DEFAULT_SYMBOL,
                base_asset=base,
                quote_asset=quote,
                api_key=BINANCE_API_KEY,
                api_secret=BINANCE_API_SECRET
            )
        except Exception as exc:
            log(f"Live trading unavailable: {exc}")
            return

        if self.stream is None:
            self.stream = CandleStream(
                DEFAULT_SYMBOL, STREAM_INTERVAL,
                on_candle=self.on_live_candle
            )
            self.stream.start()

        self.live_trader = LiveAutoTrader(
            self.params, self.memory, executor
        )

        log("Live trading started.")

    def stop_live(self):
        self.live_trader = None
        log("Live trading stopped.")

    # ----------------------------------------------
    # STOP STREAM
    # ----------------------------------------------

    def stop_stream(self):
        if self.stream:
            self.stream.stop()
            self.stream = None

    # ----------------------------------------------
    # TERMINAL MENU
    # ----------------------------------------------

    def menu(self):
        while True:
            print("\n" + "="*60)
            print(" SMARTLEARNER v4.0 — PATTERN EVOLUTION ")
            print("="*60)
            print("1. Run SmartLearn (pattern evolution)")
            print("2. Start Paper Trading")
            print("3. Start Live Trading")
            print("4. Stop Paper Trading")
            print("5. Stop Live Trading")
            print("6. Show Parameters")
            print("7. Backtest")
            print("8. Exit")
            print("="*60)

            choice = input("Select an option: ").strip()

            if choice == "1":
                self.start_smartlearn()
            elif choice == "2":
                self.start_paper()
            elif choice == "3":
                self.start_live()
            elif choice == "4":
                self.stop_paper()
            elif choice == "5":
                self.stop_live()
            elif choice == "6":
                print(json.dumps(self.params, indent=2))
            elif choice == "7":
                _, metrics = run_pa_strategy(
                    self.candles[:], self.params, self.memory
                )
                print(json.dumps(metrics, indent=2))
            elif choice == "8":
                log("Exiting…")
                self.stop_live()
                self.stop_paper()
                self.stop_stream()
                self.memory.save()
                break
            else:
                print("Invalid option.")


# ================================================================
# ENTRY POINT
# ================================================================

if __name__ == "__main__":
    app = SmartLearnerApp()
    app.menu()
