import csv
import json
import math
import random
import sys
import threading
import time
from collections import defaultdict, deque
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple

import requests

try:
    import websocket  # type: ignore
except Exception:  # pragma: no cover
    websocket = None

# === Constants ===
SYMBOL = "SOLUSDT"
KLINE_INTERVAL = "1m"
AGG_MINUTES = 12
DAYS_BACK = 30
API_BASE = "https://api.binance.com"
KLINES_ENDPOINT = "/api/v3/klines"
CANDLE_CSV = "solusdt_12min_candles.csv"
PIVOT_SEQ_CSV = "pivot_seq_returns.csv"
PATTERN_MEMORY_FILE = "pattern_memory.json"
SMARTLEARN_LOG_PREFIX = "smartlearn_trades"
SMARTLEARN_RESULTS_CSV = "smartlearn_results.csv"

PIVOT_LOOK = 3  # lookback/lookahead candles
PIVOT_FORWARD = 4
DEFAULT_TP = 0.008  # 0.8%
DEFAULT_SL = 0.008

# === Helpers ===

def log(msg: str) -> None:
    ts = datetime.utcnow().strftime("%Y-%m-%d %H:%M:%S")
    print(f"[{ts}] {msg}")


def safe_float(value: str) -> float:
    try:
        return float(value)
    except Exception:
        return 0.0


# === Data Acquisition ===

def fetch_binance_klines(symbol: str, interval: str, days: int = DAYS_BACK) -> List[Dict]:
    end_time = int(time.time() * 1000)
    start_time = int((datetime.utcnow() - timedelta(days=days)).timestamp() * 1000)
    limit = 1000
    klines: List[Dict] = []
    while start_time < end_time:
        params = {
            "symbol": symbol,
            "interval": interval,
            "startTime": start_time,
            "endTime": end_time,
            "limit": limit,
        }
        try:
            resp = requests.get(API_BASE + KLINES_ENDPOINT, params=params, timeout=10)
            resp.raise_for_status()
            data = resp.json()
        except Exception as exc:  # pragma: no cover - network errors
            log(f"Error fetching klines: {exc}. Retrying in 2s")
            time.sleep(2)
            continue
        if not data:
            break
        for entry in data:
            k = {
                "open_time": int(entry[0]),
                "open": safe_float(entry[1]),
                "high": safe_float(entry[2]),
                "low": safe_float(entry[3]),
                "close": safe_float(entry[4]),
                "volume": safe_float(entry[5]),
                "close_time": int(entry[6]),
            }
            klines.append(k)
        start_time = data[-1][0] + 60_000  # move past last candle
        time.sleep(0.1)
    log(f"Fetched {len(klines)} {interval} candles for {symbol}")
    return klines


def aggregate_candles(candles: List[Dict], minutes: int = AGG_MINUTES) -> List[Dict]:
    if not candles:
        return []
    bucket_ms = minutes * 60 * 1000
    buckets: Dict[int, List[Dict]] = defaultdict(list)
    for c in candles:
        bucket = c["open_time"] - (c["open_time"] % bucket_ms)
        buckets[bucket].append(c)
    agg: List[Dict] = []
    for bucket_start in sorted(buckets):
        group = buckets[bucket_start]
        open_price = group[0]["open"]
        close_price = group[-1]["close"]
        high_price = max(g["high"] for g in group)
        low_price = min(g["low"] for g in group)
        volume = sum(g["volume"] for g in group)
        agg.append(
            {
                "open_time": bucket_start,
                "open": open_price,
                "high": high_price,
                "low": low_price,
                "close": close_price,
                "volume": volume,
            }
        )
    log(f"Aggregated into {len(agg)} candles of {minutes} minutes")
    return agg


def export_candles_csv(candles: List[Dict], filename: str = CANDLE_CSV) -> None:
    headers = ["timestamp", "open", "high", "low", "close", "volume"]
    with open(filename, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(headers)
        for c in candles:
            writer.writerow(
                [
                    datetime.utcfromtimestamp(c["open_time"] / 1000).isoformat(),
                    c["open"],
                    c["high"],
                    c["low"],
                    c["close"],
                    c["volume"],
                ]
            )
    log(f"Saved aggregated candles to {filename}")


# === Feature Extraction ===

def classify_volume(vol: float, vols: List[float]) -> str:
    if not vols:
        return "na"
    sorted_vols = sorted(vols)
    n = len(sorted_vols)
    med = sorted_vols[n // 2]
    p75 = sorted_vols[int(n * 0.75)]
    p90 = sorted_vols[int(n * 0.9)]
    if vol < 0.5 * med:
        return "cmp"
    if vol < p75:
        return "norm"
    if vol < p90:
        return "exp"
    return "ext"


def classify_body(candle: Dict) -> Tuple[str, str]:
    body = candle["close"] - candle["open"]
    spread = candle["high"] - candle["low"]
    spread = spread if spread > 1e-9 else 1e-9
    body_ratio = body / spread
    direction = "up" if body > 0 else "dn" if body < 0 else "doji"
    if abs(body_ratio) < 0.1:
        structure = "pin"
    elif abs(body_ratio) < 0.3:
        structure = "small"
    elif abs(body_ratio) < 0.6:
        structure = "mid"
    else:
        structure = "full"
    return direction, structure


def microtrend(closes: deque) -> str:
    if len(closes) < 4:
        return "flat"
    diff = closes[-1] - closes[0]
    slope = diff / max(abs(closes[0]), 1e-9)
    if slope > 0.01:
        return "up"
    if slope < -0.01:
        return "dn"
    return "flat"


def pattern_key_for_candle(candle: Dict, ctx: Dict) -> str:
    direction, structure = classify_body(candle)
    volume_regime = classify_volume(candle["volume"], ctx.get("volumes", []))
    wick_top = candle["high"] - max(candle["open"], candle["close"])
    wick_bot = min(candle["open"], candle["close"]) - candle["low"]
    wick_ratio = "hi" if wick_top > wick_bot * 1.5 else "lo" if wick_bot > wick_top * 1.5 else "bal"
    mt = microtrend(ctx.get("recent_closes", deque(maxlen=4)))
    return f"{direction}|{structure}|{volume_regime}|{wick_ratio}|{mt}"


def enrich_candles_with_patterns(candles: List[Dict]) -> None:
    volumes = [c["volume"] for c in candles]
    closes = deque(maxlen=4)
    for candle in candles:
        closes.append(candle["close"])
        ctx = {"volumes": volumes, "recent_closes": closes}
        candle["pattern_key"] = pattern_key_for_candle(candle, ctx)


# === Pivot Detection & Mining ===

def detect_pivots(candles: List[Dict]) -> List[Tuple[int, str]]:
    pivots: List[Tuple[int, str]] = []
    for i in range(PIVOT_LOOK, len(candles) - PIVOT_LOOK):
        window_prev = candles[i - PIVOT_LOOK : i]
        window_next = candles[i + 1 : i + 1 + PIVOT_LOOK]
        high = candles[i]["high"]
        low = candles[i]["low"]
        if all(high > w["high"] for w in window_prev + window_next):
            pivots.append((i, "high"))
        if all(low < w["low"] for w in window_prev + window_next):
            pivots.append((i, "low"))
    return pivots


def mine_pivot_sequences(candles: List[Dict]) -> List[Dict]:
    results: Dict[str, Dict] = {}
    pivots = detect_pivots(candles)
    for idx, ptype in pivots:
        if idx < 3 or idx + PIVOT_FORWARD >= len(candles):
            continue
        seq = [candles[idx - 3 + j]["pattern_key"] for j in range(3)]
        seq_key = " ".join(seq)
        entry = candles[idx]["close"]
        exit_price = candles[idx + PIVOT_FORWARD]["close"]
        ret = (exit_price - entry) / entry
        signed_ret = ret if ptype == "low" else -ret
        if seq_key not in results:
            results[seq_key] = {
                "count": 0,
                "pivot_types": set(),
                "returns": [],
            }
        results[seq_key]["count"] += 1
        results[seq_key]["pivot_types"].add(ptype)
        results[seq_key]["returns"].append(round(signed_ret * 100, 4))
    rows: List[Dict] = []
    for seq_key, data in results.items():
        rets = data["returns"]
        mean_ret = sum(rets) / len(rets)
        variance = sum((r - mean_ret) ** 2 for r in rets) / max(len(rets), 1)
        stddev = math.sqrt(variance)
        rows.append(
            {
                "sequence": seq_key,
                "count": data["count"],
                "pivot_types": "/".join(sorted(data["pivot_types"])),
                "mean_return": round(mean_ret, 4),
                "stddev": round(stddev, 4),
                "returns": "|".join(str(r) for r in rets),
            }
        )
    rows.sort(key=lambda x: (x["mean_return"] * x["count"]), reverse=True)
    for idx, row in enumerate(rows, start=1):
        row["rank"] = idx
    return rows


def export_pivot_sequences(rows: List[Dict], filename: str = PIVOT_SEQ_CSV) -> None:
    headers = ["rank", "count", "pivot_types", "mean_return", "stddev", "sequence", "returns"]
    with open(filename, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)
    log(f"Saved pivot sequence returns to {filename}")


# === Pattern Memory ===
@dataclass
class PatternStats:
    count: int = 0
    wins: int = 0
    losses: int = 0
    avg_return: float = 0.0
    confidence: float = 0.0

    def update(self, ret: float, decay: float = 0.0) -> None:
        self.count = max(1, int(self.count * (1 - decay))) + 1
        if ret > 0:
            self.wins += 1
        elif ret < 0:
            self.losses += 1
        self.avg_return = (self.avg_return * (self.count - 1) + ret) / self.count
        total = self.wins + self.losses
        self.confidence = self.wins / total if total else 0.0


class PatternMemory:
    def __init__(self, filename: str = PATTERN_MEMORY_FILE, decay: float = 0.01) -> None:
        self.filename = filename
        self.decay = decay
        self.stats: Dict[str, PatternStats] = {}
        self.load()

    def load(self) -> None:
        try:
            with open(self.filename, "r") as f:
                data = json.load(f)
            for key, val in data.items():
                self.stats[key] = PatternStats(**val)
            log(f"Loaded pattern memory with {len(self.stats)} entries")
        except FileNotFoundError:
            log("Pattern memory file not found; starting fresh")
        except Exception as exc:
            log(f"Error loading pattern memory: {exc}")

    def save(self) -> None:
        data = {k: vars(v) for k, v in self.stats.items()}
        with open(self.filename, "w") as f:
            json.dump(data, f, indent=2)
        log(f"Saved pattern memory with {len(self.stats)} entries")

    def update(self, pattern_key: str, ret: float) -> None:
        if pattern_key not in self.stats:
            self.stats[pattern_key] = PatternStats()
        self.stats[pattern_key].update(ret, self.decay)

    def get(self, pattern_key: str) -> PatternStats:
        return self.stats.get(pattern_key, PatternStats())


# === Backtesting ===
@dataclass
class Trade:
    entry_time: int
    direction: str
    entry: float
    exit: float
    exit_time: int
    ret: float
    reason: str
    pattern: str


class Backtester:
    def __init__(self, candles: List[Dict], pattern_memory: PatternMemory) -> None:
        self.candles = candles
        self.pattern_memory = pattern_memory
        self.trades: List[Trade] = []

    def simulate_trade(self, idx: int, direction: str, tp: float, sl: float) -> Optional[Trade]:
        entry_candle = self.candles[idx]
        entry = entry_candle["close"]
        target = entry * (1 + tp if direction == "long" else 1 - tp)
        stop = entry * (1 - sl if direction == "long" else 1 + sl)
        exit_price = self.candles[idx]["close"]
        exit_time = self.candles[idx]["open_time"]
        for j in range(idx + 1, min(len(self.candles), idx + 8)):
            c = self.candles[j]
            if direction == "long":
                if c["low"] <= stop:
                    exit_price = stop
                    exit_time = c["open_time"]
                    break
                if c["high"] >= target:
                    exit_price = target
                    exit_time = c["open_time"]
                    break
            else:
                if c["high"] >= stop:
                    exit_price = stop
                    exit_time = c["open_time"]
                    break
                if c["low"] <= target:
                    exit_price = target
                    exit_time = c["open_time"]
                    break
            exit_price = c["close"]
            exit_time = c["open_time"]
        ret = (exit_price - entry) / entry
        if direction == "short":
            ret = -ret
        return Trade(
            entry_time=entry_candle["open_time"],
            direction=direction,
            entry=entry,
            exit=exit_price,
            exit_time=exit_time,
            ret=ret,
            reason="pattern",
            pattern=entry_candle.get("pattern_key", ""),
        )

    def run(self, min_count: int, min_conf: float, tp: float, sl: float) -> Tuple[List[Trade], float]:
        self.trades = []
        for idx, candle in enumerate(self.candles[:-8]):
            pat = candle.get("pattern_key", "")
            stats = self.pattern_memory.get(pat)
            if stats.count < min_count or stats.confidence < min_conf:
                continue
            direction = "long" if stats.avg_return >= 0 else "short"
            trade = self.simulate_trade(idx, direction, tp, sl)
            if trade:
                self.trades.append(trade)
                self.pattern_memory.update(pat, trade.ret)
        total_ret = sum(t.ret for t in self.trades)
        log(
            f"Backtest complete: {len(self.trades)} trades, total return {round(total_ret*100,2)}%"
        )
        return self.trades, total_ret


# === SmartLearn ===
@dataclass
class SmartLearnResult:
    params: Dict[str, float]
    total_return: float
    trades: List[Trade] = field(default_factory=list)


class SmartLearnWorker:
    def __init__(self, candles: List[Dict], pattern_memory: PatternMemory):
        self.candles = candles
        self.pattern_memory = pattern_memory

    def run_cycle(self, iterations: int = 5) -> SmartLearnResult:
        best: Optional[SmartLearnResult] = None
        for i in range(iterations):
            params = {
                "tp": round(random.uniform(0.004, 0.02), 4),
                "sl": round(random.uniform(0.004, 0.02), 4),
                "min_count": random.randint(2, 8),
                "min_conf": round(random.uniform(0.45, 0.65), 2),
            }
            log(f"SmartLearn iteration {i+1}/{iterations} params: {params}")
            tester = Backtester(self.candles, self.pattern_memory)
            trades, total_ret = tester.run(
                min_count=params["min_count"],
                min_conf=params["min_conf"],
                tp=params["tp"],
                sl=params["sl"],
            )
            result = SmartLearnResult(params=params, total_return=total_ret, trades=trades)
            if best is None or result.total_return > best.total_return:
                best = result
                log(
                    f"New best return {round(total_ret*100,2)}% with params {params}, trades {len(trades)}"
                )
            self.export_trades(trades, params)
        assert best is not None
        self.append_results(best)
        return best

    def export_trades(self, trades: List[Trade], params: Dict[str, float]) -> None:
        ts = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
        filename = f"{SMARTLEARN_LOG_PREFIX}_{ts}.csv"
        headers = [
            "entry_time",
            "exit_time",
            "direction",
            "entry",
            "exit",
            "return_pct",
            "pattern",
            "reason",
            "tp",
            "sl",
        ]
        with open(filename, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(headers)
            for t in trades:
                writer.writerow(
                    [
                        datetime.utcfromtimestamp(t.entry_time / 1000).isoformat(),
                        datetime.utcfromtimestamp(t.exit_time / 1000).isoformat(),
                        t.direction,
                        t.entry,
                        t.exit,
                        round(t.ret * 100, 4),
                        t.pattern,
                        t.reason,
                        params["tp"],
                        params["sl"],
                    ]
                )
        log(f"Exported trades to {filename}")

    def append_results(self, result: SmartLearnResult) -> None:
        exists = False
        try:
            with open(SMARTLEARN_RESULTS_CSV, "r") as f:
                exists = True
        except FileNotFoundError:
            exists = False
        with open(SMARTLEARN_RESULTS_CSV, "a", newline="") as f:
            writer = csv.writer(f)
            if not exists:
                writer.writerow(["timestamp", "tp", "sl", "min_count", "min_conf", "return_pct", "trades"])
            writer.writerow(
                [
                    datetime.utcnow().isoformat(),
                    result.params["tp"],
                    result.params["sl"],
                    result.params["min_count"],
                    result.params["min_conf"],
                    round(result.total_return * 100, 4),
                    len(result.trades),
                ]
            )
        log(f"Logged SmartLearn result to {SMARTLEARN_RESULTS_CSV}")


# === Paper Trading Simulation ===
class PaperTrader:
    def __init__(self, pattern_memory: PatternMemory):
        self.pattern_memory = pattern_memory
        self.running = False
        self.thread: Optional[threading.Thread] = None
        self.buffer: List[Dict] = []

    def start(self) -> None:
        if self.running:
            log("Paper trading already running")
            return
        if websocket is None:
            log("websocket-client not installed; cannot start paper trading")
            return
        self.running = True
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()
        log("Paper trading started")

    def stop(self) -> None:
        self.running = False
        if self.thread and self.thread.is_alive():
            self.thread.join(timeout=2)
        log("Paper trading stopped")

    def _run(self) -> None:  # pragma: no cover - runtime loop
        stream_url = f"wss://stream.binance.com:9443/ws/{SYMBOL.lower()}@kline_1m"
        try:
            ws = websocket.create_connection(stream_url, timeout=5)
        except Exception as exc:
            log(f"WebSocket connection error: {exc}")
            self.running = False
            return
        agg_bucket_ms = AGG_MINUTES * 60 * 1000
        current_bucket = None
        agg_candle: Dict[str, float] = {}
        volumes: List[float] = []
        closes = deque(maxlen=4)
        while self.running:
            try:
                msg = ws.recv()
                data = json.loads(msg)
                k = data.get("k", {})
                if not k or not k.get("x"):
                    continue
                candle_time = int(k.get("t"))
                bucket = candle_time - (candle_time % agg_bucket_ms)
                candle = {
                    "open_time": candle_time,
                    "open": safe_float(k.get("o", 0)),
                    "high": safe_float(k.get("h", 0)),
                    "low": safe_float(k.get("l", 0)),
                    "close": safe_float(k.get("c", 0)),
                    "volume": safe_float(k.get("v", 0)),
                }
                if current_bucket is None:
                    current_bucket = bucket
                    agg_candle = dict(candle)
                if bucket != current_bucket:
                    closes.append(agg_candle["close"])
                    ctx = {"volumes": volumes, "recent_closes": closes}
                    agg_candle["pattern_key"] = pattern_key_for_candle(agg_candle, ctx)
                    self.pattern_memory.update(agg_candle["pattern_key"], 0.0)
                    log(
                        f"Paper candle {datetime.utcfromtimestamp(current_bucket/1000)} pattern {agg_candle['pattern_key']}"
                    )
                    current_bucket = bucket
                    agg_candle = dict(candle)
                else:
                    agg_candle["high"] = max(agg_candle["high"], candle["high"])
                    agg_candle["low"] = min(agg_candle["low"], candle["low"])
                    agg_candle["close"] = candle["close"]
                    agg_candle["volume"] += candle["volume"]
                    volumes.append(agg_candle["volume"])
            except Exception as exc:
                log(f"Paper trader error: {exc}")
                time.sleep(1)
        try:
            ws.close()
        except Exception:
            pass


# === CLI ===
def initial_setup() -> Tuple[List[Dict], PatternMemory, List[Dict]]:
    klines = fetch_binance_klines(SYMBOL, KLINE_INTERVAL, DAYS_BACK)
    agg = aggregate_candles(klines, AGG_MINUTES)
    export_candles_csv(agg, CANDLE_CSV)
    enrich_candles_with_patterns(agg)
    pattern_rows = mine_pivot_sequences(agg)
    export_pivot_sequences(pattern_rows, PIVOT_SEQ_CSV)
    memory = PatternMemory()
    for c in agg:
        memory.update(c.get("pattern_key", ""), 0.0)
    memory.save()
    return agg, memory, pattern_rows


def show_menu() -> None:
    print(
        """
SOL/USDT Research Terminal
1) Run SmartLearn optimization cycles
2) Start/Stop paper trading
3) Re-run pattern mining/export
4) Show pattern memory summary
5) Exit
"""
    )


def pattern_memory_summary(memory: PatternMemory, top_n: int = 10) -> None:
    items = sorted(
        memory.stats.items(),
        key=lambda kv: kv[1].confidence * kv[1].count,
        reverse=True,
    )[:top_n]
    print("Pattern Memory Top Entries:")
    for key, stats in items:
        print(
            f"{key}: count={stats.count}, win%={round(stats.confidence*100,2)}, avg_ret={round(stats.avg_return*100,3)}%"
        )


def rerun_pattern_mining(candles: List[Dict]) -> None:
    rows = mine_pivot_sequences(candles)
    export_pivot_sequences(rows, PIVOT_SEQ_CSV)


def cli_loop(candles: List[Dict], memory: PatternMemory) -> None:
    paper = PaperTrader(memory)
    while True:
        show_menu()
        choice = input("Select option: ").strip()
        if choice == "1":
            try:
                iterations = int(input("Number of SmartLearn iterations (default 5): ") or "5")
            except ValueError:
                iterations = 5
            worker = SmartLearnWorker(candles, memory)
            best = worker.run_cycle(iterations=iterations)
            log(
                f"Best SmartLearn return {round(best.total_return*100,2)}% with {len(best.trades)} trades"
            )
        elif choice == "2":
            if paper.running:
                paper.stop()
            else:
                paper.start()
        elif choice == "3":
            rerun_pattern_mining(candles)
        elif choice == "4":
            pattern_memory_summary(memory)
        elif choice == "5":
            log("Exiting... saving state")
            memory.save()
            if paper.running:
                paper.stop()
            break
        else:
            print("Invalid choice")


# === Main Entry ===
def main() -> None:
    agg, memory, _ = initial_setup()
    try:
        cli_loop(agg, memory)
    except KeyboardInterrupt:
        log("Interrupted by user; saving state")
        memory.save()


if __name__ == "__main__":
    main()
