#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
LAXIRONIX SNIPER v3.0
Professional Solana memecoin trading infrastructure.
"""

import asyncio
import json
import time
import os
import sys
import re
import math
import hmac
import base64
import hashlib
import random
import logging
import argparse
import sqlite3
import signal
import threading
import statistics
import traceback
import textwrap
from abc import ABC, abstractmethod
from collections import deque, defaultdict, OrderedDict
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta, timezone
from enum import Enum, IntEnum
from functools import wraps, lru_cache, partial
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple, Union
from urllib.parse import urlencode, urlparse

import aiohttp
import requests
import websockets

try:
    import yaml
    HAS_YAML = True
except ImportError:
    HAS_YAML = False

try:
    from dotenv import load_dotenv
    load_dotenv()
    HAS_DOTENV = True
except ImportError:
    HAS_DOTENV = False


# ═══════════════════════════════════════════════════════════════════════════════
#  CONSTANTS
# ═══════════════════════════════════════════════════════════════════════════════

VERSION          = "3.0.0"
APP_NAME         = "Laxironix Sniper"
LAMPORTS_PER_SOL = 1_000_000_000
DEFAULT_DECIMALS = 6

SOL_MINT  = "So11111111111111111111111111111111111111112"
USDC_MINT = "EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v"
USDT_MINT = "Es9vMFrzaCERmJfrF4H2FYD4KCoNkY11McCe8BenwNYB"

PUMP_PROGRAM      = "6EF8rrecthR5Dkzon8Nwu78hRvfCKubJ14M5uBEwF6P"
PUMPSWAP_PROGRAM  = "pAMMBay6oceH9fJKBRHGP5D4bD4sWpmSwMn52FMfXEA"
RAYDIUM_V4        = "675kPX9MHTjS2zt1qfr1NYHuzeLXfQM9H24wFSUt1Mp8"
JUPITER_V6        = "JUP6LkbZbjS1jKKwapdHNy74zcZ3tLUZoi5QNyVTaV4"
TOKEN_PROGRAM     = "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"
TOKEN_2022        = "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb"

RPC_MAINNET       = "https://api.mainnet-beta.solana.com"
RPC_WS_MAINNET    = "wss://api.mainnet-beta.solana.com"
JUPITER_QUOTE     = "https://quote-api.jup.ag/v6/quote"
JUPITER_SWAP      = "https://quote-api.jup.ag/v6/swap"
JUPITER_PRICE     = "https://price.jup.ag/v6/price"
JUPITER_TOKENS    = "https://tokens.jup.ag/tokens"
BIRDEYE_API       = "https://public-api.birdeye.so"
DEXSCREENER_API   = "https://api.dexscreener.com/latest/dex"
HELIUS_API        = "https://api.helius.xyz/v0"
SOLSCAN_API       = "https://public-api.solscan.io"
JITO_BLOCK_ENGINE = "https://mainnet.block-engine.jito.wtf"

BASE58_ALPHABET = set("123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz")

DATA_DIR     = Path.home() / ".lax_sniper"
DB_FILE      = DATA_DIR / "sniper.db"
LOG_FILE     = DATA_DIR / "sniper.log"
CONFIG_FILE  = DATA_DIR / "config.yaml"
STATE_FILE   = DATA_DIR / "state.json"

DATA_DIR.mkdir(parents=True, exist_ok=True)


# ═══════════════════════════════════════════════════════════════════════════════
#  ENUMS
# ═══════════════════════════════════════════════════════════════════════════════

class LogLevel(IntEnum):
    DEBUG   = 10
    INFO    = 20
    WARNING = 30
    ERROR   = 40

class Mode(Enum):
    PAPER     = "paper"
    LIVE      = "live"
    BACKTEST  = "backtest"
    COPYTRADE = "copytrade"

class Side(Enum):
    BUY  = "buy"
    SELL = "sell"

class TokenStatus(Enum):
    DISCOVERED    = "discovered"
    SECURITY_PASS = "security_pass"
    SECURITY_FAIL = "security_fail"
    SCREENED_IN   = "screened_in"
    SCREENED_OUT  = "screened_out"
    BOUGHT        = "bought"
    SOLD          = "sold"
    REJECTED      = "rejected"

class Signal(Enum):
    STRONG_BUY  = 2
    BUY         = 1
    NEUTRAL     = 0
    SELL        = -1
    STRONG_SELL = -2

class PositionStatus(Enum):
    OPEN      = "open"
    CLOSED    = "closed"
    LIQUIDATED = "liquidated"

class ExitReason(Enum):
    STOP_LOSS     = "stop_loss"
    TAKE_PROFIT_1 = "take_profit_1"
    TAKE_PROFIT_2 = "take_profit_2"
    TRAILING_STOP = "trailing_stop"
    TIME_STOP     = "time_stop"
    SIGNAL        = "signal"
    MANUAL        = "manual"
    RUG_DETECTED  = "rug_detected"
    SHUTDOWN      = "shutdown"


# ═══════════════════════════════════════════════════════════════════════════════
#  COLORS
# ═══════════════════════════════════════════════════════════════════════════════

class C:
    _on = sys.stdout.isatty() and os.environ.get("NO_COLOR") is None
    RESET = "\033[0m" if _on else ""
    BOLD  = "\033[1m" if _on else ""
    DIM   = "\033[2m" if _on else ""
    RED   = "\033[31m" if _on else ""
    GREEN = "\033[32m" if _on else ""
    YEL   = "\033[33m" if _on else ""
    BLU   = "\033[34m" if _on else ""
    MAG   = "\033[35m" if _on else ""
    CYA   = "\033[36m" if _on else ""
    WHT   = "\033[37m" if _on else ""
    BRED  = "\033[91m" if _on else ""
    BGRN  = "\033[92m" if _on else ""
    BYEL  = "\033[93m" if _on else ""
    BCYA  = "\033[96m" if _on else ""
    BMAG  = "\033[95m" if _on else ""


# ═══════════════════════════════════════════════════════════════════════════════
#  LOGGING
# ═══════════════════════════════════════════════════════════════════════════════

class ColorFormatter(logging.Formatter):
    COLORS = {
        "DEBUG":    C.DIM,
        "INFO":     C.CYA,
        "WARNING":  C.YEL,
        "ERROR":    C.RED,
        "CRITICAL": C.BRED,
    }

    def format(self, record):
        c = self.COLORS.get(record.levelname, "")
        record.levelname = f"{c}{record.levelname}{C.RESET}"
        return super().format(record)

handler_file = logging.FileHandler(LOG_FILE, encoding="utf-8")
handler_file.setFormatter(logging.Formatter(
    "%(asctime)s [%(levelname)s] %(name)s: %(message)s",
    "%Y-%m-%d %H:%M:%S"))

handler_console = logging.StreamHandler(sys.stdout)
handler_console.setFormatter(ColorFormatter(
    "%(asctime)s %(levelname)s %(message)s", "%H:%M:%S"))

logging.basicConfig(level=logging.INFO, handlers=[handler_file, handler_console])
log = logging.getLogger("sniper")


# ═══════════════════════════════════════════════════════════════════════════════
#  UTILITIES
# ═══════════════════════════════════════════════════════════════════════════════

def is_valid_solana_address(addr: str) -> bool:
    """Valide une adresse Solana (base58, 32-44 chars)."""
    if not addr or not isinstance(addr, str):
        return False
    addr = addr.strip()
    if not (32 <= len(addr) <= 44):
        return False
    return all(c in BASE58_ALPHABET for c in addr)

def short_addr(addr: str, n: int = 6) -> str:
    """Tronque une adresse pour l'affichage."""
    if not addr or len(addr) <= n * 2 + 3:
        return addr
    return f"{addr[:n]}…{addr[-n:]}"

def fmt_sol(n: float) -> str:
    """Formate un montant SOL."""
    return f"{n:.6f}"

def fmt_pct(n: float) -> str:
    """Formate un pourcentage signé."""
    return f"{n:+.2f}%"

def now_ts() -> int:
    return int(time.time())

def now_utc() -> datetime:
    return datetime.now(timezone.utc)

def rate_limit(calls_per_second: float = 10.0):
    """Décorateur de rate limiting thread-safe."""
    min_interval = 1.0 / calls_per_second
    lock = threading.Lock()
    last = [0.0]

    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            with lock:
                elapsed = time.time() - last[0]
                wait = min_interval - elapsed
                if wait > 0:
                    time.sleep(wait)
                last[0] = time.time()
            return func(*args, **kwargs)
        return wrapper
    return decorator


def retry(max_attempts: int = 3, delay: float = 1.0, backoff: float = 2.0,
          exceptions: Tuple = (Exception,)):
    """Décorateur de retry avec backoff exponentiel."""
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            attempt = 0
            current_delay = delay
            while attempt < max_attempts:
                try:
                    return func(*args, **kwargs)
                except exceptions as e:
                    attempt += 1
                    if attempt >= max_attempts:
                        raise
                    log.debug(f"{func.__name__} retry {attempt}/{max_attempts} "
                              f"dans {current_delay:.1f}s : {e}")
                    time.sleep(current_delay)
                    current_delay *= backoff
        return wrapper
    return decorator


class TTLCache:
    """Cache avec expiration."""
    def __init__(self, ttl: float = 5.0, max_size: int = 1000):
        self.ttl = ttl
        self.max_size = max_size
        self._data: OrderedDict = OrderedDict()
        self._lock = threading.Lock()

    def get(self, key):
        with self._lock:
            if key not in self._data:
                return None
            value, ts = self._data[key]
            if time.time() - ts > self.ttl:
                del self._data[key]
                return None
            self._data.move_to_end(key)
            return value

    def set(self, key, value):
        with self._lock:
            self._data[key] = (value, time.time())
            self._data.move_to_end(key)
            if len(self._data) > self.max_size:
                self._data.popitem(last=False)


class RateLimiter:
    """Sliding window rate limiter."""
    def __init__(self, max_calls: int, window_seconds: float):
        self.max_calls = max_calls
        self.window = window_seconds
        self.calls: deque = deque()
        self._lock = threading.Lock()

    def allow(self) -> bool:
        with self._lock:
            now = time.time()
            while self.calls and self.calls[0] < now - self.window:
                self.calls.popleft()
            if len(self.calls) < self.max_calls:
                self.calls.append(now)
                return True
            return False


# ═══════════════════════════════════════════════════════════════════════════════
#  CONFIG
# ═══════════════════════════════════════════════════════════════════════════════

DEFAULT_CONFIG = {
    "version": VERSION,
    "mode": "paper",
    "network": "mainnet",

    "rpc": {
        "http": RPC_MAINNET,
        "ws":   RPC_WS_MAINNET,
        "helius_api_key": "",
        "birdeye_api_key": "",
        "solscan_api_key": "",
        "rate_limit_rps": 20,
    },

    "wallet": {
        "public_key": "",
        "private_key_env": "SNIPER_PRIVATE_KEY",
        "jito_tip_lamports": 10000,
    },

    "trading": {
        "buy_amount_sol": 0.05,
        "max_position_sol": 0.10,
        "max_concurrent_positions": 3,
        "slippage_bps": 500,
        "priority_fee_lamports": 50000,
        "min_liquidity_usd": 5000,
        "use_jito": True,
    },

    "risk": {
        "stop_loss_pct": 25.0,
        "take_profit_1_pct": 50.0,
        "take_profit_1_size": 0.5,
        "take_profit_2_pct": 200.0,
        "trailing_stop_pct": 15.0,
        "use_trailing_stop": True,
        "max_hold_seconds": 300,
        "daily_loss_limit_pct": 20.0,
        "cooldown_seconds": 5,
    },

    "security": {
        "require_mint_revoked": True,
        "require_freeze_revoked": True,
        "require_lp_locked": True,
        "max_holder_concentration_pct": 40.0,
        "max_top10_holder_pct": 30.0,
        "min_holder_count": 20,
        "min_age_seconds": 15,
        "max_age_seconds": 900,
        "block_blacklisted_creators": True,
    },

    "screening": {
        "min_score": 60,
        "weight_liquidity": 30,
        "weight_timing": 15,
        "weight_bonding": 25,
        "weight_age": 20,
        "weight_holder_growth": 10,
    },

    "monitor": {
        "interval_seconds": 5,
        "position_check_seconds": 3,
        "history_points": 500,
        "price_source": "jupiter",
    },

    "copy_trading": {
        "enabled": False,
        "smart_wallets": [],
        "min_winrate": 0.6,
        "min_pnl_sol": 10.0,
        "copy_size_pct": 0.5,
    },

    "notifications": {
        "discord_webhook": "",
        "telegram_token": "",
        "telegram_chat_id": "",
        "notify_on_buy": True,
        "notify_on_sell": True,
        "notify_on_error": True,
        "notify_on_rug": True,
    },

    "database": {
        "path": str(DB_FILE),
    },

    "logging": {
        "level": "INFO",
        "file": str(LOG_FILE),
    },
}


class Config:
    """Configuration YAML/JSON avec accès par chemin pointé."""

    def __init__(self, path: Path = CONFIG_FILE):
        self.path = path
        self.data: Dict = {}
        self.load()

    def load(self):
        if self.path.exists():
            try:
                with open(self.path, "r", encoding="utf-8") as f:
                    if self.path.suffix in (".yaml", ".yml") and HAS_YAML:
                        raw = yaml.safe_load(f) or {}
                    else:
                        raw = json.load(f)
                self.data = self._deep_merge(dict(DEFAULT_CONFIG), raw)
            except Exception as e:
                log.warning(f"Config invalide ({e}), utilisation des défauts")
                self.data = dict(DEFAULT_CONFIG)
        else:
            self.data = dict(DEFAULT_CONFIG)
            self.save()

    def _deep_merge(self, base: Dict, over: Dict) -> Dict:
        out = dict(base)
        for k, v in over.items():
            if k in out and isinstance(out[k], dict) and isinstance(v, dict):
                out[k] = self._deep_merge(out[k], v)
            else:
                out[k] = v
        return out

    def save(self):
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                if self.path.suffix in (".yaml", ".yml") and HAS_YAML:
                    yaml.safe_dump(self.data, f, sort_keys=False, allow_unicode=True)
                else:
                    json.dump(self.data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            log.error(f"Save config : {e}")

    def get(self, path: str, default: Any = None) -> Any:
        cur = self.data
        for part in path.split("."):
            if isinstance(cur, dict) and part in cur:
                cur = cur[part]
            else:
                return default
        return cur

    def set(self, path: str, value: Any):
        parts = path.split(".")
        cur = self.data
        for part in parts[:-1]:
            if part not in cur or not isinstance(cur[part], dict):
                cur[part] = {}
            cur = cur[part]
        cur[parts[-1]] = value
        self.save()


# ═══════════════════════════════════════════════════════════════════════════════
#  DATA MODELS
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class TokenCandidate:
    mint: str
    symbol: str = ""
    name: str = ""
    creator: str = ""
    pool_address: str = ""
    created_at: int = 0
    initial_liquidity_sol: float = 0.0
    bonding_curve_pct: float = 0.0
    holder_count: int = 0
    top10_holder_pct: float = 0.0
    status: TokenStatus = TokenStatus.DISCOVERED
    security_data: Dict = field(default_factory=dict)
    screening_score: float = 0.0
    screening_breakdown: Dict = field(default_factory=dict)
    rejected_reason: str = ""

    def to_dict(self) -> Dict:
        d = asdict(self)
        d["status"] = self.status.value
        return d


@dataclass
class Position:
    mint: str
    symbol: str
    entry_price: float
    quantity: float
    entry_time: int
    entry_sol: float
    high_water: float = 0.0
    low_water: float = 0.0
    tp1_hit: bool = False
    tp1_size: float = 0.0
    realized_sol: float = 0.0
    fees_sol: float = 0.0
    status: PositionStatus = PositionStatus.OPEN
    entry_txid: str = ""

    def __post_init__(self):
        if self.high_water == 0:
            self.high_water = self.entry_price
        if self.low_water == 0:
            self.low_water = self.entry_price

    def unrealized_pnl_pct(self, price: float) -> float:
        if self.entry_price == 0:
            return 0.0
        return ((price - self.entry_price) / self.entry_price) * 100

    def unrealized_pnl_sol(self, price: float) -> float:
        return self.entry_sol * (self.unrealized_pnl_pct(price) / 100)

    def age_seconds(self) -> int:
        return now_ts() - self.entry_time


@dataclass
class Trade:
    mint: str
    symbol: str
    side: Side
    entry_price: float
    exit_price: float
    quantity: float
    entry_time: int
    exit_time: int
    pnl_sol: float
    pnl_pct: float
    fees_sol: float
    reason: ExitReason
    entry_txid: str = ""
    exit_txid: str = ""

    def duration(self) -> int:
        return self.exit_time - self.entry_time


@dataclass
class Candle:
    timestamp: int
    open: float
    high: float
    low: float
    close: float
    volume: float = 0.0


# ═══════════════════════════════════════════════════════════════════════════════
#  DATABASE
# ═══════════════════════════════════════════════════════════════════════════════

class Database:
    """Couche SQLite thread-safe."""

    def __init__(self, path: Path):
        self.path = path
        path.parent.mkdir(parents=True, exist_ok=True)
        self._lock = threading.RLock()
        self._conn = sqlite3.connect(str(path), check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._conn.execute("PRAGMA journal_mode=WAL")
        self._init_schema()

    def _init_schema(self):
        with self._lock:
            c = self._conn.cursor()
            c.executescript("""
                CREATE TABLE IF NOT EXISTS candidates (
                    mint TEXT PRIMARY KEY,
                    symbol TEXT, name TEXT, creator TEXT,
                    status TEXT, score REAL,
                    payload TEXT, created_at INTEGER
                );
                CREATE TABLE IF NOT EXISTS positions (
                    mint TEXT PRIMARY KEY,
                    symbol TEXT, entry_price REAL, quantity REAL,
                    entry_time INTEGER, entry_sol REAL,
                    high_water REAL, low_water REAL,
                    tp1_hit INTEGER, realized_sol REAL,
                    status TEXT, payload TEXT
                );
                CREATE TABLE IF NOT EXISTS trades (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    mint TEXT, symbol TEXT, side TEXT,
                    entry_price REAL, exit_price REAL, quantity REAL,
                    entry_time INTEGER, exit_time INTEGER,
                    pnl_sol REAL, pnl_pct REAL, fees_sol REAL,
                    reason TEXT, entry_txid TEXT, exit_txid TEXT
                );
                CREATE TABLE IF NOT EXISTS equity (
                    ts INTEGER PRIMARY KEY, equity REAL,
                    cash REAL, positions_value REAL
                );
                CREATE TABLE IF NOT EXISTS signals (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    mint TEXT, strategy TEXT, signal TEXT,
                    price REAL, reason TEXT, ts INTEGER
                );
                CREATE TABLE IF NOT EXISTS blacklist (
                    address TEXT PRIMARY KEY, reason TEXT, ts INTEGER
                );
                CREATE INDEX IF NOT EXISTS idx_trades_mint ON trades(mint);
                CREATE INDEX IF NOT EXISTS idx_trades_time ON trades(exit_time);
                CREATE INDEX IF NOT EXISTS idx_signals_mint ON signals(mint);
            """)
            self._conn.commit()

    def execute(self, sql: str, params: Tuple = ()) -> sqlite3.Cursor:
        with self._lock:
            cur = self._conn.execute(sql, params)
            self._conn.commit()
            return cur

    def fetchone(self, sql: str, params: Tuple = ()) -> Optional[sqlite3.Row]:
        with self._lock:
            return self._conn.execute(sql, params).fetchone()

    def fetchall(self, sql: str, params: Tuple = ()) -> List[sqlite3.Row]:
        with self._lock:
            return self._conn.execute(sql, params).fetchall()

    def save_candidate(self, c: TokenCandidate):
        self.execute(
            """INSERT OR REPLACE INTO candidates
               (mint, symbol, name, creator, status, score, payload, created_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?)""",
            (c.mint, c.symbol, c.name, c.creator,
             c.status.value, c.screening_score,
             json.dumps(c.to_dict()), c.created_at or now_ts())
        )

    def save_position(self, p: Position):
        self.execute(
            """INSERT OR REPLACE INTO positions
               (mint, symbol, entry_price, quantity, entry_time, entry_sol,
                high_water, low_water, tp1_hit, realized_sol, status, payload)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (p.mint, p.symbol, p.entry_price, p.quantity, p.entry_time,
             p.entry_sol, p.high_water, p.low_water, int(p.tp1_hit),
             p.realized_sol, p.status.value, json.dumps(asdict(p)))
        )

    def close_position(self, mint: str):
        self.execute("DELETE FROM positions WHERE mint = ?", (mint,))

    def save_trade(self, t: Trade):
        self.execute(
            """INSERT INTO trades
               (mint, symbol, side, entry_price, exit_price, quantity,
                entry_time, exit_time, pnl_sol, pnl_pct, fees_sol,
                reason, entry_txid, exit_txid)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (t.mint, t.symbol, t.side.value, t.entry_price, t.exit_price,
             t.quantity, t.entry_time, t.exit_time, t.pnl_sol, t.pnl_pct,
             t.fees_sol, t.reason.value, t.entry_txid, t.exit_txid)
        )

    def save_equity(self, equity: float, cash: float, positions_value: float):
        self.execute(
            "INSERT OR REPLACE INTO equity (ts, equity, cash, positions_value) "
            "VALUES (?, ?, ?, ?)",
            (now_ts(), equity, cash, positions_value)
        )

    def save_signal(self, mint: str, strategy: str, signal: Signal,
                    price: float, reason: str):
        self.execute(
            "INSERT INTO signals (mint, strategy, signal, price, reason, ts) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (mint, strategy, signal.name, price, reason, now_ts())
        )

    def is_blacklisted(self, address: str) -> bool:
        row = self.fetchone("SELECT 1 FROM blacklist WHERE address = ?", (address,))
        return row is not None

    def blacklist(self, address: str, reason: str):
        self.execute(
            "INSERT OR IGNORE INTO blacklist (address, reason, ts) VALUES (?, ?, ?)",
            (address, reason, now_ts())
        )

    def stats(self) -> Dict:
        row = self.fetchone("""
            SELECT
              COUNT(*) AS total,
              COALESCE(SUM(CASE WHEN pnl_sol > 0 THEN 1 ELSE 0 END), 0) AS wins,
              COALESCE(SUM(CASE WHEN pnl_sol <= 0 THEN 1 ELSE 0 END), 0) AS losses,
              COALESCE(SUM(pnl_sol), 0) AS total_pnl,
              COALESCE(SUM(CASE WHEN pnl_sol > 0 THEN pnl_sol ELSE 0 END), 0) AS gross_win,
              COALESCE(SUM(CASE WHEN pnl_sol < 0 THEN -pnl_sol ELSE 0 END), 0) AS gross_loss,
              COALESCE(MAX(pnl_sol), 0) AS best,
              COALESCE(MIN(pnl_sol), 0) AS worst
            FROM trades
        """)
        if not row:
            return {"total": 0, "wins": 0, "losses": 0, "win_rate": 0.0,
                    "pnl": 0.0, "profit_factor": 0.0, "best": 0.0, "worst": 0.0}
        total = row["total"] or 0
        return {
            "total":         total,
            "wins":          row["wins"] or 0,
            "losses":        row["losses"] or 0,
            "win_rate":      (row["wins"] / total * 100) if total else 0.0,
            "pnl":           row["total_pnl"] or 0.0,
            "profit_factor": (row["gross_win"] / row["gross_loss"]) if row["gross_loss"] else 0.0,
            "best":          row["best"] or 0.0,
            "worst":         row["worst"] or 0.0,
        }


# ═══════════════════════════════════════════════════════════════════════════════
#  RPC CLIENT (Solana)
# ═══════════════════════════════════════════════════════════════════════════════

class SolanaRPC:
    """Client JSON-RPC Solana avec rate limiting."""

    def __init__(self, cfg: Config):
        self.url = cfg.get("rpc.http", RPC_MAINNET)
        self.ws_url = cfg.get("rpc.ws", RPC_WS_MAINNET)
        self.session = requests.Session()
        self.session.headers.update({
            "Content-Type": "application/json",
            "User-Agent": f"LaxSniper/{VERSION}",
        })
        self._id = 0
        self.limiter = RateLimiter(
            cfg.get("rpc.rate_limit_rps", 20), 1.0)

    @retry(max_attempts=3, delay=0.5)
    def _call(self, method: str, params: List = None) -> Any:
        self._id += 1
        payload = {"jsonrpc": "2.0", "id": self._id,
                   "method": method, "params": params or []}
        r = self.session.post(self.url, json=payload, timeout=15)
        r.raise_for_status()
        data = r.json()
        if "error" in data:
            raise RuntimeError(f"RPC error: {data['error']}")
        return data.get("result")

    def get_balance(self, address: str) -> int:
        """Retourne le solde en lamports."""
        res = self._call("getBalance", [address, {"commitment": "confirmed"}])
        return int(res.get("value", 0)) if isinstance(res, dict) else 0

    def get_sol_balance(self, address: str) -> float:
        return self.get_balance(address) / LAMPORTS_PER_SOL

    def get_account_info(self, address: str) -> Optional[Dict]:
        res = self._call("getAccountInfo", [address, {"encoding": "jsonParsed"}])
        return res.get("value") if res else None

    def get_mint_info(self, mint: str) -> Optional[Dict]:
        """Lit les autorités et décimales d'un mint SPL."""
        info = self.get_account_info(mint)
        if not info:
            return None
        try:
            parsed = info["data"]["parsed"]["info"]
            return {
                "mint_authority":   parsed.get("mintAuthority"),
                "freeze_authority": parsed.get("freezeAuthority"),
                "decimals":         int(parsed.get("decimals", 6)),
                "supply":           int(parsed.get("supply", "0")),
                "is_initialized":   parsed.get("isInitialized", False),
            }
        except (KeyError, TypeError):
            return None

    def get_token_accounts(self, wallet: str) -> List[Dict]:
        """Retourne les comptes SPL token d'un wallet."""
        res = self._call("getTokenAccountsByOwner", [
            wallet,
            {"programId": TOKEN_PROGRAM},
            {"encoding": "jsonParsed", "commitment": "confirmed"},
        ])
        if not res:
            return []
        out = []
        for acc in res.get("value", []) or []:
            try:
                info = acc["account"]["data"]["parsed"]["info"]
                out.append({
                    "mint":   info["mint"],
                    "amount": float(info["tokenAmount"]["uiAmount"] or 0),
                    "raw":    int(info["tokenAmount"]["amount"]),
                    "decimals": int(info["tokenAmount"]["decimals"]),
                })
            except (KeyError, TypeError):
                continue
        return out

    def get_signatures(self, address: str, limit: int = 20) -> List[Dict]:
        res = self._call("getSignaturesForAddress", [address, {"limit": limit}])
        return res or []

    def get_transaction(self, sig: str) -> Optional[Dict]:
        return self._call("getTransaction", [
            sig, {"encoding": "jsonParsed", "maxSupportedTransactionVersion": 0}
        ])

    def get_latest_blockhash(self) -> Optional[str]:
        res = self._call("getLatestBlockhash", [{"commitment": "confirmed"}])
        if res and "value" in res:
            return res["value"].get("blockhash")
        return None

    def get_token_largest_accounts(self, mint: str) -> List[Dict]:
        """Récupère les plus gros holders d'un token."""
        res = self._call("getTokenLargestAccounts", [mint])
        if not res:
            return []
        return res.get("value", []) or []


# ═══════════════════════════════════════════════════════════════════════════════
#  JUPITER CLIENT
# ═══════════════════════════════════════════════════════════════════════════════

class JupiterClient:
    """Client pour l'agrégateur Jupiter V6."""

    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.session = requests.Session()
        self.session.headers.update({"User-Agent": f"LaxSniper/{VERSION}"})
        self.cache = TTLCache(ttl=3.0)

    @retry(max_attempts=2, delay=0.3)
    def get_quote(self, input_mint: str, output_mint: str,
                  amount_lamports: int, slippage_bps: int = 500) -> Optional[Dict]:
        """Obtient un devis de swap."""
        params = {
            "inputMint":         input_mint,
            "outputMint":        output_mint,
            "amount":            str(amount_lamports),
            "slippageBps":       str(slippage_bps),
            "onlyDirectRoutes":  "false",
            "asLegacyTransaction": "false",
        }
        r = self.session.get(JUPITER_QUOTE, params=params, timeout=10)
        r.raise_for_status()
        return r.json()

    def get_price(self, mint: str) -> Optional[float]:
        """Prix USD d'un token, avec cache 3s."""
        cached = self.cache.get(f"price:{mint}")
        if cached is not None:
            return cached
        try:
            r = self.session.get(JUPITER_PRICE, params={"ids": mint}, timeout=8)
            r.raise_for_status()
            data = r.json()
            entry = data.get("data", {}).get(mint)
            if entry and "price" in entry:
                price = float(entry["price"])
                self.cache.set(f"price:{mint}", price)
                return price
        except Exception as e:
            log.debug(f"Jupiter price error: {e}")
        return None

    def get_prices(self, mints: List[str]) -> Dict[str, Optional[float]]:
        if not mints:
            return {}
        try:
            r = self.session.get(JUPITER_PRICE,
                                 params={"ids": ",".join(mints)}, timeout=10)
            r.raise_for_status()
            data = r.json().get("data", {})
            return {m: (float(data[m]["price"]) if m in data and "price" in data[m] else None)
                    for m in mints}
        except Exception:
            return {m: None for m in mints}

    def get_token_metadata(self, mint: str) -> Optional[Dict]:
        """Récupère les métadonnées d'un token (symbol, name, logo)."""
        try:
            r = self.session.get(JUPITER_TOKENS, timeout=15)
            r.raise_for_status()
            tokens = r.json()
            for tok in tokens:
                if tok.get("address") == mint:
                    return tok
        except Exception:
            pass
        return None

    def search_tokens(self, query: str, limit: int = 10) -> List[Dict]:
        """Recherche dans la liste des tokens Jupiter."""
        try:
            r = self.session.get(JUPITER_TOKENS, timeout=15)
            r.raise_for_status()
            tokens = r.json()
            q = query.upper()
            results = [t for t in tokens if q in t.get("symbol", "").upper()
                       or q in t.get("name", "").upper()]
            return results[:limit]
        except Exception:
            return []


# ═══════════════════════════════════════════════════════════════════════════════
#  BIRDEYE CLIENT
# ═══════════════════════════════════════════════════════════════════════════════

class BirdeyeClient:
    """Client API Birdeye pour la data on-chain avancée."""

    def __init__(self, cfg: Config):
        self.api_key = cfg.get("rpc.birdeye_api_key", "")
        self.session = requests.Session()
        self.session.headers.update({
            "X-API-KEY": self.api_key,
            "x-chain":   "solana",
            "User-Agent": f"LaxSniper/{VERSION}",
        })

    def _enabled(self) -> bool:
        return bool(self.api_key)

    def token_security(self, mint: str) -> Optional[Dict]:
        """Score de sécurité d'un token."""
        if not self._enabled():
            return None
        try:
            r = self.session.get(f"{BIRDEYE_API}/defi/token_security",
                                 params={"address": mint}, timeout=10)
            if r.status_code == 200:
                return r.json().get("data")
        except Exception:
            pass
        return None

    def token_overview(self, mint: str) -> Optional[Dict]:
        """Overview complet d'un token."""
        if not self._enabled():
            return None
        try:
            r = self.session.get(f"{BIRDEYE_API}/defi/token_overview",
                                 params={"address": mint}, timeout=10)
            if r.status_code == 200:
                return r.json().get("data")
        except Exception:
            pass
        return None

    def token_holders(self, mint: str, limit: int = 20) -> Optional[Dict]:
        """Distribution des holders."""
        if not self._enabled():
            return None
        try:
            r = self.session.get(f"{BIRDEYE_API}/defi/v3/token/holder",
                                 params={"address": mint, "limit": limit},
                                 timeout=10)
            if r.status_code == 200:
                return r.json().get("data")
        except Exception:
            pass
        return None

    def trending_tokens(self, limit: int = 20) -> List[Dict]:
        """Tokens en tendance sur les dernières 24h."""
        if not self._enabled():
            return []
        try:
            r = self.session.get(f"{BIRDEYE_API}/defi/token_trending",
                                 params={"sort_by": "rank", "sort_type": "asc",
                                         "offset": 0, "limit": limit},
                                 timeout=10)
            if r.status_code == 200:
                return r.json().get("data", {}).get("tokens", [])
        except Exception:
            pass
        return []


# ═══════════════════════════════════════════════════════════════════════════════
#  DEXSCREENER CLIENT
# ═══════════════════════════════════════════════════════════════════════════════

class DexScreenerClient:
    """Client DexScreener pour les prix et la liquidité."""

    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update({"User-Agent": f"LaxSniper/{VERSION}"})
        self.cache = TTLCache(ttl=10.0)

    def get_token_pairs(self, mint: str) -> List[Dict]:
        """Retourne toutes les paires pour un mint."""
        cached = self.cache.get(f"pairs:{mint}")
        if cached is not None:
            return cached
        try:
            r = self.session.get(f"{DEXSCREENER_API}/tokens/{mint}", timeout=10)
            r.raise_for_status()
            pairs = r.json().get("pairs") or []
            self.cache.set(f"pairs:{mint}", pairs)
            return pairs
        except Exception:
            return []

    def get_best_pair(self, mint: str) -> Optional[Dict]:
        """Retourne la paire avec le plus de liquidité."""
        pairs = self.get_token_pairs(mint)
        if not pairs:
            return None
        return max(pairs, key=lambda p:
                   float(p.get("liquidity", {}).get("usd", 0) or 0))

    def get_price_usd(self, mint: str) -> Optional[float]:
        pair = self.get_best_pair(mint)
        if pair:
            price = pair.get("priceUsd")
            if price:
                return float(price)
        return None

    def get_liquidity_usd(self, mint: str) -> float:
        pair = self.get_best_pair(mint)
        if pair:
            return float(pair.get("liquidity", {}).get("usd", 0) or 0)
        return 0.0

    def get_volume_24h(self, mint: str) -> float:
        pair = self.get_best_pair(mint)
        if pair:
            return float(pair.get("volume", {}).get("h24", 0) or 0)
        return 0.0

    def get_price_change_24h(self, mint: str) -> float:
        pair = self.get_best_pair(mint)
        if pair:
            return float(pair.get("priceChange", {}).get("h24", 0) or 0)
        return 0.0

    def get_new_pairs(self) -> List[Dict]:
        """Récupère les dernières paires créées."""
        try:
            r = self.session.get(f"{DEXSCREENER_API}/search",
                                 params={"q": "SOL"}, timeout=10)
            r.raise_for_status()
            return r.json().get("pairs", [])[:50]
        except Exception:
            return []


# ═══════════════════════════════════════════════════════════════════════════════
#  HELIUS CLIENT (Webhooks, enhanced API)
# ═══════════════════════════════════════════════════════════════════════════════

class HeliusClient:
    """Client Helius pour les webhooks et l'API enhanced."""

    def __init__(self, cfg: Config):
        self.api_key = cfg.get("rpc.helius_api_key", "")
        self.session = requests.Session()

    def _enabled(self) -> bool:
        return bool(self.api_key)

    def get_assets_by_owner(self, wallet: str) -> List[Dict]:
        """Assets (NFTs + tokens) d'un wallet."""
        if not self._enabled():
            return []
        try:
            r = self.session.post(
                f"{HELIUS_API}/token-metadata?api-key={self.api_key}",
                json={"mintAccounts": [wallet], "includeOffChain": False},
                timeout=15)
            if r.status_code == 200:
                return r.json()
        except Exception:
            pass
        return []

    def get_transactions(self, address: str, limit: int = 20) -> List[Dict]:
        """Historique de transactions parsé."""
        if not self._enabled():
            return []
        try:
            r = self.session.get(
                f"{HELIUS_API}/addresses/{address}/transactions",
                params={"api-key": self.api_key, "limit": limit},
                timeout=15)
            if r.status_code == 200:
                return r.json()
        except Exception:
            pass
        return []


# ═══════════════════════════════════════════════════════════════════════════════
#  JITO CLIENT (MEV protection)
# ═══════════════════════════════════════════════════════════════════════════════

class JitoClient:
    """Client pour l'envoi de bundles via Jito (protection MEV)."""

    def __init__(self, cfg: Config):
        self.tip_lamports = cfg.get("wallet.jito_tip_lamports", 10000)
        self.session = requests.Session()

    def get_tip_accounts(self) -> List[str]:
        """Retourne les comptes tip officiels Jito."""
        try:
            r = self.session.get(
                f"{JITO_BLOCK_ENGINE}/api/v1/bundles",
                timeout=10)
            # Note: Jito n'expose pas toujours cet endpoint publiquement
        except Exception:
            pass
        # Adresses tip officielles connues
        return [
            "96gYZGLnJYVFmbjzopPSU6QiEV5fGqZNyN9nmNhvrZU5",
            "HFqU5x63VTqvQss8hp11i4wVV8bD44PvwucfZ2bU7gRe",
            "Cw8CFyM9FkoMi7K7Crf6HNQqf4uEMzpKw6QNghXLvLkY",
            "ADaUMid9yfUytqMBgopwjb2DTLSokTSzL1zt6iGPaS49",
        ]

    def build_bundle(self, transactions: List[str]) -> Dict:
        """Construit un bundle Jito."""
        return {
            "jsonrpc": "2.0",
            "id":      1,
            "method":  "sendBundle",
            "params":  [transactions],
        }


# ═══════════════════════════════════════════════════════════════════════════════
#  WEBSOCKET DISCOVERY
# ═══════════════════════════════════════════════════════════════════════════════

class WebSocketDiscovery:
    """
    Écoute les logs du program Pump.fun pour détecter les créations.
    """
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.ws_url = cfg.get("rpc.ws", RPC_WS_MAINNET)
        self.program_id = PUMP_PROGRAM
        self.queue: asyncio.Queue = asyncio.Queue()
        self.seen = set()
        self.running = False
        self.reconnect_delay = 2.0

    async def _subscribe(self, ws):
        payload = {
            "jsonrpc": "2.0",
            "id":      1,
            "method":  "logsSubscribe",
            "params":  [
                {"mentions": [self.program_id]},
                {"commitment": "processed"},
            ],
        }
        await ws.send(json.dumps(payload))

    async def _process_log(self, data: Dict):
        params = data.get("params", {})
        result = params.get("result", {})
        value = result.get("value", {})
        logs = value.get("logs", []) or []
        signature = value.get("signature", "")

        # Détection de création Pump.fun
        is_create = any("Instruction: Create" in log for log in logs)
        if not is_create:
            return

        # Extraction du mint depuis les logs
        for line in logs:
            if "Program log: Mint:" in line:
                mint = line.split("Mint:")[-1].strip()
                if mint not in self.seen and is_valid_solana_address(mint):
                    self.seen.add(mint)
                    await self.queue.put({
                        "mint":      mint,
                        "signature": signature,
                        "ts":        now_ts(),
                        "source":    "pumpfun_ws",
                    })
                    log.info(f"🔍 Discovery : {short_addr(mint)}")

    async def run(self):
        self.running = True
        while self.running:
            try:
                async with websockets.connect(
                    self.ws_url,
                    ping_interval=20,
                    ping_timeout=10,
                    max_size=2**22,
                ) as ws:
                    await self._subscribe(ws)
                    log.info("WebSocket discovery connecté")
                    while self.running:
                        try:
                            msg = await asyncio.wait_for(ws.recv(), timeout=45)
                            await self._process_log(json.loads(msg))
                        except asyncio.TimeoutError:
                            # Ping keepalive
                            try:
                                await ws.send(json.dumps({
                                    "jsonrpc": "2.0", "id": 99, "method": "ping"
                                }))
                            except Exception:
                                break
            except Exception as e:
                log.warning(f"WS reconnect dans {self.reconnect_delay}s : {e}")
                await asyncio.sleep(self.reconnect_delay)
                self.reconnect_delay = min(self.reconnect_delay * 1.5, 30.0)

    def stop(self):
        self.running = False


# ═══════════════════════════════════════════════════════════════════════════════
#  SECURITY GATE
# ═══════════════════════════════════════════════════════════════════════════════

class SecurityGate:
    """Filtre multi-couches pour éviter les scams/rugs."""

    def __init__(self, cfg: Config, rpc: SolanaRPC, birdeye: BirdeyeClient,
                 db: Database):
        self.cfg = cfg
        self.rpc = rpc
        self.birdeye = birdeye
        self.db = db

    def check(self, c: TokenCandidate) -> bool:
        """Retourne True si le token passe tous les filtres."""
        # 0. Blacklist
        if self.db.is_blacklisted(c.mint):
            c.status = TokenStatus.REJECTED
            c.rejected_reason = "blacklisted"
            return False

        # 1. Autorités du mint
        mint_info = self.rpc.get_mint_info(c.mint)
        if not mint_info:
            c.status = TokenStatus.REJECTED
            c.rejected_reason = "mint_info_unavailable"
            return False

        if self.cfg.get("security.require_mint_revoked", True):
            if mint_info.get("mint_authority"):
                c.status = TokenStatus.SECURITY_FAIL
                c.rejected_reason = "mint_authority_active"
                log.debug(f"❌ {short_addr(c.mint)} : mint authority active")
                return False

        if self.cfg.get("security.require_freeze_revoked", True):
            if mint_info.get("freeze_authority"):
                c.status = TokenStatus.SECURITY_FAIL
                c.rejected_reason = "freeze_authority_active"
                log.debug(f"❌ {short_addr(c.mint)} : freeze authority active")
                return False

        # 2. Birdeye security (si activé)
        sec_data = self.birdeye.token_security(c.mint)
        if sec_data:
            if sec_data.get("is_honeypot"):
                c.status = TokenStatus.SECURITY_FAIL
                c.rejected_reason = "honeypot"
                log.warning(f"🍯 {short_addr(c.mint)} : honeypot détecté")
                return False

            top10 = float(sec_data.get("top10HolderPercent", 0) or 0)
            max_top10 = self.cfg.get("security.max_top10_holder_pct", 30.0)
            if top10 > max_top10:
                c.status = TokenStatus.SECURITY_FAIL
                c.rejected_reason = f"top10_holders_{top10:.1f}%"
                log.debug(f"❌ {short_addr(c.mint)} : top10 {top10:.1f}%")
                return False

            c.security_data = sec_data
            c.top10_holder_pct = top10
            c.holder_count = int(sec_data.get("holderCount", 0) or 0)

        # 3. Liquidité minimum
        from dex import DexScreenerClient  # évite circularité
        c.status = TokenStatus.SECURITY_PASS
        return True


# ═══════════════════════════════════════════════════════════════════════════════
#  SCREENER
# ═══════════════════════════════════════════════════════════════════════════════

class Screener:
    """Score multi-facteurs pour classer les tokens."""

    def __init__(self, cfg: Config, dex: DexScreenerClient):
        self.cfg = cfg
        self.dex = dex
        self.weights = {
            "liquidity":      cfg.get("screening.weight_liquidity", 30),
            "timing":         cfg.get("screening.weight_timing", 15),
            "bonding":        cfg.get("screening.weight_bonding", 25),
            "age":            cfg.get("screening.weight_age", 20),
            "holder_growth":  cfg.get("screening.weight_holder_growth", 10),
        }

    def score(self, c: TokenCandidate) -> float:
        """Retourne un score 0-100 + détail par facteur."""
        breakdown = {}

        # 1. Liquidité (source : DexScreener)
        liq_usd = self.dex.get_liquidity_usd(c.mint)
        if liq_usd >= 50000:
            breakdown["liquidity"] = self.weights["liquidity"]
        elif liq_usd >= 20000:
            breakdown["liquidity"] = self.weights["liquidity"] * 0.8
        elif liq_usd >= 5000:
            breakdown["liquidity"] = self.weights["liquidity"] * 0.5
        elif liq_usd >= 2000:
            breakdown["liquidity"] = self.weights["liquidity"] * 0.25
        else:
            breakdown["liquidity"] = 0.0

        # 2. Timing (heures UTC actives)
        hour = now_utc().hour
        if hour in (6, 7, 8, 9, 10, 11):
            breakdown["timing"] = self.weights["timing"]
        elif hour in (14, 15, 16, 17, 18, 19):
            breakdown["timing"] = self.weights["timing"] * 0.7
        elif hour in (0, 1, 2, 3, 4, 5):
            breakdown["timing"] = 0.0
        else:
            breakdown["timing"] = self.weights["timing"] * 0.3

        # 3. Bonding curve progression
        bc = c.bonding_curve_pct
        if 70 <= bc < 88:
            breakdown["bonding"] = self.weights["bonding"]
        elif 50 <= bc < 70:
            breakdown["bonding"] = self.weights["bonding"] * 0.6
        elif bc >= 88:
            breakdown["bonding"] = self.weights["bonding"] * 0.4
        elif 20 <= bc < 50:
            breakdown["bonding"] = self.weights["bonding"] * 0.2
        else:
            breakdown["bonding"] = 0.0

        # 4. Âge du token
        age = now_ts() - c.created_at
        min_age = self.cfg.get("security.min_age_seconds", 15)
        max_age = self.cfg.get("security.max_age_seconds", 900)
        if age < min_age:
            breakdown["age"] = 0.0
        elif age < 60:
            breakdown["age"] = self.weights["age"]
        elif age < 300:
            breakdown["age"] = self.weights["age"] * 0.7
        elif age < max_age:
            breakdown["age"] = self.weights["age"] * 0.3
        else:
            breakdown["age"] = 0.0

        # 5. Growth des holders
        hc = c.holder_count
        if hc >= 200:
            breakdown["holder_growth"] = self.weights["holder_growth"]
        elif hc >= 100:
            breakdown["holder_growth"] = self.weights["holder_growth"] * 0.8
        elif hc >= 50:
            breakdown["holder_growth"] = self.weights["holder_growth"] * 0.5
        elif hc >= 20:
            breakdown["holder_growth"] = self.weights["holder_growth"] * 0.25
        else:
            breakdown["holder_growth"] = 0.0

        total = sum(breakdown.values())
        c.screening_score = total
        c.screening_breakdown = breakdown

        if total >= self.cfg.get("screening.min_score", 60):
            c.status = TokenStatus.SCREENED_IN
            log.info(f"📊 {short_addr(c.mint)} : score {total:.1f} ✅")
        else:
            c.status = TokenStatus.SCREENED_OUT
            log.debug(f"📊 {short_addr(c.mint)} : score {total:.1f} ❌")
        return total


# ═══════════════════════════════════════════════════════════════════════════════
#  INDICATORS
# ═══════════════════════════════════════════════════════════════════════════════

class Indicators:
    """Indicateurs techniques. Tous retournent des listes alignées."""

    @staticmethod
    def sma(values: List[float], period: int) -> List[Optional[float]]:
        out = [None] * len(values)
        if period <= 0 or len(values) < period:
            return out
        s = 0.0
        for i, v in enumerate(values):
            s += v
            if i >= period:
                s -= values[i - period]
            if i >= period - 1:
                out[i] = s / period
        return out

    @staticmethod
    def ema(values: List[float], period: int) -> List[Optional[float]]:
        out = [None] * len(values)
        if period <= 0 or len(values) < period:
            return out
        k = 2 / (period + 1)
        prev = sum(values[:period]) / period
        out[period - 1] = prev
        for i in range(period, len(values)):
            prev = values[i] * k + prev * (1 - k)
            out[i] = prev
        return out

    @staticmethod
    def rsi(values: List[float], period: int = 14) -> List[Optional[float]]:
        out = [None] * len(values)
        if len(values) <= period:
            return out
        gains = losses = 0.0
        for i in range(1, period + 1):
            d = values[i] - values[i - 1]
            if d >= 0:
                gains += d
            else:
                losses -= d
        avg_gain = gains / period
        avg_loss = losses / period
        out[period] = 100 - 100 / (1 + (avg_gain / avg_loss if avg_loss else float("inf")))
        for i in range(period + 1, len(values)):
            d = values[i] - values[i - 1]
            g = max(d, 0)
            l = max(-d, 0)
            avg_gain = (avg_gain * (period - 1) + g) / period
            avg_loss = (avg_loss * (period - 1) + l) / period
            out[i] = 100 - 100 / (1 + (avg_gain / avg_loss if avg_loss else float("inf")))
        return out

    @staticmethod
    def macd(values: List[float], fast: int = 12, slow: int = 26,
             signal: int = 9) -> Tuple[List[Optional[float]], List, List]:
        ef = Indicators.ema(values, fast)
        es = Indicators.ema(values, slow)
        line = [(f - s) if (f is not None and s is not None) else None
                for f, s in zip(ef, es)]
        valid = [v for v in line if v is not None]
        sig = [None] * len(values)
        if len(valid) >= signal:
            sv = Indicators.ema(valid, signal)
            off = len(values) - len(valid)
            for i, v in enumerate(sv):
                if v is not None:
                    sig[off + i] = v
        hist = [(m - s) if (m is not None and s is not None) else None
                for m, s in zip(line, sig)]
        return line, sig, hist

    @staticmethod
    def bollinger(values: List[float], period: int = 20, mult: float = 2.0):
        mid = Indicators.sma(values, period)
        up = [None] * len(values)
        lo = [None] * len(values)
        for i in range(period - 1, len(values)):
            window = values[i - period + 1:i + 1]
            sd = statistics.pstdev(window)
            if mid[i] is not None:
                up[i] = mid[i] + mult * sd
                lo[i] = mid[i] - mult * sd
        return lo, mid, up

    @staticmethod
    def atr(highs: List[float], lows: List[float], closes: List[float],
            period: int = 14) -> List[Optional[float]]:
        out = [None] * len(closes)
        if len(closes) < period + 1:
            return out
        trs = [0.0]
        for i in range(1, len(closes)):
            trs.append(max(
                highs[i] - lows[i],
                abs(highs[i] - closes[i - 1]),
                abs(lows[i] - closes[i - 1]),
            ))
        atr0 = sum(trs[1:period + 1]) / period
        out[period] = atr0
        prev = atr0
        for i in range(period + 1, len(closes)):
            prev = (prev * (period - 1) + trs[i]) / period
            out[i] = prev
        return out

    @staticmethod
    def obv(closes: List[float], volumes: List[float]) -> List[float]:
        out = [0.0] * len(closes)
        for i in range(1, len(closes)):
            if closes[i] > closes[i - 1]:
                out[i] = out[i - 1] + volumes[i]
            elif closes[i] < closes[i - 1]:
                out[i] = out[i - 1] - volumes[i]
            else:
                out[i] = out[i - 1]
        return out

    @staticmethod
    def vwap(highs: List[float], lows: List[float], closes: List[float],
             volumes: List[float]) -> List[Optional[float]]:
        out = [None] * len(closes)
        cum_pv = cum_v = 0.0
        for i in range(len(closes)):
            tp = (highs[i] + lows[i] + closes[i]) / 3
            cum_pv += tp * volumes[i]
            cum_v += volumes[i]
            if cum_v > 0:
                out[i] = cum_pv / cum_v
        return out

    @staticmethod
    def adx(highs, lows, closes, period=14):
        n = len(closes)
        out = [None] * n
        if n < period * 2:
            return out
        pdm = [0.0] * n
        mdm = [0.0] * n
        trs = [0.0] * n
        for i in range(1, n):
            up = highs[i] - highs[i - 1]
            dn = lows[i - 1] - lows[i]
            pdm[i] = up if (up > dn and up > 0) else 0
            mdm[i] = dn if (dn > up and dn > 0) else 0
            trs[i] = max(
                highs[i] - lows[i],
                abs(highs[i] - closes[i - 1]),
                abs(lows[i] - closes[i - 1]),
            )
        def wilder(vals):
            res = [0.0] * n
            s = sum(vals[1:period + 1])
            res[period] = s
            for i in range(period + 1, n):
                res[i] = res[i - 1] - res[i - 1] / period + vals[i]
            return res
        tr_s = wilder(trs)
        pdm_s = wilder(pdm)
        mdm_s = wilder(mdm)
        dx = [None] * n
        for i in range(period, n):
            if tr_s[i] == 0:
                continue
            pdi = 100 * pdm_s[i] / tr_s[i]
            mdi = 100 * mdm_s[i] / tr_s[i]
            if pdi + mdi == 0:
                continue
            dx[i] = 100 * abs(pdi - mdi) / (pdi + mdi)
        valid = [v for v in dx if v is not None]
        if len(valid) < period:
            return out
        adx_v = [None] * len(valid)
        start = sum(valid[:period]) / period
        adx_v[period - 1] = start
        for i in range(period, len(valid)):
            adx_v[i] = (adx_v[i - 1] * (period - 1) + valid[i]) / period
        off = n - len(valid)
        for i, v in enumerate(adx_v):
            if v is not None:
                out[off + i] = v
        return out


# ═══════════════════════════════════════════════════════════════════════════════
#  STRATEGY FRAMEWORK
# ═══════════════════════════════════════════════════════════════════════════════

class Strategy(ABC):
    name = "base"

    def __init__(self, params: Optional[Dict] = None):
        self.params = params or {}
        self.closes: List[float] = []
        self.highs: List[float] = []
        self.lows: List[float] = []
        self.volumes: List[float] = []

    def update(self, candle: Candle):
        self.closes.append(candle.close)
        self.highs.append(candle.high)
        self.lows.append(candle.low)
        self.volumes.append(candle.volume)
        max_len = int(self.params.get("max_history", 500))
        if len(self.closes) > max_len:
            self.closes.pop(0)
            self.highs.pop(0)
            self.lows.pop(0)
            self.volumes.pop(0)

    @abstractmethod
    def signal(self) -> Tuple[Signal, str]:
        ...

    @property
    def last_price(self) -> Optional[float]:
        return self.closes[-1] if self.closes else None


class RsiStrategy(Strategy):
    name = "rsi"
    def __init__(self, params=None):
        super().__init__(params)
        self.period = int(self.params.get("period", 14))
        self.os = float(self.params.get("oversold", 30))
        self.ob = float(self.params.get("overbought", 70))

    def signal(self):
        if len(self.closes) < self.period + 2:
            return Signal.NEUTRAL, "warmup"
        rsi = Indicators.rsi(self.closes, self.period)
        v = rsi[-1]
        if v is None:
            return Signal.NEUTRAL, "no rsi"
        if v < self.os - 5:
            return Signal.STRONG_BUY, f"RSI {v:.1f}"
        if v < self.os:
            return Signal.BUY, f"RSI {v:.1f}"
        if v > self.ob + 5:
            return Signal.STRONG_SELL, f"RSI {v:.1f}"
        if v > self.ob:
            return Signal.SELL, f"RSI {v:.1f}"
        return Signal.NEUTRAL, f"RSI {v:.1f}"


class MacdStrategy(Strategy):
    name = "macd"
    def signal(self):
        if len(self.closes) < 40:
            return Signal.NEUTRAL, "warmup"
        _, _, hist = Indicators.macd(self.closes)
        if len(hist) < 2 or hist[-1] is None or hist[-2] is None:
            return Signal.NEUTRAL, "no macd"
        h0, h1 = hist[-2], hist[-1]
        if h0 < 0 and h1 > 0:
            return Signal.BUY, "MACD cross up"
        if h0 > 0 and h1 < 0:
            return Signal.SELL, "MACD cross down"
        return Signal.NEUTRAL, "neutral"


class EmaCrossStrategy(Strategy):
    name = "ema_cross"
    def __init__(self, params=None):
        super().__init__(params)
        self.fast = int(self.params.get("fast", 9))
        self.slow = int(self.params.get("slow", 21))

    def signal(self):
        if len(self.closes) < self.slow + 2:
            return Signal.NEUTRAL, "warmup"
        f = Indicators.ema(self.closes, self.fast)
        s = Indicators.ema(self.closes, self.slow)
        if None in (f[-1], f[-2], s[-1], s[-2]):
            return Signal.NEUTRAL, "no ema"
        if f[-2] <= s[-2] and f[-1] > s[-1]:
            return Signal.STRONG_BUY, "EMA cross up"
        if f[-2] >= s[-2] and f[-1] < s[-1]:
            return Signal.STRONG_SELL, "EMA cross down"
        if f[-1] > s[-1]:
            return Signal.BUY, "uptrend"
        if f[-1] < s[-1]:
            return Signal.SELL, "downtrend"
        return Signal.NEUTRAL, "flat"


class BollingerStrategy(Strategy):
    name = "bollinger"
    def __init__(self, params=None):
        super().__init__(params)
        self.period = int(self.params.get("period", 20))
        self.mult = float(self.params.get("mult", 2.0))

    def signal(self):
        if len(self.closes) < self.period + 2:
            return Signal.NEUTRAL, "warmup"
        lo, _, up = Indicators.bollinger(self.closes, self.period, self.mult)
        if lo[-1] is None or up[-1] is None:
            return Signal.NEUTRAL, "no bands"
        p = self.closes[-1]
        if p < lo[-1]:
            return Signal.STRONG_BUY, "below lower band"
        if p > up[-1]:
            return Signal.STRONG_SELL, "above upper band"
        return Signal.NEUTRAL, "inside bands"


class MomentumStrategy(Strategy):
    name = "momentum"
    def __init__(self, params=None):
        super().__init__(params)
        self.lookback = int(self.params.get("lookback", 10))
        self.threshold = float(self.params.get("threshold_pct", 3.0))

    def signal(self):
        if len(self.closes) < self.lookback + 1:
            return Signal.NEUTRAL, "warmup"
        past, now = self.closes[-self.lookback - 1], self.closes[-1]
        if past == 0:
            return Signal.NEUTRAL, "zero"
        ch = (now - past) / past * 100
        if ch > self.threshold:
            return Signal.BUY, f"mom +{ch:.2f}%"
        if ch < -self.threshold:
            return Signal.SELL, f"mom {ch:.2f}%"
        return Signal.NEUTRAL, f"mom {ch:+.2f}%"


class BreakoutStrategy(Strategy):
    name = "breakout"
    def __init__(self, params=None):
        super().__init__(params)
        self.lookback = int(self.params.get("lookback", 20))

    def signal(self):
        if len(self.closes) < self.lookback + 2:
            return Signal.NEUTRAL, "warmup"
        wh = max(self.highs[-self.lookback - 1:-1])
        wl = min(self.lows[-self.lookback - 1:-1])
        p = self.closes[-1]
        if p > wh:
            return Signal.STRONG_BUY, f"break {wh:.6f}"
        if p < wl:
            return Signal.STRONG_SELL, f"break {wl:.6f}"
        return Signal.NEUTRAL, "range"


class CompositeStrategy(Strategy):
    name = "composite"
    def __init__(self, params=None):
        super().__init__(params)
        self.strats: List[Tuple[Strategy, float]] = []
        self.add(RsiStrategy(), 1.0)
        self.add(MacdStrategy(), 1.2)
        self.add(EmaCrossStrategy(), 1.0)
        self.add(MomentumStrategy(), 0.8)

    def add(self, s: Strategy, w: float):
        self.strats.append((s, w))

    def update(self, candle: Candle):
        super().update(candle)
        for s, _ in self.strats:
            s.update(candle)

    def signal(self):
        if not self.strats:
            return Signal.NEUTRAL, "no strats"
        total_w = sum(w for _, w in self.strats)
        acc = 0.0
        reasons = []
        for s, w in self.strats:
            sig, reason = s.signal()
            acc += sig.value * w
            reasons.append(f"{s.name}:{sig.name}")
        avg = acc / total_w
        if avg >= 1.2:
            return Signal.STRONG_BUY, "; ".join(reasons)
        if avg >= 0.4:
            return Signal.BUY, "; ".join(reasons)
        if avg <= -1.2:
            return Signal.STRONG_SELL, "; ".join(reasons)
        if avg <= -0.4:
            return Signal.SELL, "; ".join(reasons)
        return Signal.NEUTRAL, "; ".join(reasons)


STRATEGY_REGISTRY: Dict[str, type] = {
    "rsi": RsiStrategy,
    "macd": MacdStrategy,
    "ema_cross": EmaCrossStrategy,
    "bollinger": BollingerStrategy,
    "momentum": MomentumStrategy,
    "breakout": BreakoutStrategy,
    "composite": CompositeStrategy,
}


def build_strategy(name: str, params: Optional[Dict] = None) -> Strategy:
    cls = STRATEGY_REGISTRY.get(name.lower(), CompositeStrategy)
    return cls(params)


# ═══════════════════════════════════════════════════════════════════════════════
#  RISK MANAGER
# ═══════════════════════════════════════════════════════════════════════════════

class RiskManager:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.peak_equity = 0.0
        self.day_start_equity = 0.0
        self.day_start_ts = now_ts()
        self.last_trade_ts = 0.0
        self._lock = threading.RLock()

    def update_equity(self, equity: float):
        with self._lock:
            if equity > self.peak_equity:
                self.peak_equity = equity
            if now_ts() - self.day_start_ts >= 86400:
                self.day_start_ts = now_ts()
                self.day_start_equity = equity

    def max_dd_breached(self, equity: float) -> bool:
        with self._lock:
            if self.peak_equity <= 0:
                return False
            dd = (self.peak_equity - equity) / self.peak_equity * 100
            return dd >= float(self.cfg.get("risk.daily_loss_limit_pct", 20))

    def daily_loss_breached(self, equity: float) -> bool:
        with self._lock:
            if self.day_start_equity <= 0:
                return False
            loss = (self.day_start_equity - equity) / self.day_start_equity * 100
            return loss >= float(self.cfg.get("risk.daily_loss_limit_pct", 20))

    def cooldown_active(self) -> bool:
        with self._lock:
            cd = float(self.cfg.get("risk.cooldown_seconds", 5))
            return (time.time() - self.last_trade_ts) < cd

    def mark_trade(self):
        with self._lock:
            self.last_trade_ts = time.time()

    def position_size_sol(self, equity_sol: float) -> float:
        """Calcule la taille de position en SOL."""
        size = float(self.cfg.get("trading.buy_amount_sol", 0.05))
        max_pos = float(self.cfg.get("trading.max_position_sol", 0.10))
        return min(size, max_pos, equity_sol * 0.2)


# ═══════════════════════════════════════════════════════════════════════════════
#  POSITION MANAGER
# ═══════════════════════════════════════════════════════════════════════════════

class PositionManager:
    """Gère les sorties : SL, TP1/TP2, trailing, time-stop."""

    def __init__(self, cfg: Config, db: Database):
        self.cfg = cfg
        self.db = db
        self.positions: Dict[str, Position] = {}
        self._lock = threading.RLock()

    def add(self, p: Position):
        with self._lock:
            self.positions[p.mint] = p
            self.db.save_position(p)

    def get(self, mint: str) -> Optional[Position]:
        with self._lock:
            return self.positions.get(mint)

    def all(self) -> List[Position]:
        with self._lock:
            return list(self.positions.values())

    def count(self) -> int:
        with self._lock:
            return len(self.positions)

    def update(self, mint: str, price: float) -> Optional[ExitReason]:
        """Met à jour une position, retourne la raison de sortie si applicable."""
        with self._lock:
            p = self.positions.get(mint)
            if not p:
                return None

            if price > p.high_water:
                p.high_water = price
            if price < p.low_water:
                p.low_water = price

            pnl_pct = p.unrealized_pnl_pct(price)
            age = p.age_seconds()

            # Time-stop
            if age > int(self.cfg.get("risk.max_hold_seconds", 300)):
                return ExitReason.TIME_STOP

            # Stop-loss
            if pnl_pct <= -float(self.cfg.get("risk.stop_loss_pct", 25)):
                return ExitReason.STOP_LOSS

            # TP1
            if not p.tp1_hit and pnl_pct >= float(
                    self.cfg.get("risk.take_profit_1_pct", 50)):
                return ExitReason.TAKE_PROFIT_1

            # TP2
            if p.tp1_hit and pnl_pct >= float(
                    self.cfg.get("risk.take_profit_2_pct", 200)):
                return ExitReason.TAKE_PROFIT_2

            # Trailing stop après TP1
            if (p.tp1_hit and self.cfg.get("risk.use_trailing_stop", True)):
                trail = (p.high_water - price) / p.high_water * 100
                if trail >= float(self.cfg.get("risk.trailing_stop_pct", 15)):
                    return ExitReason.TRAILING_STOP

            return None

    def remove(self, mint: str):
        with self._lock:
            self.positions.pop(mint, None)
            self.db.close_position(mint)


# ═══════════════════════════════════════════════════════════════════════════════
#  EXECUTOR
# ═══════════════════════════════════════════════════════════════════════════════

class Executor:
    """Exécution (paper / live via Jupiter)."""

    def __init__(self, cfg: Config, jupiter: JupiterClient, mode: Mode):
        self.cfg = cfg
        self.jupiter = jupiter
        self.mode = mode
        self.fees_pct = 0.003
        self.slippage_pct = 0.001

    def _apply_slippage(self, price: float, side: Side) -> float:
        slip = price * self.slippage_pct
        return price + slip if side == Side.BUY else price - slip

    def buy(self, mint: str, sol_amount: float, current_price: float
            ) -> Tuple[bool, float, float, float, str]:
        """
        Retourne (success, exec_price, quantity, fee_sol, txid).
        """
        if current_price <= 0:
            return False, 0.0, 0.0, 0.0, "invalid_price"

        if self.mode == Mode.PAPER:
            exec_price = self._apply_slippage(current_price, Side.BUY)
            quantity = sol_amount / exec_price
            fee = sol_amount * self.fees_pct
            txid = f"paper_buy_{int(time.time()*1000)}"
            log.info(f"[PAPER BUY] {short_addr(mint)} : "
                     f"{sol_amount:.4f} SOL @ {exec_price:.10f} = {quantity:.2f} tokens")
            return True, exec_price, quantity, fee, txid

        # Mode live
        try:
            lamports = int(sol_amount * LAMPORTS_PER_SOL)
            slippage_bps = int(self.cfg.get("trading.slippage_bps", 500))
            quote = self.jupiter.get_quote(SOL_MINT, mint, lamports, slippage_bps)
            if not quote:
                return False, 0.0, 0.0, 0.0, "no_quote"

            out_amount = int(quote.get("outAmount", 0))
            if out_amount <= 0:
                return False, 0.0, 0.0, 0.0, "zero_out"

            price_impact = float(quote.get("priceImpactPct", 0))
            if price_impact > 5.0:
                return False, 0.0, 0.0, 0.0, f"high_impact_{price_impact:.2f}%"

            # Signer + envoyer la transaction (nécessite un wallet Solana)
            # Pour la sécurité, on ne va pas plus loin ici.
            log.warning("Mode live non activé : signature désactivée pour sécurité")
            return False, 0.0, 0.0, 0.0, "live_disabled"
        except Exception as e:
            log.error(f"Erreur live buy : {e}")
            return False, 0.0, 0.0, 0.0, str(e)

    def sell(self, mint: str, quantity: float, current_price: float
             ) -> Tuple[bool, float, float, float, str]:
        if current_price <= 0:
            return False, 0.0, 0.0, 0.0, "invalid_price"

        if self.mode == Mode.PAPER:
            exec_price = self._apply_slippage(current_price, Side.SELL)
            proceeds = exec_price * quantity
            fee = proceeds * self.fees_pct
            txid = f"paper_sell_{int(time.time()*1000)}"
            log.info(f"[PAPER SELL] {short_addr(mint)} : "
                     f"{quantity:.2f} tokens @ {exec_price:.10f} = {proceeds:.4f} SOL")
            return True, exec_price, quantity, fee, txid

        # Mode live
        try:
            raw = int(quantity * 10**DEFAULT_DECIMALS)
            slippage_bps = int(self.cfg.get("trading.slippage_bps", 500))
            quote = self.jupiter.get_quote(mint, SOL_MINT, raw, slippage_bps)
            if not quote:
                return False, 0.0, 0.0, 0.0, "no_quote"
            log.warning("Mode live non activé : signature désactivée")
            return False, 0.0, 0.0, 0.0, "live_disabled"
        except Exception as e:
            return False, 0.0, 0.0, 0.0, str(e)


# ═══════════════════════════════════════════════════════════════════════════════
#  NOTIFIER
# ═══════════════════════════════════════════════════════════════════════════════

class Notifier:
    def __init__(self, cfg: Config):
        self.discord = cfg.get("notifications.discord_webhook", "")
        self.tg_token = cfg.get("notifications.telegram_token", "")
        self.tg_chat = cfg.get("notifications.telegram_chat_id", "")
        self.session = requests.Session()

    def _send_discord(self, title: str, body: str, level: str):
        if not self.discord:
            return
        colors = {"info": 0x5DA9FF, "success": 0x14F195, "warning": 0xFFB020,
                  "error": 0xFF4D6D, "trade": 0x9945FF, "rug": 0xFF0000}
        try:
            self.session.post(self.discord, json={
                "username": "LAX Sniper",
                "embeds": [{
                    "title": title, "description": body,
                    "color": colors.get(level, 0x9945FF),
                    "timestamp": now_utc().isoformat(),
                    "footer": {"text": f"Laxironix Sniper v{VERSION}"},
                }],
            }, timeout=8)
        except Exception:
            pass

    def _send_telegram(self, title: str, body: str):
        if not self.tg_token or not self.tg_chat:
            return
        try:
            self.session.post(
                f"https://api.telegram.org/bot{self.tg_token}/sendMessage",
                json={"chat_id": self.tg_chat,
                      "text": f"*{title}*\n\n{body}",
                      "parse_mode": "Markdown"},
                timeout=8)
        except Exception:
            pass

    def send(self, title: str, body: str, level: str = "info"):
        self._send_discord(title, body, level)
        self._send_telegram(title, body)

    def buy(self, mint: str, symbol: str, sol: float, price: float, qty: float):
        self.send(f"🟢 BUY {symbol}",
                  f"Mint: `{short_addr(mint)}`\n"
                  f"SOL: {sol:.4f}\nPrice: {price:.10f}\nQty: {qty:.2f}",
                  "trade")

    def sell(self, mint: str, symbol: str, pnl: float, pnl_pct: float,
             reason: str):
        emoji = "🟢" if pnl >= 0 else "🔴"
        self.send(f"{emoji} SELL {symbol} ({reason})",
                  f"Mint: `{short_addr(mint)}`\n"
                  f"PnL: {pnl:+.4f} SOL ({pnl_pct:+.2f}%)",
                  "trade")

    def error(self, msg: str):
        self.send("⚠️ Erreur", f"```{msg}```", "error")

    def rug(self, mint: str, reason: str):
        self.send("🚨 RUG DÉTECTÉ", f"Mint: `{mint}`\nRaison: {reason}", "rug")


# ═══════════════════════════════════════════════════════════════════════════════
#  BACKTESTER
# ═══════════════════════════════════════════════════════════════════════════════

class Backtester:
    def __init__(self, strategy: Strategy, starting_sol: float = 1.0):
        self.strategy = strategy
        self.starting_sol = starting_sol
        self.trades: List[Trade] = []

    def run(self, candles: List[Candle], fee_pct: float = 0.003,
            slippage_pct: float = 0.001, sl_pct: float = 8.0,
            tp_pct: float = 20.0) -> Dict:
        cash = self.starting_sol
        qty = 0.0
        entry_price = 0.0
        entry_ts = 0
        peak = self.starting_sol
        max_dd = 0.0
        equity_curve = []

        for c in candles:
            self.strategy.update(c)
            price = c.close
            equity = cash + qty * price
            if equity > peak:
                peak = equity
            dd = (peak - equity) / peak * 100 if peak else 0
            if dd > max_dd:
                max_dd = dd
            equity_curve.append(equity)

            if qty > 0:
                # SL / TP
                if price <= entry_price * (1 - sl_pct / 100):
                    exec_price = price * (1 - slippage_pct)
                    proceeds = exec_price * qty
                    fee = proceeds * fee_pct
                    cash += proceeds - fee
                    pnl = (exec_price - entry_price) * qty - fee
                    self.trades.append(Trade(
                        mint="backtest", symbol="BT", side=Side.BUY,
                        entry_price=entry_price, exit_price=exec_price,
                        quantity=qty, entry_time=entry_ts, exit_time=c.timestamp,
                        pnl_sol=pnl, pnl_pct=(exec_price - entry_price) / entry_price * 100,
                        fees_sol=fee, reason=ExitReason.STOP_LOSS,
                    ))
                    qty = 0
                    continue
                if price >= entry_price * (1 + tp_pct / 100):
                    exec_price = price * (1 - slippage_pct)
                    proceeds = exec_price * qty
                    fee = proceeds * fee_pct
                    cash += proceeds - fee
                    pnl = (exec_price - entry_price) * qty - fee
                    self.trades.append(Trade(
                        mint="backtest", symbol="BT", side=Side.BUY,
                        entry_price=entry_price, exit_price=exec_price,
                        quantity=qty, entry_time=entry_ts, exit_time=c.timestamp,
                        pnl_sol=pnl, pnl_pct=(exec_price - entry_price) / entry_price * 100,
                        fees_sol=fee, reason=ExitReason.TAKE_PROFIT_1,
                    ))
                    qty = 0
                    continue

            if len(self.strategy.closes) < 30:
                continue
            sig, _ = self.strategy.signal()
            if sig in (Signal.BUY, Signal.STRONG_BUY) and qty == 0:
                exec_price = price * (1 + slippage_pct)
                budget = cash * 0.95
                qty = budget / exec_price
                cash -= qty * exec_price
                entry_price = exec_price
                entry_ts = c.timestamp
            elif sig in (Signal.SELL, Signal.STRONG_SELL) and qty > 0:
                exec_price = price * (1 - slippage_pct)
                proceeds = exec_price * qty
                fee = proceeds * fee_pct
                cash += proceeds - fee
                pnl = (exec_price - entry_price) * qty - fee
                self.trades.append(Trade(
                    mint="backtest", symbol="BT", side=Side.BUY,
                    entry_price=entry_price, exit_price=exec_price,
                    quantity=qty, entry_time=entry_ts, exit_time=c.timestamp,
                    pnl_sol=pnl, pnl_pct=(exec_price - entry_price) / entry_price * 100,
                    fees_sol=fee, reason=ExitReason.SIGNAL,
                ))
                qty = 0

        final_eq = cash + qty * (candles[-1].close if candles else 0)
        wins = [t for t in self.trades if t.pnl_sol > 0]
        losses = [t for t in self.trades if t.pnl_sol <= 0]
        gw = sum(t.pnl_sol for t in wins)
        gl = abs(sum(t.pnl_sol for t in losses))
        return {
            "starting": self.starting_sol,
            "ending": final_eq,
            "net_pnl": final_eq - self.starting_sol,
            "net_pnl_pct": (final_eq - self.starting_sol) / self.starting_sol * 100,
            "total_trades": len(self.trades),
            "wins": len(wins), "losses": len(losses),
            "win_rate": (len(wins) / len(self.trades) * 100) if self.trades else 0,
            "profit_factor": (gw / gl) if gl else 0,
            "max_drawdown_pct": max_dd,
            "peak_equity": peak,
        }


# ═══════════════════════════════════════════════════════════════════════════════
#  MAIN SNIPER
# ═══════════════════════════════════════════════════════════════════════════════

class LaxSniper:
    """Orchestrateur principal."""

    def __init__(self, cfg: Config, mode: Mode = Mode.PAPER):
        self.cfg = cfg
        self.mode = mode
        self.db = Database(Path(cfg.get("database.path", str(DB_FILE))))
        self.rpc = SolanaRPC(cfg)
        self.jupiter = JupiterClient(cfg)
        self.birdeye = BirdeyeClient(cfg)
        self.dex = DexScreenerClient()
        self.helius = HeliusClient(cfg)
        self.jito = JitoClient(cfg)
        self.security = SecurityGate(cfg, self.rpc, self.birdeye, self.db)
        self.screener = Screener(cfg, self.dex)
        self.risk = RiskManager(cfg)
        self.positions = PositionManager(cfg, self.db)
        self.executor = Executor(cfg, self.jupiter, mode)
        self.notifier = Notifier(cfg)
        self.discovery = WebSocketDiscovery(cfg)

        self.cash_sol = float(cfg.get("trading.buy_amount_sol", 0.05)) * 20  # pool initial
        self.running = False
        self.start_ts = now_ts()

    def _current_equity(self) -> float:
        equity = self.cash_sol
        for p in self.positions.all():
            price = self.jupiter.get_price(p.mint) or p.entry_price
            equity += p.quantity * price
        return equity

    async def _handle_candidate(self, data: Dict):
        mint = data["mint"]
        c = TokenCandidate(
            mint=mint,
            created_at=data.get("ts", now_ts()),
        )

        # Étape 2 : Security
        if not self.security.check(c):
            self.db.save_candidate(c)
            return

        # Enrichir avec métadonnées Jupiter
        meta = self.jupiter.get_token_metadata(mint)
        if meta:
            c.symbol = meta.get("symbol", "")
            c.name = meta.get("name", "")

        # Étape 3 : Screening
        self.screener.score(c)
        self.db.save_candidate(c)

        if c.status != TokenStatus.SCREENED_IN:
            return

        # Limite de positions concurrentes
        max_pos = int(self.cfg.get("trading.max_concurrent_positions", 3))
        if self.positions.count() >= max_pos:
            log.info(f"Limite de positions atteinte ({max_pos})")
            return

        # Étape 4 : Exécution
        sol_amount = self.risk.position_size_sol(self.cash_sol)
        if sol_amount <= 0 or sol_amount > self.cash_sol:
            return

        price = self.jupiter.get_price(mint)
        if price is None or price <= 0:
            price = self.dex.get_price_usd(mint)
            if price:
                # Convertir en prix SOL
                sol_price = self.jupiter.get_price(SOL_MINT) or 200.0
                price = price / sol_price
        if price is None or price <= 0:
            log.warning(f"Impossible d'obtenir le prix de {short_addr(mint)}")
            return

        success, exec_price, qty, fee, txid = self.executor.buy(mint, sol_amount, price)
        if not success:
            log.warning(f"Buy rejeté : {txid}")
            return

        self.cash_sol -= (sol_amount + fee)

        pos = Position(
            mint=mint,
            symbol=c.symbol or mint[:6],
            entry_price=exec_price,
            quantity=qty,
            entry_time=now_ts(),
            entry_sol=sol_amount,
            fees_sol=fee,
            entry_txid=txid,
        )
        self.positions.add(pos)
        self.risk.mark_trade()

        if self.cfg.get("notifications.notify_on_buy", True):
            self.notifier.buy(mint, pos.symbol, sol_amount, exec_price, qty)

    async def _monitor_positions(self):
        for p in self.positions.all():
            price = self.jupiter.get_price(p.mint)
            if price is None:
                price = self.dex.get_price_usd(p.mint)
                if price:
                    sol_price = self.jupiter.get_price(SOL_MINT) or 200.0
                    price = price / sol_price
            if price is None or price <= 0:
                continue

            reason = self.positions.update(p.mint, price)
            if reason is None:
                continue

            # Sortie
            if reason == ExitReason.TAKE_PROFIT_1 and not p.tp1_hit:
                # Vendre 50%
                sell_qty = p.quantity * float(self.cfg.get("risk.take_profit_1_size", 0.5))
                success, exec_price, _, fee, txid = self.executor.sell(p.mint, sell_qty, price)
                if success:
                    p.quantity -= sell_qty
                    p.tp1_hit = True
                    p.tp1_size = sell_qty
                    proceeds = exec_price * sell_qty - fee
                    p.realized_sol += proceeds
                    self.cash_sol += proceeds
                    self.positions.db.save_position(p)
                    pnl_pct = p.unrealized_pnl_pct(exec_price)
                    self.notifier.sell(p.mint, p.symbol, proceeds, pnl_pct, "tp1")
                continue

            # Sortie totale
            success, exec_price, _, fee, txid = self.executor.sell(p.mint, p.quantity, price)
            if not success:
                continue

            pnl_sol = (exec_price - p.entry_price) * p.quantity - fee + p.realized_sol
            pnl_pct = p.unrealized_pnl_pct(exec_price)
            trade = Trade(
                mint=p.mint, symbol=p.symbol, side=Side.BUY,
                entry_price=p.entry_price, exit_price=exec_price,
                quantity=p.quantity + p.tp1_size,
                entry_time=p.entry_time, exit_time=now_ts(),
                pnl_sol=pnl_sol, pnl_pct=pnl_pct,
                fees_sol=fee, reason=reason,
                entry_txid=p.entry_txid, exit_txid=txid,
            )
            self.db.save_trade(trade)
            self.positions.remove(p.mint)
            self.cash_sol += (exec_price * p.quantity - fee)
            self.risk.mark_trade()

            if self.cfg.get("notifications.notify_on_sell", True):
                self.notifier.sell(p.mint, p.symbol, pnl_sol, pnl_pct, reason.value)

    async def _discovery_worker(self):
        """Écoute la queue de discovery et traite les candidats."""
        while self.running:
            try:
                data = await asyncio.wait_for(self.discovery.queue.get(), timeout=1.0)
                asyncio.create_task(self._handle_candidate(data))
            except asyncio.TimeoutError:
                continue
            except Exception as e:
                log.error(f"Discovery worker : {e}")

    async def _position_worker(self):
        """Surveille les positions ouvertes."""
        interval = int(self.cfg.get("monitor.position_check_seconds", 3))
        while self.running:
            try:
                if self.positions.count() > 0:
                    await self._monitor_positions()
            except Exception as e:
                log.error(f"Position worker : {e}")
            await asyncio.sleep(interval)

    async def _equity_worker(self):
        """Enregistre la courbe d'équité."""
        while self.running:
            try:
                equity = self._current_equity()
                self.risk.update_equity(equity)
                positions_value = sum(
                    p.quantity * (self.jupiter.get_price(p.mint) or p.entry_price)
                    for p in self.positions.all()
                )
                self.db.save_equity(equity, self.cash_sol, positions_value)
            except Exception:
                pass
            await asyncio.sleep(30)

    async def run(self):
        self.running = True
        log.info("═" * 60)
        log.info(f"LAXIRONIX SNIPER v{VERSION} démarré (mode {self.mode.value})")
        log.info("═" * 60)

        self.notifier.send("🚀 Sniper démarré",
                           f"Mode : `{self.mode.value}`\n"
                           f"Capital initial : {self.cash_sol:.4f} SOL",
                           "success")

        await asyncio.gather(
            self.discovery.run(),
            self._discovery_worker(),
            self._position_worker(),
            self._equity_worker(),
        )

    def stop(self):
        self.running = False
        self.discovery.stop()


# ═══════════════════════════════════════════════════════════════════════════════
#  CLI
# ═══════════════════════════════════════════════════════════════════════════════

def banner():
    print(f"""
{C.BMAG}{C.BOLD}  ╔══════════════════════════════════════════════════════════════╗
  ║  LAXIRONIX SNIPER  v{VERSION}  {C.DIM}·  Solana Memecoin Bot{C.RESET}{C.BMAG}{C.BOLD}              ║
  ║  {C.DIM}Discovery · Security · Screening · Execution · Risk{C.RESET}{C.BMAG}{C.BOLD}            ║
  ╚══════════════════════════════════════════════════════════════╝{C.RESET}
""")


def cmd_run(args):
    banner()
    cfg = Config()
    mode = Mode(args.mode or cfg.get("mode", "paper"))
    bot = LaxSniper(cfg, mode=mode)
    try:
        asyncio.run(bot.run())
    except KeyboardInterrupt:
        log.info("Arrêt demandé")
        bot.stop()


def cmd_stats(args):
    banner()
    db = Database(Path(Config().get("database.path", str(DB_FILE))))
    s = db.stats()
    print(f"  {C.BCYA}{C.BOLD}▸ Performance{C.RESET}")
    print(f"  {'Trades':<20} {s['total']}")
    print(f"  {'Wins / Losses':<20} {C.BGRN}{s['wins']}{C.RESET} / {C.BRED}{s['losses']}{C.RESET}")
    print(f"  {'Win rate':<20} {s['win_rate']:.1f}%")
    color = C.BGRN if s['pnl'] >= 0 else C.BRED
    print(f"  {'PnL total':<20} {color}{s['pnl']:+.6f} SOL{C.RESET}")
    print(f"  {'Meilleur trade':<20} {C.BGRN}{s['best']:+.6f}{C.RESET}")
    print(f"  {'Pire trade':<20} {C.BRED}{s['worst']:+.6f}{C.RESET}")
    print(f"  {'Profit factor':<20} {s['profit_factor']:.2f}")


def cmd_backtest(args):
    banner()
    strategy = build_strategy(args.strategy or "composite")
    # Générer des bougies synthétiques pour la démo
    import random
    random.seed(args.seed or 42)
    candles = []
    price = 0.001
    for i in range(args.candles):
        ret = random.gauss(0.0002, 0.03)
        new_price = max(price * (1 + ret), 1e-9)
        candles.append(Candle(
            timestamp=now_ts() - (args.candles - i) * 60,
            open=price, high=max(price, new_price) * 1.01,
            low=min(price, new_price) * 0.99,
            close=new_price, volume=random.uniform(1e5, 1e6),
        ))
        price = new_price
    bt = Backtester(strategy, starting_sol=1.0)
    report = bt.run(candles)
    print(f"  {C.BCYA}{C.BOLD}▸ Backtest ({args.strategy}){C.RESET}")
    for k, v in report.items():
        if isinstance(v, float):
            print(f"  {k:<22} {v:>15.6f}")
        else:
            print(f"  {k:<22} {v:>15}")


def cmd_price(args):
    banner()
    jup = JupiterClient(Config())
    mints = {"SOL": SOL_MINT, "USDC": USDC_MINT}
    for sym, mint in mints.items():
        p = jup.get_price(mint)
        print(f"  {sym:<8} ${p:.4f}" if p else f"  {sym:<8} —")


def cmd_wallet(args):
    banner()
    if not is_valid_solana_address(args.address):
        print(f"  {C.BRED}✘{C.RESET} Adresse invalide")
        return
    rpc = SolanaRPC(Config())
    sol = rpc.get_sol_balance(args.address)
    print(f"  {C.BCYA}Wallet :{C.RESET} {args.address}")
    print(f"  {C.BCYA}SOL    :{C.RESET} {sol:.6f}")
    tokens = rpc.get_token_accounts(args.address)
    if tokens:
        print(f"  {C.BCYA}Tokens :{C.RESET}")
        for t in tokens[:10]:
            print(f"    {short_addr(t['mint'])} : {t['amount']:.4f}")


def cmd_config(args):
    banner()
    cfg = Config()
    if args.set:
        k, v = args.set
        try:
            v = json.loads(v)
        except Exception:
            pass
        cfg.set(k, v)
        print(f"  {C.BGRN}✔{C.RESET} {k} = {v!r}")
        return
    print(json.dumps(cfg.data, indent=2, ensure_ascii=False))


def build_parser():
    p = argparse.ArgumentParser(prog="lax_sniper",
                                description="Laxironix Sniper — Solana memecoin bot")
    p.add_argument("--version", action="version", version=f"%(prog)s {VERSION}")
    sub = p.add_subparsers(dest="cmd")

    sp = sub.add_parser("run", help="Lancer le bot")
    sp.add_argument("--mode", choices=["paper", "live", "copytrade"], default=None)
    sp.set_defaults(func=cmd_run)

    sp = sub.add_parser("stats", help="Statistiques")
    sp.set_defaults(func=cmd_stats)

    sp = sub.add_parser("backtest", help="Backtest")
    sp.add_argument("--strategy", default="composite")
    sp.add_argument("--candles", type=int, default=2000)
    sp.add_argument("--seed", type=int, default=42)
    sp.set_defaults(func=cmd_backtest)

    sp = sub.add_parser("price", help="Prix live")
    sp.set_defaults(func=cmd_price)

    sp = sub.add_parser("wallet", help="Inspecter un wallet")
    sp.add_argument("address")
    sp.set_defaults(func=cmd_wallet)

    sp = sub.add_parser("config", help="Config")
    sp.add_argument("--set", nargs=2, metavar=("KEY", "VALUE"))
    sp.set_defaults(func=cmd_config)

    return p


def main():
    parser = build_parser()
    if len(sys.argv) == 1:
        banner()
        parser.print_help()
        return 0
    args = parser.parse_args()
    if not hasattr(args, "func"):
        banner()
        parser.print_help()
        return 0
    return args.func(args) or 0


if __name__ == "__main__":
    sys.exit(main())
