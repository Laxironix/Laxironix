#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
================================================================================
 LAXIRONIX TRADING BOT
 Professional algorithmic trading system for Solana memecoins
================================================================================

A single-file, batteries-included trading system covering:

  - Solana JSON-RPC client (balances, token accounts, signatures, tx sim)
  - Lightweight WebSocket subscriber for account/log/slot updates
  - Market data aggregation (Jupiter / DexScreener) with local candle building
  - New-token scanner for freshly launched memecoins
  - Token security analysis (mint/freeze authority, LP status, concentration,
    creator history, honeypot-style heuristics) -> rug-pull risk scoring
  - Wallet / holder / whale behavioural analysis
  - Liquidity depth analysis and slippage estimation
  - A full technical indicator library (SMA, EMA, RSI, MACD, Bollinger, ATR,
    VWAP, Stochastic, ADX, OBV, CCI, Williams %R, realized volatility)
  - A strategy framework with 9 concrete strategies + a weighted composite
  - A signal engine that fuses security score + strategy signal + liquidity
    checks into a final BUY / SELL / HOLD / REJECT decision with a 0-100 score
  - A risk manager that can veto ANY signal (drawdown, daily loss, cooldown,
    circuit breaker, emergency stop, exposure limits, blacklist, sanity
    checks on price/amount/address)
  - Position sizing, portfolio accounting, SQLite persistence
  - Paper / simulation / backtest / live execution modes (paper is default;
    live requires multiple explicit confirmations and is never silently
    reachable)
  - A backtesting engine with PnL, drawdown, win rate, profit factor,
    expectancy, Sharpe and Sortino ratios, built to avoid look-ahead bias
  - Telegram / Discord notifications
  - A tiny dependency-free local HTTP status dashboard
  - A CLI covering run/paper/backtest/simulation/live/scan/status/performance
  - Built-in unit tests runnable with `python trading.py --test`

SAFETY
------
  * No private key is ever hardcoded. Keys are read from the environment
    (LAX_PRIVATE_KEY) and are never logged, printed, or persisted.
  * Default mode is PAPER. LIVE mode requires --i-understand-the-risk AND
    an environment confirmation variable AND a config flag, all three.
  * The RiskManager sits between every signal and the ExecutionEngine and
    can block a trade outright, regardless of what the strategy says.
  * This software does not guarantee profit. Memecoin trading is extremely
    high risk and you can lose all of your funds. Educational use only.

License: MIT
"""

from __future__ import annotations

import os
import re
import sys
import json
import time
import math
import uuid
import queue
import signal
import string
import random
import shutil
import sqlite3
import logging
import argparse
import textwrap
import threading
import statistics
import traceback
import unittest
import http.server
import socketserver
import urllib.request
import urllib.error
from abc import ABC, abstractmethod
from collections import deque, OrderedDict, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta, timezone
from enum import Enum, auto
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple, Union

try:
    import requests
    HAS_REQUESTS = True
except ImportError:
    HAS_REQUESTS = False
    print("\n  [ERROR] Missing dependency: requests")
    print("  Install: pip install requests\n")
    sys.exit(1)

try:
    import yaml
    HAS_YAML = True
except ImportError:
    HAS_YAML = False

try:
    import websocket  # websocket-client, optional
    HAS_WEBSOCKET = True
except ImportError:
    HAS_WEBSOCKET = False


# ================================================================================
#  VERSION / CONSTANTS
# ================================================================================

VERSION = "2.0.0"
APP_NAME = "Laxironix Trading Bot"

CONFIG_DIR = Path(os.environ.get("LAX_HOME", str(Path.home() / ".lax_trader")))
DB_FILE = CONFIG_DIR / "trades.db"
LOG_FILE = CONFIG_DIR / "lax_trader.log"
STATE_FILE = CONFIG_DIR / "state.json"
CONFIG_FILE = CONFIG_DIR / "config.yaml"
BLACKLIST_FILE = CONFIG_DIR / "blacklist.json"

LAMPORTS_PER_SOL = 1_000_000_000
SOL_DECIMALS = 9
TOKEN_PROGRAM_ID = "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"
TOKEN_2022_PROGRAM_ID = "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb"
SYSTEM_PROGRAM_ID = "11111111111111111111111111111111111111111"

# Public endpoints (override via config/env for private RPC)
DEFAULT_RPC_ENDPOINTS = [
    "https://api.mainnet-beta.solana.com",
]
DEFAULT_WS_ENDPOINT = "wss://api.mainnet-beta.solana.com"

JUPITER_PRICE_API = "https://price.jup.ag/v6/price"
JUPITER_QUOTE_API = "https://quote-api.jup.ag/v6/quote"
JUPITER_SWAP_API = "https://quote-api.jup.ag/v6/swap"
JUPITER_TOKEN_LIST_API = "https://token.jup.ag/all"
DEXSCREENER_TOKENS_API = "https://api.dexscreener.com/latest/dex/tokens"
DEXSCREENER_SEARCH_API = "https://api.dexscreener.com/latest/dex/search"
DEXSCREENER_PAIRS_API = "https://api.dexscreener.com/latest/dex/pairs/solana"

KNOWN_MINTS = {
    "SOL": "So11111111111111111111111111111111111111112",
    "USDC": "EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v",
    "USDT": "Es9vMFrzaCERmJfrF4H2FYD4KCoNkY11McCe8BenwNYB",
    "BONK": "DezXAZ8z7PnrnRJjz3wXBoRgixCa6xjnB7YaB1pPB263",
    "JUP": "JUPyiwrYJFskUPiHa7hkeR8VUtAeFoSYbKedZNsDvCN",
}

PROJECT = {
    "name": "Laxironix",
    "ticker": "$LAX",
    "chain": "Solana",
    "discord": "https://discord.gg/V3HnCfHm6",
    "x": "https://x.com/Laxironix",
    "github": "https://github.com/Laxironix",
}

LAX_MINT = os.environ.get("LAX_MINT", "")

BASE58_ALPHABET = set("123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz")


# ================================================================================
#  TERMINAL COLORS
# ================================================================================

class C:
    """ANSI color helper. Disabled automatically for non-tty / NO_COLOR."""
    _on = sys.stdout.isatty() and os.environ.get("NO_COLOR") is None
    RESET = "\033[0m" if _on else ""
    BOLD = "\033[1m" if _on else ""
    DIM = "\033[2m" if _on else ""
    RED = "\033[31m" if _on else ""
    GREEN = "\033[32m" if _on else ""
    YELLOW = "\033[33m" if _on else ""
    BLUE = "\033[34m" if _on else ""
    MAGENTA = "\033[35m" if _on else ""
    CYAN = "\033[36m" if _on else ""
    WHITE = "\033[37m" if _on else ""
    BRED = "\033[91m" if _on else ""
    BGREEN = "\033[92m" if _on else ""
    BYELLOW = "\033[93m" if _on else ""
    BCYAN = "\033[96m" if _on else ""
    BMAGENTA = "\033[95m" if _on else ""


# ================================================================================
#  CUSTOM EXCEPTIONS
# ================================================================================

class LaxError(Exception):
    """Base exception for all Laxironix errors."""


class ConfigError(LaxError):
    """Raised on invalid or missing configuration."""


class RpcError(LaxError):
    """Raised when a Solana RPC call fails after all retries."""


class RateLimitError(RpcError):
    """Raised when an upstream API rate-limits us."""


class MarketDataError(LaxError):
    """Raised when market data cannot be retrieved or is inconsistent."""


class SecurityCheckError(LaxError):
    """Raised when a token fails a mandatory security check."""


class RiskViolation(LaxError):
    """Raised when the RiskManager blocks an action. Never bypass this."""


class ExecutionError(LaxError):
    """Raised when an order cannot be executed."""


class InvalidAddressError(LaxError):
    """Raised when a Solana address fails validation."""


class InsufficientFundsError(LaxError):
    """Raised when the portfolio does not have enough cash/quantity."""


class LiveTradingNotConfirmedError(LaxError):
    """Raised when live mode is requested without the required confirmations."""


class BacktestDataError(LaxError):
    """Raised when backtest input data is invalid or insufficient."""


class DatabaseError(LaxError):
    """Raised on persistence-layer failures."""


# ================================================================================
#  ENUMS
# ================================================================================

class Mode(Enum):
    PAPER = "paper"
    SIMULATION = "simulation"
    BACKTEST = "backtest"
    LIVE = "live"


class Side(Enum):
    BUY = "buy"
    SELL = "sell"


class OrderType(Enum):
    MARKET = "market"
    LIMIT = "limit"


class OrderStatus(Enum):
    PENDING = "pending"
    FILLED = "filled"
    PARTIALLY_FILLED = "partially_filled"
    CANCELLED = "cancelled"
    REJECTED = "rejected"
    FAILED = "failed"


class TradeSignal(Enum):
    STRONG_BUY = "strong_buy"
    BUY = "buy"
    NEUTRAL = "neutral"
    SELL = "sell"
    STRONG_SELL = "strong_sell"


class Decision(Enum):
    """Final fused decision after security + strategy + risk fusion."""
    BUY = "buy"
    SELL = "sell"
    HOLD = "hold"
    REJECT = "reject"


class RiskLevel(Enum):
    VERY_LOW = "very_low"
    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"
    VERY_HIGH = "very_high"
    CRITICAL = "critical"


class CircuitState(Enum):
    CLOSED = "closed"       # normal operation
    OPEN = "open"           # trading halted
    HALF_OPEN = "half_open" # testing resumption


class ScanStatus(Enum):
    NEW = "new"
    WATCHING = "watching"
    QUALIFIED = "qualified"
    REJECTED = "rejected"
    EXPIRED = "expired"


# ================================================================================
#  DATACLASSES / DOMAIN MODELS
# ================================================================================

@dataclass
class Candle:
    timestamp: int
    open: float
    high: float
    low: float
    close: float
    volume: float = 0.0

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "Candle":
        return cls(**{k: d[k] for k in ("timestamp", "open", "high", "low", "close", "volume") if k in d})


@dataclass
class Order:
    side: Side
    quantity: float
    price: Optional[float] = None
    order_type: OrderType = OrderType.MARKET
    client_id: str = field(default_factory=lambda: uuid.uuid4().hex[:16])
    timestamp: int = field(default_factory=lambda: int(time.time()))
    max_slippage_bps: int = 100

    def to_dict(self) -> Dict[str, Any]:
        d = asdict(self)
        d["side"] = self.side.value
        d["order_type"] = self.order_type.value
        return d


@dataclass
class Fill:
    order_id: int
    side: Side
    quantity: float
    price: float
    fee: float
    timestamp: int
    txid: str = ""
    status: OrderStatus = OrderStatus.FILLED

    @property
    def value(self) -> float:
        return self.quantity * self.price


@dataclass
class Position:
    symbol: str
    mint: str
    quantity: float
    entry_price: float
    entry_time: int
    stop_loss: Optional[float] = None
    take_profit: Optional[float] = None
    trailing_high: Optional[float] = None
    trailing_stop: Optional[float] = None

    @property
    def cost_basis(self) -> float:
        return self.quantity * self.entry_price

    def unrealized_pnl(self, price: float) -> float:
        return (price - self.entry_price) * self.quantity

    def unrealized_pnl_pct(self, price: float) -> float:
        if self.entry_price == 0:
            return 0.0
        return (price - self.entry_price) / self.entry_price * 100.0

    def update_trailing(self, price: float, trail_pct: float) -> None:
        if self.trailing_high is None or price > self.trailing_high:
            self.trailing_high = price
            self.trailing_stop = price * (1 - trail_pct / 100.0)


@dataclass
class Trade:
    symbol: str
    mint: str
    side: Side
    entry_price: float
    exit_price: float
    quantity: float
    entry_time: int
    exit_time: int
    pnl: float
    pnl_pct: float
    fees: float
    reason: str = ""

    @property
    def duration_seconds(self) -> int:
        return self.exit_time - self.entry_time


@dataclass
class EquityPoint:
    timestamp: int
    equity: float
    cash: float
    position_value: float


@dataclass
class TokenHolder:
    address: str
    amount: float
    pct_of_supply: float
    is_contract: bool = False
    label: str = ""


@dataclass
class TokenInfo:
    mint: str
    symbol: str = ""
    name: str = ""
    decimals: int = 6
    supply: float = 0.0
    creator: str = ""
    created_at: int = 0
    mint_authority: Optional[str] = None
    freeze_authority: Optional[str] = None
    is_token_2022: bool = False
    lp_mint: str = ""
    lp_locked_pct: float = 0.0
    lp_burned_pct: float = 0.0
    price_usd: float = 0.0
    price_sol: float = 0.0
    market_cap_usd: float = 0.0
    liquidity_usd: float = 0.0
    volume_24h_usd: float = 0.0
    holder_count: int = 0
    top_holders: List[TokenHolder] = field(default_factory=list)
    pair_address: str = ""
    dex_id: str = ""


@dataclass
class SecurityFinding:
    code: str
    severity: RiskLevel
    message: str


@dataclass
class SecurityReport:
    mint: str
    findings: List[SecurityFinding] = field(default_factory=list)
    risk_score: float = 0.0          # 0 (safe) .. 100 (certain rug)
    risk_level: RiskLevel = RiskLevel.MEDIUM
    passed: bool = False
    checked_at: int = field(default_factory=lambda: int(time.time()))

    def add(self, code: str, severity: RiskLevel, message: str) -> None:
        self.findings.append(SecurityFinding(code, severity, message))

    def summary(self) -> str:
        return "; ".join(f"[{f.severity.value}] {f.message}" for f in self.findings) or "no findings"


@dataclass
class LiquidityReport:
    mint: str
    liquidity_usd: float
    depth_buy_1pct: float = 0.0     # USD tradable before 1% price impact (buy side)
    depth_sell_1pct: float = 0.0
    estimated_slippage_bps: Dict[float, float] = field(default_factory=dict)  # size_usd -> bps
    is_sufficient: bool = False


@dataclass
class WalletProfile:
    address: str
    sol_balance: float = 0.0
    token_accounts: int = 0
    tx_count_estimate: int = 0
    age_days: Optional[float] = None
    is_whale: bool = False
    is_suspicious: bool = False
    notes: List[str] = field(default_factory=list)


@dataclass
class ScanCandidate:
    token: TokenInfo
    status: ScanStatus = ScanStatus.NEW
    first_seen: int = field(default_factory=lambda: int(time.time()))
    last_updated: int = field(default_factory=lambda: int(time.time()))
    security: Optional[SecurityReport] = None
    liquidity: Optional[LiquidityReport] = None
    score: float = 0.0


@dataclass
class FusedSignal:
    mint: str
    decision: Decision
    score: float                     # 0..100 opportunity score
    strategy_signal: TradeSignal
    strategy_reason: str
    security_score: float
    liquidity_ok: bool
    reasons: List[str] = field(default_factory=list)
    timestamp: int = field(default_factory=lambda: int(time.time()))


@dataclass
class BacktestReport:
    starting_balance: float
    ending_balance: float
    net_pnl: float
    net_pnl_pct: float
    total_trades: int
    wins: int
    losses: int
    win_rate: float
    avg_win: float
    avg_loss: float
    profit_factor: float
    expectancy: float
    max_drawdown_pct: float
    peak_equity: float
    trough_equity: float
    sharpe: float
    sortino: float
    fees_paid: float
    slippage_cost: float

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


# ================================================================================
#  GENERIC UTILITIES
# ================================================================================

def utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def now_ts() -> int:
    return int(time.time())


def clamp(value: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, value))


def pct_change(a: float, b: float) -> float:
    """Percent change from a to b."""
    if a == 0:
        return 0.0
    return (b - a) / a * 100.0


def safe_div(a: float, b: float, default: float = 0.0) -> float:
    return a / b if b else default


def fmt_usd(v: float) -> str:
    if v >= 1_000_000:
        return f"${v/1_000_000:.2f}M"
    if v >= 1_000:
        return f"${v/1_000:.2f}K"
    return f"${v:.4f}"


def fmt_pct(v: float) -> str:
    return f"{v:+.2f}%"


def is_valid_solana_address(addr: Optional[str]) -> bool:
    """Best-effort base58 validation (length + alphabet). Not a full curve check."""
    if not addr or not isinstance(addr, str):
        return False
    if not (32 <= len(addr) <= 44):
        return False
    return all(ch in BASE58_ALPHABET for ch in addr)


def truncate_addr(addr: str, n: int = 4) -> str:
    if not addr or len(addr) <= 2 * n + 3:
        return addr
    return f"{addr[:n]}...{addr[-n:]}"


def mask_secret(secret: Optional[str]) -> str:
    """Never expose a secret in logs; used defensively even for non-key strings."""
    if not secret:
        return "<empty>"
    return f"<redacted:{len(secret)} chars>"


def retry(times: int = 3, delay: float = 1.0, backoff: float = 2.0,
          exceptions: Tuple[type, ...] = (Exception,),
          logger: Optional[logging.Logger] = None) -> Callable:
    """Decorator: retry a function with exponential backoff."""
    def decorator(fn: Callable) -> Callable:
        def wrapper(*args, **kwargs):
            _delay = delay
            last_exc: Optional[Exception] = None
            for attempt in range(1, times + 1):
                try:
                    return fn(*args, **kwargs)
                except exceptions as e:  # noqa: BLE001
                    last_exc = e
                    if logger:
                        logger.debug(f"{fn.__name__} attempt {attempt}/{times} failed: {e}")
                    if attempt < times:
                        time.sleep(_delay)
                        _delay *= backoff
            assert last_exc is not None
            raise last_exc
        wrapper.__name__ = fn.__name__
        return wrapper
    return decorator


class TokenBucketRateLimiter:
    """Simple thread-safe token-bucket rate limiter for outbound API calls."""

    def __init__(self, rate_per_sec: float, burst: int = 5):
        self.rate = rate_per_sec
        self.capacity = burst
        self.tokens = float(burst)
        self.last = time.monotonic()
        self.lock = threading.Lock()

    def acquire(self, block: bool = True) -> bool:
        with self.lock:
            now = time.monotonic()
            elapsed = now - self.last
            self.last = now
            self.tokens = min(self.capacity, self.tokens + elapsed * self.rate)
            if self.tokens >= 1.0:
                self.tokens -= 1.0
                return True
            if not block:
                return False
            wait = (1.0 - self.tokens) / self.rate
        time.sleep(max(wait, 0.0))
        with self.lock:
            self.tokens = max(0.0, self.tokens - 1.0)
        return True


class LRUCache:
    """Minimal thread-safe LRU cache with TTL, used for RPC/market data caching."""

    def __init__(self, maxsize: int = 512, ttl: float = 5.0):
        self.maxsize = maxsize
        self.ttl = ttl
        self._data: "OrderedDict[str, Tuple[Any, float]]" = OrderedDict()
        self._lock = threading.Lock()

    def get(self, key: str) -> Optional[Any]:
        with self._lock:
            item = self._data.get(key)
            if item is None:
                return None
            value, ts = item
            if (time.time() - ts) > self.ttl:
                del self._data[key]
                return None
            self._data.move_to_end(key)
            return value

    def set(self, key: str, value: Any) -> None:
        with self._lock:
            self._data[key] = (value, time.time())
            self._data.move_to_end(key)
            while len(self._data) > self.maxsize:
                self._data.popitem(last=False)

    def clear(self) -> None:
        with self._lock:
            self._data.clear()


class CircuitBreaker:
    """Generic circuit breaker: opens after N consecutive failures, half-opens after cooldown."""

    def __init__(self, failure_threshold: int = 5, cooldown_seconds: float = 60.0):
        self.failure_threshold = failure_threshold
        self.cooldown_seconds = cooldown_seconds
        self.state = CircuitState.CLOSED
        self.failures = 0
        self.opened_at: Optional[float] = None
        self.lock = threading.Lock()

    def allow(self) -> bool:
        with self.lock:
            if self.state == CircuitState.OPEN:
                if self.opened_at and (time.time() - self.opened_at) >= self.cooldown_seconds:
                    self.state = CircuitState.HALF_OPEN
                    return True
                return False
            return True

    def record_success(self) -> None:
        with self.lock:
            self.failures = 0
            self.state = CircuitState.CLOSED
            self.opened_at = None

    def record_failure(self) -> None:
        with self.lock:
            self.failures += 1
            if self.failures >= self.failure_threshold:
                self.state = CircuitState.OPEN
                self.opened_at = time.time()

    def force_open(self) -> None:
        with self.lock:
            self.state = CircuitState.OPEN
            self.opened_at = time.time()

    def force_close(self) -> None:
        with self.lock:
            self.state = CircuitState.CLOSED
            self.failures = 0
            self.opened_at = None


# ================================================================================
#  CONFIGURATION
# ================================================================================

DEFAULT_CONFIG: Dict[str, Any] = {
    "version": VERSION,
    "mode": "paper",                      # paper | simulation | backtest | live
    "network": "mainnet",

    "wallet": {
        "public_key": "",
        "private_key_env": "LAX_PRIVATE_KEY",
    },

    "rpc": {
        "endpoints": list(DEFAULT_RPC_ENDPOINTS),
        "ws_endpoint": DEFAULT_WS_ENDPOINT,
        "timeout_seconds": 15,
        "max_retries": 3,
        "rate_limit_per_sec": 8,
    },

    "trading": {
        "quote_mint": KNOWN_MINTS["SOL"],
        "starting_balance_quote": 1.0,
        "max_position_quote": 0.20,
        "position_size_pct": 0.08,
        "min_order_quote": 0.01,
        "max_concurrent_positions": 3,
        "slippage_bps": 150,
        "max_allowed_slippage_bps": 500,
        "priority_fee_lamports": 20000,
    },

    "scanner": {
        "enabled": True,
        "poll_interval_seconds": 15,
        "min_liquidity_usd": 3000.0,
        "min_age_seconds": 60,
        "max_age_seconds": 86400 * 3,
        "min_volume_24h_usd": 2000.0,
        "watchlist_size": 50,
    },

    "security": {
        "max_top10_holder_pct": 45.0,
        "reject_if_mint_authority_active": True,
        "reject_if_freeze_authority_active": True,
        "min_lp_locked_or_burned_pct": 80.0,
        "min_holder_count": 30,
        "max_creator_supply_pct": 15.0,
        "min_security_score_to_trade": 60.0,
    },

    "strategy": {
        "name": "composite",
        "params": {},
    },

    "risk": {
        "max_drawdown_pct": 20.0,
        "stop_loss_pct": 12.0,
        "take_profit_pct": 35.0,
        "trailing_stop_pct": 10.0,
        "use_trailing_stop": True,
        "max_open_positions": 3,
        "daily_loss_limit_pct": 15.0,
        "cooldown_seconds": 45,
        "circuit_breaker_failures": 5,
        "circuit_breaker_cooldown_seconds": 120,
        "max_trade_pct_of_equity": 0.20,
        "emergency_stop": False,
    },

    "monitor": {
        "interval_seconds": 15,
        "price_source": "jupiter",
        "history_points": 300,
    },

    "notifications": {
        "discord_webhook": "",
        "telegram_bot_token": "",
        "telegram_chat_id": "",
        "notify_on_trade": True,
        "notify_on_signal": False,
        "notify_on_error": True,
        "notify_on_scan_hit": True,
    },

    "dashboard": {
        "enabled": False,
        "host": "127.0.0.1",
        "port": 8787,
    },

    "database": {
        "path": str(DB_FILE),
    },

    "logging": {
        "level": "INFO",
        "file": str(LOG_FILE),
        "json": False,
    },

    "live_confirmation": {
        # ALL of these must be true/matching for live mode to run.
        "config_flag_enabled": False,
        "required_env_var": "LAX_LIVE_CONFIRM",
        "required_env_value": "I_UNDERSTAND_THE_RISK",
    },
}


class Config:
    """YAML/JSON configuration loader with dot-path access and deep merge.

    Secrets (private keys) are NEVER stored here — only environment variable
    *names* are stored, e.g. wallet.private_key_env = "LAX_PRIVATE_KEY".
    """

    def __init__(self, path: Path = CONFIG_FILE, overrides: Optional[Dict[str, Any]] = None):
        self.path = path
        self.data: Dict[str, Any] = {}
        self.load()
        if overrides:
            for k, v in overrides.items():
                self.set(k, v, persist=False)

    def load(self) -> None:
        CONFIG_DIR.mkdir(parents=True, exist_ok=True)
        if self.path.exists():
            try:
                with open(self.path, "r", encoding="utf-8") as f:
                    if self.path.suffix in (".yaml", ".yml") and HAS_YAML:
                        raw = yaml.safe_load(f) or {}
                    else:
                        raw = json.load(f)
                self.data = self._merge(json.loads(json.dumps(DEFAULT_CONFIG)), raw)
            except Exception as e:
                logging.getLogger("lax.config").warning(f"Failed to load config ({e}); using defaults")
                self.data = json.loads(json.dumps(DEFAULT_CONFIG))
        else:
            self.data = json.loads(json.dumps(DEFAULT_CONFIG))
            self.save()

    @staticmethod
    def _merge(base: Dict, over: Dict) -> Dict:
        out = dict(base)
        for k, v in (over or {}).items():
            if k in out and isinstance(out[k], dict) and isinstance(v, dict):
                out[k] = Config._merge(out[k], v)
            else:
                out[k] = v
        return out

    def save(self) -> None:
        try:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            with open(self.path, "w", encoding="utf-8") as f:
                if self.path.suffix in (".yaml", ".yml") and HAS_YAML:
                    yaml.safe_dump(self.data, f, sort_keys=False, allow_unicode=True)
                else:
                    json.dump(self.data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            logging.getLogger("lax.config").error(f"Failed to save config: {e}")

    def get(self, path: str, default: Any = None) -> Any:
        cur: Any = self.data
        for part in path.split("."):
            if isinstance(cur, dict) and part in cur:
                cur = cur[part]
            else:
                return default
        return cur

    def set(self, path: str, value: Any, persist: bool = True) -> None:
        parts = path.split(".")
        cur = self.data
        for part in parts[:-1]:
            if part not in cur or not isinstance(cur[part], dict):
                cur[part] = {}
            cur = cur[part]
        cur[parts[-1]] = value
        if persist:
            self.save()

    def validate(self) -> List[str]:
        """Return a list of human-readable configuration problems (empty if OK)."""
        problems: List[str] = []
        if self.get("trading.position_size_pct", 0) <= 0:
            problems.append("trading.position_size_pct must be > 0")
        if self.get("trading.max_position_quote", 0) <= 0:
            problems.append("trading.max_position_quote must be > 0")
        if self.get("risk.stop_loss_pct", 0) <= 0:
            problems.append("risk.stop_loss_pct must be > 0")
        if self.get("risk.max_drawdown_pct", 0) <= 0:
            problems.append("risk.max_drawdown_pct must be > 0")
        mode = self.get("mode", "paper")
        if mode not in [m.value for m in Mode]:
            problems.append(f"unknown mode '{mode}'")
        return problems

    def get_private_key(self) -> Optional[str]:
        """Read the private key from the configured environment variable.

        This is the ONLY place a private key may be read. It is never
        logged, never written to config, and never returned in any status
        payload. Callers must treat the return value as sensitive.
        """
        env_name = self.get("wallet.private_key_env", "LAX_PRIVATE_KEY")
        return os.environ.get(env_name)


# ================================================================================
#  STRUCTURED LOGGING
# ================================================================================

class JsonFormatter(logging.Formatter):
    """Renders log records as single-line JSON for machine ingestion."""

    def format(self, record: logging.LogRecord) -> str:
        payload = {
            "ts": datetime.fromtimestamp(record.created, tz=timezone.utc).isoformat(),
            "level": record.levelname,
            "logger": record.name,
            "message": record.getMessage(),
        }
        if record.exc_info:
            payload["exc_info"] = self.formatException(record.exc_info)
        return json.dumps(payload, ensure_ascii=False)


_SECRET_PATTERN = re.compile(r"(?i)(private[_ ]?key|secret|seed)\s*[:=]\s*\S+")


class RedactingFilter(logging.Filter):
    """Defense-in-depth: scrubs anything that looks like a secret before it is logged."""

    def filter(self, record: logging.LogRecord) -> bool:
        try:
            msg = record.getMessage()
        except Exception:
            return True
        if _SECRET_PATTERN.search(msg):
            record.msg = _SECRET_PATTERN.sub(r"\1: <redacted>", msg)
            record.args = ()
        return True


def setup_logging(cfg: Config) -> logging.Logger:
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    level_name = str(cfg.get("logging.level", "INFO")).upper()
    level = getattr(logging, level_name, logging.INFO)
    log_path = Path(cfg.get("logging.file", str(LOG_FILE)))
    use_json = bool(cfg.get("logging.json", False))

    root = logging.getLogger("lax")
    root.setLevel(level)
    root.handlers.clear()

    file_handler = logging.FileHandler(log_path, encoding="utf-8")
    stream_handler = logging.StreamHandler(sys.stdout)

    if use_json:
        fmt = JsonFormatter()
    else:
        fmt = logging.Formatter(
            fmt="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
            datefmt="%H:%M:%S",
        )
    file_handler.setFormatter(fmt)
    stream_handler.setFormatter(fmt)

    redactor = RedactingFilter()
    file_handler.addFilter(redactor)
    stream_handler.addFilter(redactor)

    root.addHandler(file_handler)
    root.addHandler(stream_handler)
    root.propagate = False
    return root


log = logging.getLogger("lax")


# ================================================================================
#  SOLANA RPC CLIENT
# ================================================================================

class SolanaClient:
    """JSON-RPC client for Solana with retries, rate limiting, endpoint failover,
    and a circuit breaker so a flaky RPC cannot spin the bot into a hot loop.
    """

    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.endpoints: List[str] = list(cfg.get("rpc.endpoints", DEFAULT_RPC_ENDPOINTS))
        if not self.endpoints:
            self.endpoints = list(DEFAULT_RPC_ENDPOINTS)
        self.timeout = float(cfg.get("rpc.timeout_seconds", 15))
        self.max_retries = int(cfg.get("rpc.max_retries", 3))
        self.session = requests.Session()
        self.session.headers.update({"Content-Type": "application/json",
                                      "User-Agent": f"LaxTrader/{VERSION}"})
        self.limiter = TokenBucketRateLimiter(
            rate_per_sec=float(cfg.get("rpc.rate_limit_per_sec", 8)), burst=10)
        self.breaker = CircuitBreaker(failure_threshold=6, cooldown_seconds=30)
        self._endpoint_idx = 0
        self._lock = threading.Lock()
        self.logger = logging.getLogger("lax.rpc")

    def _current_endpoint(self) -> str:
        with self._lock:
            return self.endpoints[self._endpoint_idx % len(self.endpoints)]

    def _rotate_endpoint(self) -> None:
        with self._lock:
            self._endpoint_idx = (self._endpoint_idx + 1) % len(self.endpoints)

    def call(self, method: str, params: Optional[List[Any]] = None) -> Any:
        """Perform a JSON-RPC call, returning the `result` field.

        Raises RpcError if all endpoints/retries are exhausted, or if the
        circuit breaker is open.
        """
        if not self.breaker.allow():
            raise RpcError(f"circuit breaker open, refusing RPC call '{method}'")

        payload = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params or []}
        last_err: Optional[Exception] = None

        for attempt in range(self.max_retries * len(self.endpoints)):
            endpoint = self._current_endpoint()
            self.limiter.acquire()
            try:
                resp = self.session.post(endpoint, json=payload, timeout=self.timeout)
                if resp.status_code == 429:
                    raise RateLimitError(f"rate limited by {endpoint}")
                resp.raise_for_status()
                data = resp.json()
                if "error" in data:
                    raise RpcError(f"{method} -> {data['error']}")
                self.breaker.record_success()
                return data.get("result")
            except (requests.RequestException, RpcError) as e:
                last_err = e
                self.breaker.record_failure()
                self.logger.debug(f"RPC {method} failed on {endpoint}: {e}")
                self._rotate_endpoint()
                time.sleep(min(0.5 * (attempt + 1), 4.0))

        raise RpcError(f"RPC method '{method}' failed after retries: {last_err}")

    # ─── Convenience wrappers ───────────────────────────────────────────────

    def get_balance_lamports(self, address: str) -> int:
        if not is_valid_solana_address(address):
            raise InvalidAddressError(f"invalid address: {address}")
        result = self.call("getBalance", [address, {"commitment": "confirmed"}])
        return int(result["value"]) if isinstance(result, dict) else int(result or 0)

    def get_sol_balance(self, address: str) -> float:
        return self.get_balance_lamports(address) / LAMPORTS_PER_SOL

    def get_account_info(self, address: str, encoding: str = "jsonParsed") -> Optional[Dict[str, Any]]:
        if not is_valid_solana_address(address):
            raise InvalidAddressError(f"invalid address: {address}")
        result = self.call("getAccountInfo", [address, {"encoding": encoding, "commitment": "confirmed"}])
        if not result:
            return None
        return result.get("value")

    def get_token_supply(self, mint: str) -> Optional[Dict[str, Any]]:
        result = self.call("getTokenSupply", [mint, {"commitment": "confirmed"}])
        return result.get("value") if result else None

    def get_token_accounts_by_owner(self, owner: str, program_id: str = TOKEN_PROGRAM_ID) -> List[Dict[str, Any]]:
        if not is_valid_solana_address(owner):
            raise InvalidAddressError(f"invalid address: {owner}")
        result = self.call("getTokenAccountsByOwner", [
            owner,
            {"programId": program_id},
            {"encoding": "jsonParsed", "commitment": "confirmed"},
        ])
        out: List[Dict[str, Any]] = []
        for acc in (result or {}).get("value", []):
            try:
                parsed = acc["account"]["data"]["parsed"]["info"]
                out.append({
                    "pubkey": acc.get("pubkey"),
                    "mint": parsed["mint"],
                    "amount": float(parsed["tokenAmount"]["uiAmount"] or 0),
                    "decimals": int(parsed["tokenAmount"]["decimals"]),
                })
            except Exception:
                continue
        return out

    def get_token_largest_accounts(self, mint: str) -> List[Dict[str, Any]]:
        result = self.call("getTokenLargestAccounts", [mint, {"commitment": "confirmed"}])
        out = []
        for a in (result or {}).get("value", []):
            out.append({
                "address": a.get("address"),
                "amount": float(a.get("uiAmount") or 0),
            })
        return out

    def get_signatures_for_address(self, address: str, limit: int = 50) -> List[Dict[str, Any]]:
        if not is_valid_solana_address(address):
            raise InvalidAddressError(f"invalid address: {address}")
        result = self.call("getSignaturesForAddress", [address, {"limit": limit}])
        return result or []

    def get_slot(self) -> int:
        return int(self.call("getSlot"))

    def get_health(self) -> str:
        try:
            return str(self.call("getHealth"))
        except RpcError:
            return "unhealthy"

    def simulate_transaction(self, tx_base64: str) -> Dict[str, Any]:
        """Simulate a base64-encoded transaction (never signs or sends)."""
        result = self.call("simulateTransaction", [tx_base64, {"encoding": "base64"}])
        return result or {}

    def send_raw_transaction(self, tx_base64: str, skip_preflight: bool = False) -> str:
        """Broadcast a signed transaction. Only ever called from LiveExecutor,
        and only ever after RiskManager approval. Returns the tx signature.
        """
        result = self.call("sendTransaction", [tx_base64, {
            "encoding": "base64",
            "skipPreflight": skip_preflight,
            "maxRetries": 3,
        }])
        return str(result)

    def confirm_transaction(self, signature: str, timeout_s: float = 45.0,
                            poll_interval: float = 2.0) -> bool:
        """Poll getSignatureStatuses until confirmed/finalized or timeout."""
        deadline = time.time() + timeout_s
        while time.time() < deadline:
            try:
                result = self.call("getSignatureStatuses", [[signature], {"searchTransactionHistory": True}])
                statuses = (result or {}).get("value", [None])
                st = statuses[0]
                if st is not None:
                    if st.get("err"):
                        return False
                    conf = st.get("confirmationStatus")
                    if conf in ("confirmed", "finalized"):
                        return True
            except RpcError as e:
                self.logger.debug(f"confirm poll failed: {e}")
            time.sleep(poll_interval)
        return False


# ================================================================================
#  WEBSOCKET SUBSCRIBER (best-effort; optional dependency)
# ================================================================================

class SolanaWebSocketClient:
    """Lightweight subscriber for account/logs/slot notifications.

    Runs in a background thread. If the optional `websocket-client` package
    is not installed, this degrades gracefully to a no-op and callers should
    fall back to polling via SolanaClient.
    """

    def __init__(self, cfg: Config, on_message: Optional[Callable[[Dict[str, Any]], None]] = None):
        self.cfg = cfg
        self.url = cfg.get("rpc.ws_endpoint", DEFAULT_WS_ENDPOINT)
        self.on_message = on_message or (lambda msg: None)
        self._ws = None
        self._thread: Optional[threading.Thread] = None
        self._running = False
        self._subscriptions: Dict[int, Dict[str, Any]] = {}
        self._next_id = 1
        self._lock = threading.Lock()
        self.logger = logging.getLogger("lax.ws")
        self.connected = False

    @property
    def available(self) -> bool:
        return HAS_WEBSOCKET

    def start(self) -> None:
        if not HAS_WEBSOCKET:
            self.logger.warning("websocket-client not installed; falling back to polling only")
            return
        if self._running:
            return
        self._running = True
        self._thread = threading.Thread(target=self._run_forever, daemon=True)
        self._thread.start()

    def stop(self) -> None:
        self._running = False
        try:
            if self._ws:
                self._ws.close()
        except Exception:
            pass

    def _run_forever(self) -> None:
        backoff = 1.0
        while self._running:
            try:
                self._connect_and_listen()
                backoff = 1.0
            except Exception as e:
                self.logger.debug(f"ws loop error: {e}")
            self.connected = False
            if self._running:
                time.sleep(min(backoff, 30.0))
                backoff *= 1.7

    def _connect_and_listen(self) -> None:
        assert HAS_WEBSOCKET
        ws = websocket.create_connection(self.url, timeout=20)
        self._ws = ws
        self.connected = True
        self.logger.info(f"WebSocket connected: {self.url}")
        with self._lock:
            for sub in self._subscriptions.values():
                ws.send(json.dumps(sub))
        while self._running:
            try:
                raw = ws.recv()
            except Exception:
                break
            if not raw:
                continue
            try:
                msg = json.loads(raw)
            except json.JSONDecodeError:
                continue
            self.on_message(msg)
        try:
            ws.close()
        except Exception:
            pass

    def subscribe_logs(self, mentions: Optional[List[str]] = None, commitment: str = "confirmed") -> int:
        with self._lock:
            sub_id = self._next_id
            self._next_id += 1
            filt = {"mentions": mentions} if mentions else "all"
            req = {
                "jsonrpc": "2.0", "id": sub_id, "method": "logsSubscribe",
                "params": [filt, {"commitment": commitment}],
            }
            self._subscriptions[sub_id] = req
            if self._ws and self.connected:
                try:
                    self._ws.send(json.dumps(req))
                except Exception:
                    pass
            return sub_id

    def subscribe_account(self, address: str, commitment: str = "confirmed") -> int:
        with self._lock:
            sub_id = self._next_id
            self._next_id += 1
            req = {
                "jsonrpc": "2.0", "id": sub_id, "method": "accountSubscribe",
                "params": [address, {"encoding": "jsonParsed", "commitment": commitment}],
            }
            self._subscriptions[sub_id] = req
            if self._ws and self.connected:
                try:
                    self._ws.send(json.dumps(req))
                except Exception:
                    pass
            return sub_id


# ================================================================================
#  MARKET DATA
# ================================================================================

class MarketData:
    """Fetches prices and pair metadata from Jupiter / DexScreener, builds
    local OHLCV candles from repeated price polls (memecoins on DEXes rarely
    expose a clean public OHLC API), and caches aggressively to stay polite
    to upstream services.
    """

    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.source = cfg.get("monitor.price_source", "jupiter")
        self.session = requests.Session()
        self.session.headers.update({"User-Agent": f"LaxTrader/{VERSION}"})
        self.cache = LRUCache(maxsize=1024, ttl=5.0)
        self.pair_cache = LRUCache(maxsize=512, ttl=15.0)
        self.limiter = TokenBucketRateLimiter(rate_per_sec=4.0, burst=8)
        self.logger = logging.getLogger("lax.market")
        # mint -> deque of Candle (built locally from polled prices)
        self._candle_builders: Dict[str, "CandleBuilder"] = {}

    # ─── Price ──────────────────────────────────────────────────────────────

    def get_price_usd(self, mint: str, force: bool = False) -> Optional[float]:
        cache_key = f"price:{mint}"
        if not force:
            cached = self.cache.get(cache_key)
            if cached is not None:
                return cached
        price = self._price_jupiter(mint)
        if price is None:
            price = self._price_dexscreener(mint)
        if price is not None:
            self.cache.set(cache_key, price)
        return price

    def get_pair_price(self, base_mint: str, quote_mint: str) -> Optional[float]:
        base_p = self.get_price_usd(base_mint)
        quote_p = self.get_price_usd(quote_mint)
        if not base_p or not quote_p:
            return None
        return base_p / quote_p

    def _price_jupiter(self, mint: str) -> Optional[float]:
        self.limiter.acquire()
        try:
            r = self.session.get(JUPITER_PRICE_API, params={"ids": mint}, timeout=10)
            r.raise_for_status()
            data = r.json()
            entry = data.get("data", {}).get(mint)
            if entry and "price" in entry:
                return float(entry["price"])
        except Exception as e:
            self.logger.debug(f"jupiter price failed for {truncate_addr(mint)}: {e}")
        return None

    def _price_dexscreener(self, mint: str) -> Optional[float]:
        pair = self.get_best_pair(mint)
        if pair:
            try:
                return float(pair.get("priceUsd") or 0) or None
            except (TypeError, ValueError):
                return None
        return None

    # ─── Pair metadata ──────────────────────────────────────────────────────

    def get_pairs(self, mint: str) -> List[Dict[str, Any]]:
        cache_key = f"pairs:{mint}"
        cached = self.pair_cache.get(cache_key)
        if cached is not None:
            return cached
        self.limiter.acquire()
        try:
            r = self.session.get(f"{DEXSCREENER_TOKENS_API}/{mint}", timeout=12)
            r.raise_for_status()
            data = r.json()
            pairs = data.get("pairs") or []
            self.pair_cache.set(cache_key, pairs)
            return pairs
        except Exception as e:
            self.logger.debug(f"dexscreener pairs failed for {truncate_addr(mint)}: {e}")
            return []

    def get_best_pair(self, mint: str) -> Optional[Dict[str, Any]]:
        """Return the highest-liquidity pair for a mint."""
        pairs = self.get_pairs(mint)
        if not pairs:
            return None
        return max(pairs, key=lambda p: float((p.get("liquidity") or {}).get("usd", 0) or 0))

    def search_pairs(self, query: str) -> List[Dict[str, Any]]:
        self.limiter.acquire()
        try:
            r = self.session.get(DEXSCREENER_SEARCH_API, params={"q": query}, timeout=12)
            r.raise_for_status()
            return (r.json() or {}).get("pairs") or []
        except Exception as e:
            self.logger.debug(f"dexscreener search failed for '{query}': {e}")
            return []

    def build_token_info(self, mint: str) -> Optional[TokenInfo]:
        pair = self.get_best_pair(mint)
        if not pair:
            return None
        base = pair.get("baseToken", {}) if pair.get("baseToken", {}).get("address") == mint else pair.get("baseToken", {})
        try:
            info = TokenInfo(
                mint=mint,
                symbol=(pair.get("baseToken") or {}).get("symbol", ""),
                name=(pair.get("baseToken") or {}).get("name", ""),
                price_usd=float(pair.get("priceUsd") or 0),
                price_sol=float(pair.get("priceNative") or 0),
                market_cap_usd=float(pair.get("fdv") or pair.get("marketCap") or 0),
                liquidity_usd=float((pair.get("liquidity") or {}).get("usd") or 0),
                volume_24h_usd=float((pair.get("volume") or {}).get("h24") or 0),
                pair_address=pair.get("pairAddress", ""),
                dex_id=pair.get("dexId", ""),
                created_at=int((pair.get("pairCreatedAt") or 0) / 1000) if pair.get("pairCreatedAt") else 0,
            )
            return info
        except (TypeError, ValueError) as e:
            self.logger.debug(f"failed to parse pair for {truncate_addr(mint)}: {e}")
            return None

    # ─── Local candle building from polled prices ──────────────────────────

    def get_or_create_builder(self, mint: str, interval_seconds: int = 60, max_len: int = 500) -> "CandleBuilder":
        if mint not in self._candle_builders:
            self._candle_builders[mint] = CandleBuilder(interval_seconds=interval_seconds, max_len=max_len)
        return self._candle_builders[mint]

    def poll_and_update_candles(self, mint: str, interval_seconds: int = 60) -> Optional[Candle]:
        price = self.get_price_usd(mint)
        if price is None:
            return None
        builder = self.get_or_create_builder(mint, interval_seconds=interval_seconds)
        pair = self.get_best_pair(mint)
        volume_hint = 0.0
        if pair:
            try:
                volume_hint = float((pair.get("volume") or {}).get("m5") or 0) / 5.0
            except (TypeError, ValueError):
                volume_hint = 0.0
        return builder.update(price, volume_hint)

    def get_candles(self, mint: str) -> List[Candle]:
        builder = self._candle_builders.get(mint)
        return list(builder.candles) if builder else []


class CandleBuilder:
    """Aggregates a stream of (price, volume) samples into fixed-interval OHLCV candles."""

    def __init__(self, interval_seconds: int = 60, max_len: int = 500):
        self.interval_seconds = interval_seconds
        self.candles: deque = deque(maxlen=max_len)
        self._current: Optional[Candle] = None
        self._bucket_start: Optional[int] = None

    def update(self, price: float, volume: float = 0.0) -> Optional[Candle]:
        now = int(time.time())
        bucket = now - (now % self.interval_seconds)
        if self._bucket_start is None or bucket != self._bucket_start:
            if self._current is not None:
                self.candles.append(self._current)
            self._bucket_start = bucket
            self._current = Candle(timestamp=bucket, open=price, high=price,
                                    low=price, close=price, volume=volume)
        else:
            c = self._current
            c.high = max(c.high, price)
            c.low = min(c.low, price)
            c.close = price
            c.volume += volume
        return self._current

    def closed_candles(self) -> List[Candle]:
        """All fully-closed candles (excludes the still-forming current one)."""
        return list(self.candles)

    def all_candles_including_current(self) -> List[Candle]:
        out = list(self.candles)
        if self._current is not None:
            out.append(self._current)
        return out


def generate_synthetic_candles(n: int = 500, start_price: float = 0.000001,
                                volatility: float = 0.035, drift: float = 0.0002,
                                interval_seconds: int = 60,
                                seed: Optional[int] = None) -> List[Candle]:
    """Random-walk candle generator for backtests/tests when no live data is used.
    Memecoin-flavoured: higher volatility and fatter tails than a typical asset.
    """
    rng = random.Random(seed)
    candles: List[Candle] = []
    price = start_price
    now = int(time.time()) - n * interval_seconds
    for i in range(n):
        # occasional volatility spikes to emulate memecoin behaviour
        vol = volatility * (3.0 if rng.random() < 0.03 else 1.0)
        ret = rng.gauss(drift, vol)
        new_price = max(price * (1 + ret), 1e-12)
        hi = max(price, new_price) * (1 + abs(rng.gauss(0, vol / 3)))
        lo = min(price, new_price) * (1 - abs(rng.gauss(0, vol / 3)))
        lo = max(lo, 1e-12)
        vol_amt = abs(rng.gauss(5000, 3000)) * (1 + abs(ret) * 20)
        candles.append(Candle(
            timestamp=now + i * interval_seconds,
            open=price, high=hi, low=lo, close=new_price, volume=vol_amt,
        ))
        price = new_price
    return candles


# ================================================================================
#  TOKEN SCANNER
# ================================================================================

class TokenScanner:
    """Discovers candidate memecoins via DexScreener search/pairs endpoints
    and maintains a watchlist of candidates that pass basic liquidity/age
    filters before being handed to deeper security analysis.
    """

    def __init__(self, cfg: Config, market: MarketData):
        self.cfg = cfg
        self.market = market
        self.logger = logging.getLogger("lax.scanner")
        self.min_liquidity = float(cfg.get("scanner.min_liquidity_usd", 3000))
        self.min_age = int(cfg.get("scanner.min_age_seconds", 60))
        self.max_age = int(cfg.get("scanner.max_age_seconds", 86400 * 3))
        self.min_volume = float(cfg.get("scanner.min_volume_24h_usd", 2000))
        self.watchlist_size = int(cfg.get("scanner.watchlist_size", 50))
        self.candidates: "OrderedDict[str, ScanCandidate]" = OrderedDict()
        self._lock = threading.Lock()
        self._seen_mints: set = set()

    def _passes_basic_filters(self, token: TokenInfo) -> Tuple[bool, str]:
        if token.liquidity_usd < self.min_liquidity:
            return False, f"liquidity {fmt_usd(token.liquidity_usd)} < min {fmt_usd(self.min_liquidity)}"
        if token.volume_24h_usd < self.min_volume:
            return False, f"24h volume {fmt_usd(token.volume_24h_usd)} < min {fmt_usd(self.min_volume)}"
        if token.created_at:
            age = now_ts() - token.created_at
            if age < self.min_age:
                return False, f"too new ({age}s old)"
            if age > self.max_age:
                return False, f"too old ({age}s old)"
        return True, "ok"

    def scan_query(self, query: str) -> List[TokenInfo]:
        """Search DexScreener for pairs matching a free-text query (e.g. 'solana')."""
        pairs = self.market.search_pairs(query)
        results: List[TokenInfo] = []
        for p in pairs:
            if p.get("chainId") != "solana":
                continue
            try:
                token = TokenInfo(
                    mint=(p.get("baseToken") or {}).get("address", ""),
                    symbol=(p.get("baseToken") or {}).get("symbol", ""),
                    name=(p.get("baseToken") or {}).get("name", ""),
                    price_usd=float(p.get("priceUsd") or 0),
                    market_cap_usd=float(p.get("fdv") or p.get("marketCap") or 0),
                    liquidity_usd=float((p.get("liquidity") or {}).get("usd") or 0),
                    volume_24h_usd=float((p.get("volume") or {}).get("h24") or 0),
                    pair_address=p.get("pairAddress", ""),
                    dex_id=p.get("dexId", ""),
                    created_at=int((p.get("pairCreatedAt") or 0) / 1000) if p.get("pairCreatedAt") else 0,
                )
            except (TypeError, ValueError):
                continue
            if not token.mint or not is_valid_solana_address(token.mint):
                continue
            results.append(token)
        return results

    def scan_once(self, queries: Optional[List[str]] = None) -> List[ScanCandidate]:
        """Run one scan pass, updating and returning newly-qualified candidates."""
        queries = queries or ["solana", "pump", "meme", "sol"]
        new_candidates: List[ScanCandidate] = []
        for q in queries:
            tokens = self.scan_query(q)
            for token in tokens:
                if token.mint in self._seen_mints:
                    continue
                ok, reason = self._passes_basic_filters(token)
                with self._lock:
                    if token.mint in self.candidates:
                        cand = self.candidates[token.mint]
                        cand.token = token
                        cand.last_updated = now_ts()
                        if ok and cand.status == ScanStatus.NEW:
                            cand.status = ScanStatus.WATCHING
                    else:
                        status = ScanStatus.WATCHING if ok else ScanStatus.REJECTED
                        cand = ScanCandidate(token=token, status=status)
                        self.candidates[token.mint] = cand
                        self._seen_mints.add(token.mint)
                        if ok:
                            new_candidates.append(cand)
                        self.logger.debug(f"scan: {token.symbol or truncate_addr(token.mint)} -> {status.value} ({reason})")
                self._trim_watchlist()
        return new_candidates

    def _trim_watchlist(self) -> None:
        with self._lock:
            if len(self.candidates) <= self.watchlist_size * 4:
                return
            # Drop the oldest rejected/expired entries first
            to_drop = [m for m, c in self.candidates.items()
                       if c.status in (ScanStatus.REJECTED, ScanStatus.EXPIRED)]
            for m in to_drop[: max(0, len(self.candidates) - self.watchlist_size * 2)]:
                del self.candidates[m]

    def get_watchlist(self) -> List[ScanCandidate]:
        with self._lock:
            items = [c for c in self.candidates.values() if c.status in (ScanStatus.WATCHING, ScanStatus.QUALIFIED)]
        items.sort(key=lambda c: c.score, reverse=True)
        return items[: self.watchlist_size]

    def mark_qualified(self, mint: str, score: float) -> None:
        with self._lock:
            if mint in self.candidates:
                self.candidates[mint].status = ScanStatus.QUALIFIED
                self.candidates[mint].score = score
                self.candidates[mint].last_updated = now_ts()

    def mark_rejected(self, mint: str, reason: str = "") -> None:
        with self._lock:
            if mint in self.candidates:
                self.candidates[mint].status = ScanStatus.REJECTED
                self.candidates[mint].last_updated = now_ts()


# ================================================================================
#  TOKEN SECURITY ANALYZER (rug-pull risk scoring)
# ================================================================================

class TokenSecurityAnalyzer:
    """Heuristic security analysis for Solana SPL tokens.

    This is NOT a substitute for a full on-chain audit. It combines several
    cheap, well-known heuristics used across the memecoin-trading community:
      - Is the mint authority still active? (creator can mint more supply)
      - Is the freeze authority still active? (creator can freeze holders)
      - Holder concentration (top 10 holders' % of supply)
      - LP locked/burned percentage
      - Creator's remaining supply share
      - Basic honeypot heuristic: can the token realistically be sold
        (approximated via sell-side liquidity depth, since we do not
        execute a real simulated sell against every token)
    """

    def __init__(self, cfg: Config, rpc: SolanaClient, market: MarketData):
        self.cfg = cfg
        self.rpc = rpc
        self.market = market
        self.logger = logging.getLogger("lax.security")
        self.max_top10_pct = float(cfg.get("security.max_top10_holder_pct", 45.0))
        self.reject_mint_auth = bool(cfg.get("security.reject_if_mint_authority_active", True))
        self.reject_freeze_auth = bool(cfg.get("security.reject_if_freeze_authority_active", True))
        self.min_lp_locked_pct = float(cfg.get("security.min_lp_locked_or_burned_pct", 80.0))
        self.min_holder_count = int(cfg.get("security.min_holder_count", 30))
        self.max_creator_pct = float(cfg.get("security.max_creator_supply_pct", 15.0))
        self.min_score_to_trade = float(cfg.get("security.min_security_score_to_trade", 60.0))

    def fetch_mint_authorities(self, mint: str) -> Tuple[Optional[str], Optional[str], bool]:
        """Returns (mint_authority, freeze_authority, is_token_2022)."""
        try:
            acc = self.rpc.get_account_info(mint, encoding="jsonParsed")
        except (RpcError, InvalidAddressError) as e:
            self.logger.debug(f"mint authority lookup failed for {truncate_addr(mint)}: {e}")
            return None, None, False
        if not acc:
            return None, None, False
        owner_program = acc.get("owner", "")
        is_2022 = owner_program == TOKEN_2022_PROGRAM_ID
        try:
            info = acc["data"]["parsed"]["info"]
            mint_auth = info.get("mintAuthority")
            freeze_auth = info.get("freezeAuthority")
            return mint_auth, freeze_auth, is_2022
        except (KeyError, TypeError):
            return None, None, is_2022

    def fetch_top_holders(self, mint: str, supply: float) -> List[TokenHolder]:
        try:
            largest = self.rpc.get_token_largest_accounts(mint)
        except (RpcError, InvalidAddressError) as e:
            self.logger.debug(f"largest accounts lookup failed for {truncate_addr(mint)}: {e}")
            return []
        holders: List[TokenHolder] = []
        for a in largest:
            pct = safe_div(a["amount"], supply) * 100.0 if supply else 0.0
            holders.append(TokenHolder(address=a["address"], amount=a["amount"], pct_of_supply=pct))
        return holders

    def analyze(self, token: TokenInfo, creator: Optional[str] = None) -> SecurityReport:
        report = SecurityReport(mint=token.mint)
        score = 100.0  # start clean, deduct for each red flag

        # 1. Supply / mint info
        supply_info = None
        try:
            supply_info = self.rpc.get_token_supply(token.mint)
        except (RpcError, InvalidAddressError) as e:
            self.logger.debug(f"supply lookup failed: {e}")
        supply = float(supply_info.get("uiAmount") or 0) if supply_info else token.supply

        # 2. Mint / freeze authority
        mint_auth, freeze_auth, is_2022 = self.fetch_mint_authorities(token.mint)
        token.mint_authority = mint_auth
        token.freeze_authority = freeze_auth
        token.is_token_2022 = is_2022

        if mint_auth:
            report.add("MINT_AUTHORITY_ACTIVE", RiskLevel.CRITICAL,
                       "Mint authority is still active — creator can mint unlimited new supply")
            score -= 40 if self.reject_mint_auth else 20
        else:
            report.add("MINT_AUTHORITY_REVOKED", RiskLevel.VERY_LOW, "Mint authority revoked")

        if freeze_auth:
            report.add("FREEZE_AUTHORITY_ACTIVE", RiskLevel.HIGH,
                       "Freeze authority is still active — creator can freeze holder accounts")
            score -= 25 if self.reject_freeze_auth else 12
        else:
            report.add("FREEZE_AUTHORITY_REVOKED", RiskLevel.VERY_LOW, "Freeze authority revoked")

        # 3. Holder concentration
        holders = self.fetch_top_holders(token.mint, supply)
        token.top_holders = holders
        token.holder_count = max(token.holder_count, len(holders))
        top10_pct = sum(h.pct_of_supply for h in holders[:10])
        if top10_pct > self.max_top10_pct:
            sev = RiskLevel.CRITICAL if top10_pct > 70 else RiskLevel.HIGH
            report.add("HIGH_HOLDER_CONCENTRATION", sev,
                       f"Top 10 holders control {top10_pct:.1f}% of supply (max allowed {self.max_top10_pct:.1f}%)")
            score -= min(35, (top10_pct - self.max_top10_pct) * 0.8)
        else:
            report.add("HOLDER_CONCENTRATION_OK", RiskLevel.LOW,
                       f"Top 10 holders control {top10_pct:.1f}% of supply")

        # 4. Creator supply share (best-effort: treat the single largest
        #    holder as a creator-wallet proxy when no creator is supplied)
        if holders:
            creator_pct = holders[0].pct_of_supply
            if creator_pct > self.max_creator_pct:
                report.add("LARGE_SINGLE_HOLDER", RiskLevel.HIGH,
                           f"Largest single wallet holds {creator_pct:.1f}% of supply")
                score -= min(20, (creator_pct - self.max_creator_pct) * 0.5)

        # 5. LP lock/burn — DexScreener doesn't expose this directly, so we
        #    treat liquidity relative to market cap as a rough, conservative
        #    proxy: extremely low liquidity-to-mcap ratio increases rug risk.
        lp_ratio = safe_div(token.liquidity_usd, token.market_cap_usd) * 100.0 if token.market_cap_usd else 0.0
        if lp_ratio < 3.0 and token.market_cap_usd > 0:
            report.add("LOW_LIQUIDITY_RATIO", RiskLevel.HIGH,
                       f"Liquidity is only {lp_ratio:.2f}% of market cap — thin exit liquidity")
            score -= 15
        token.lp_locked_pct = 0.0  # unknown without a locker-specific API; left explicit, not assumed safe

        # 6. Holder count
        if token.holder_count and token.holder_count < self.min_holder_count:
            report.add("LOW_HOLDER_COUNT", RiskLevel.MEDIUM,
                       f"Only {token.holder_count} holders (min recommended {self.min_holder_count})")
            score -= 10

        # 7. Liquidity sanity
        if token.liquidity_usd <= 0:
            report.add("NO_LIQUIDITY", RiskLevel.CRITICAL, "No liquidity found for this token")
            score -= 50

        # 8. Age sanity (extremely new tokens are statistically more likely to rug)
        if token.created_at:
            age_min = (now_ts() - token.created_at) / 60.0
            if age_min < 5:
                report.add("EXTREMELY_NEW", RiskLevel.HIGH, f"Token is only {age_min:.1f} minutes old")
                score -= 10

        score = clamp(score, 0.0, 100.0)
        report.risk_score = score
        if score >= 80:
            report.risk_level = RiskLevel.VERY_LOW
        elif score >= 60:
            report.risk_level = RiskLevel.LOW
        elif score >= 40:
            report.risk_level = RiskLevel.MEDIUM
        elif score >= 20:
            report.risk_level = RiskLevel.HIGH
        else:
            report.risk_level = RiskLevel.CRITICAL

        hard_fail = (
            (mint_auth and self.reject_mint_auth) or
            (freeze_auth and self.reject_freeze_auth) or
            token.liquidity_usd <= 0
        )
        report.passed = (not hard_fail) and (score >= self.min_score_to_trade)
        return report


# ================================================================================
#  LIQUIDITY ANALYZER
# ================================================================================

class LiquidityAnalyzer:
    """Estimates tradable depth and expected slippage using a constant-product
    (x*y=k) approximation seeded from the pool's reported liquidity in USD.
    This is an approximation — real pools may use different curves — but it
    gives a conservative, directionally-correct slippage estimate.
    """

    def __init__(self, cfg: Config, market: MarketData):
        self.cfg = cfg
        self.market = market
        self.logger = logging.getLogger("lax.liquidity")

    def analyze(self, token: TokenInfo, sizes_usd: Optional[List[float]] = None) -> LiquidityReport:
        sizes_usd = sizes_usd or [50, 200, 500, 1000, 5000]
        liquidity = token.liquidity_usd
        report = LiquidityReport(mint=token.mint, liquidity_usd=liquidity)

        if liquidity <= 0:
            report.is_sufficient = False
            return report

        # Assume liquidity is split ~50/50 between base and quote reserves.
        reserve_quote = liquidity / 2.0
        reserve_base = liquidity / 2.0  # in USD-equivalent terms for estimation

        for size in sizes_usd:
            # constant product slippage estimate for a buy of `size` USD worth
            # price_impact ~= size / (reserve_quote + size)
            impact = safe_div(size, reserve_quote + size)
            report.estimated_slippage_bps[size] = impact * 10_000

        # Depth for ~1% impact: solve size such that size/(reserve+size) = 0.01
        # => size = reserve * 0.01 / (1 - 0.01)
        report.depth_buy_1pct = reserve_quote * 0.01 / 0.99
        report.depth_sell_1pct = reserve_base * 0.01 / 0.99
        report.is_sufficient = liquidity >= 1000.0
        return report

    def estimate_slippage_bps(self, token: TokenInfo, size_usd: float) -> float:
        liquidity = token.liquidity_usd
        if liquidity <= 0:
            return 10_000.0  # effectively "can't trade"
        reserve_quote = liquidity / 2.0
        return safe_div(size_usd, reserve_quote + size_usd) * 10_000


# ================================================================================
#  WALLET ANALYZER
# ================================================================================

class WalletAnalyzer:
    """Profiles wallets (creators, top holders, counterparties) for whale and
    suspicious-activity heuristics: unusually high balances relative to the
    ecosystem, very recent first activity, or bursty transaction patterns
    consistent with sniping/bundling bots.
    """

    WHALE_SOL_THRESHOLD = 500.0

    def __init__(self, cfg: Config, rpc: SolanaClient):
        self.cfg = cfg
        self.rpc = rpc
        self.logger = logging.getLogger("lax.wallet")
        self._cache = LRUCache(maxsize=256, ttl=120.0)

    def profile(self, address: str) -> WalletProfile:
        cached = self._cache.get(address)
        if cached is not None:
            return cached

        profile = WalletProfile(address=address)
        try:
            profile.sol_balance = self.rpc.get_sol_balance(address)
        except (RpcError, InvalidAddressError) as e:
            profile.notes.append(f"balance lookup failed: {e}")

        try:
            accounts = self.rpc.get_token_accounts_by_owner(address)
            profile.token_accounts = len(accounts)
        except (RpcError, InvalidAddressError) as e:
            profile.notes.append(f"token account lookup failed: {e}")

        try:
            sigs = self.rpc.get_signatures_for_address(address, limit=100)
            profile.tx_count_estimate = len(sigs)
            if sigs:
                oldest = sigs[-1].get("blockTime")
                if oldest:
                    profile.age_days = max(0.0, (now_ts() - oldest) / 86400.0)
                # Bursty activity heuristic: many signatures within a very
                # short window suggests bot / bundler behaviour.
                times = [s.get("blockTime") for s in sigs if s.get("blockTime")]
                if len(times) >= 20:
                    span = max(times) - min(times)
                    if span < 60 and len(times) >= 20:
                        profile.is_suspicious = True
                        profile.notes.append("20+ transactions within 60 seconds (bot-like burst)")
        except (RpcError, InvalidAddressError) as e:
            profile.notes.append(f"signature lookup failed: {e}")

        if profile.sol_balance >= self.WHALE_SOL_THRESHOLD:
            profile.is_whale = True
            profile.notes.append(f"holds {profile.sol_balance:.1f} SOL (whale threshold {self.WHALE_SOL_THRESHOLD})")

        if profile.age_days is not None and profile.age_days < 1 and profile.tx_count_estimate > 50:
            profile.is_suspicious = True
            profile.notes.append("wallet is <1 day old with unusually high transaction count")

        self._cache.set(address, profile)
        return profile

    def analyze_holders(self, holders: List[TokenHolder], sample: int = 10) -> Dict[str, Any]:
        """Batch-profile the top N holders and summarize whale/suspicious counts."""
        results = []
        for h in holders[:sample]:
            if not is_valid_solana_address(h.address):
                continue
            p = self.profile(h.address)
            results.append(p)
        whales = sum(1 for p in results if p.is_whale)
        suspicious = sum(1 for p in results if p.is_suspicious)
        return {
            "profiled": len(results),
            "whales": whales,
            "suspicious": suspicious,
            "profiles": results,
        }


# ================================================================================
#  TECHNICAL INDICATORS
# ================================================================================

class Indicators:
    """Technical analysis indicator library. All functions return lists
    aligned with the input (None where insufficient history exists) so
    callers can safely index with [-1] / [-2] without off-by-one errors.
    """

    @staticmethod
    def sma(values: List[float], period: int) -> List[Optional[float]]:
        out: List[Optional[float]] = [None] * len(values)
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
        out: List[Optional[float]] = [None] * len(values)
        if period <= 0 or len(values) < period:
            return out
        k = 2 / (period + 1)
        sma0 = sum(values[:period]) / period
        out[period - 1] = sma0
        prev = sma0
        for i in range(period, len(values)):
            prev = values[i] * k + prev * (1 - k)
            out[i] = prev
        return out

    @staticmethod
    def wma(values: List[float], period: int) -> List[Optional[float]]:
        out: List[Optional[float]] = [None] * len(values)
        if period <= 0 or len(values) < period:
            return out
        weights = list(range(1, period + 1))
        denom = sum(weights)
        for i in range(period - 1, len(values)):
            window = values[i - period + 1:i + 1]
            out[i] = sum(w * v for w, v in zip(weights, window)) / denom
        return out

    @staticmethod
    def rsi(values: List[float], period: int = 14) -> List[Optional[float]]:
        out: List[Optional[float]] = [None] * len(values)
        if len(values) <= period:
            return out
        gains, losses = 0.0, 0.0
        for i in range(1, period + 1):
            diff = values[i] - values[i - 1]
            if diff >= 0:
                gains += diff
            else:
                losses -= diff
        avg_gain = gains / period
        avg_loss = losses / period
        rs = (avg_gain / avg_loss) if avg_loss > 0 else float("inf")
        out[period] = 100 - (100 / (1 + rs))
        for i in range(period + 1, len(values)):
            diff = values[i] - values[i - 1]
            gain = max(diff, 0)
            loss = max(-diff, 0)
            avg_gain = (avg_gain * (period - 1) + gain) / period
            avg_loss = (avg_loss * (period - 1) + loss) / period
            rs = (avg_gain / avg_loss) if avg_loss > 0 else float("inf")
            out[i] = 100 - (100 / (1 + rs))
        return out

    @staticmethod
    def macd(values: List[float], fast: int = 12, slow: int = 26, signal: int = 9
              ) -> Tuple[List[Optional[float]], List[Optional[float]], List[Optional[float]]]:
        ema_fast = Indicators.ema(values, fast)
        ema_slow = Indicators.ema(values, slow)
        macd_line: List[Optional[float]] = [
            (f - s) if (f is not None and s is not None) else None
            for f, s in zip(ema_fast, ema_slow)
        ]
        valid = [v for v in macd_line if v is not None]
        if len(valid) < signal:
            return macd_line, [None] * len(values), [None] * len(values)
        sig_full: List[Optional[float]] = [None] * len(values)
        sig_vals = Indicators.ema(valid, signal)
        offset = len(values) - len(valid)
        for i, v in enumerate(sig_vals):
            if v is not None:
                sig_full[offset + i] = v
        hist: List[Optional[float]] = [
            (m - s) if (m is not None and s is not None) else None
            for m, s in zip(macd_line, sig_full)
        ]
        return macd_line, sig_full, hist

    @staticmethod
    def bollinger(values: List[float], period: int = 20, mult: float = 2.0
                  ) -> Tuple[List[Optional[float]], List[Optional[float]], List[Optional[float]]]:
        middle = Indicators.sma(values, period)
        upper: List[Optional[float]] = [None] * len(values)
        lower: List[Optional[float]] = [None] * len(values)
        for i in range(period - 1, len(values)):
            window = values[i - period + 1:i + 1]
            sd = statistics.pstdev(window)
            if middle[i] is not None:
                upper[i] = middle[i] + mult * sd
                lower[i] = middle[i] - mult * sd
        return lower, middle, upper

    @staticmethod
    def atr(highs: List[float], lows: List[float], closes: List[float],
            period: int = 14) -> List[Optional[float]]:
        out: List[Optional[float]] = [None] * len(closes)
        if len(closes) < period + 1:
            return out
        trs = [0.0]
        for i in range(1, len(closes)):
            tr = max(
                highs[i] - lows[i],
                abs(highs[i] - closes[i - 1]),
                abs(lows[i] - closes[i - 1]),
            )
            trs.append(tr)
        atr0 = sum(trs[1:period + 1]) / period
        out[period] = atr0
        prev = atr0
        for i in range(period + 1, len(closes)):
            prev = (prev * (period - 1) + trs[i]) / period
            out[i] = prev
        return out

    @staticmethod
    def stochastic(highs: List[float], lows: List[float], closes: List[float],
                   k_period: int = 14, d_period: int = 3
                   ) -> Tuple[List[Optional[float]], List[Optional[float]]]:
        k: List[Optional[float]] = [None] * len(closes)
        for i in range(k_period - 1, len(closes)):
            hh = max(highs[i - k_period + 1:i + 1])
            ll = min(lows[i - k_period + 1:i + 1])
            k[i] = 50.0 if hh == ll else (closes[i] - ll) / (hh - ll) * 100
        valid_k = [v for v in k if v is not None]
        d_full: List[Optional[float]] = [None] * len(closes)
        d_vals = Indicators.sma(valid_k, d_period)
        offset = len(closes) - len(valid_k)
        for i, v in enumerate(d_vals):
            if v is not None:
                d_full[offset + i] = v
        return k, d_full

    @staticmethod
    def adx(highs: List[float], lows: List[float], closes: List[float],
            period: int = 14) -> List[Optional[float]]:
        n = len(closes)
        out: List[Optional[float]] = [None] * n
        if n < period * 2:
            return out
        plus_dm = [0.0] * n
        minus_dm = [0.0] * n
        trs = [0.0] * n
        for i in range(1, n):
            up = highs[i] - highs[i - 1]
            dn = lows[i - 1] - lows[i]
            plus_dm[i] = up if (up > dn and up > 0) else 0.0
            minus_dm[i] = dn if (dn > up and dn > 0) else 0.0
            trs[i] = max(highs[i] - lows[i], abs(highs[i] - closes[i - 1]), abs(lows[i] - closes[i - 1]))

        def wilder(vals: List[float]) -> List[float]:
            res = [0.0] * n
            res[period] = sum(vals[1:period + 1])
            for i in range(period + 1, n):
                res[i] = res[i - 1] - (res[i - 1] / period) + vals[i]
            return res

        tr_s, pdm_s, mdm_s = wilder(trs), wilder(plus_dm), wilder(minus_dm)
        dx: List[Optional[float]] = [None] * n
        for i in range(period, n):
            if tr_s[i] == 0:
                continue
            pdi = 100 * pdm_s[i] / tr_s[i]
            mdi = 100 * mdm_s[i] / tr_s[i]
            if pdi + mdi == 0:
                continue
            dx[i] = 100 * abs(pdi - mdi) / (pdi + mdi)

        valid_dx = [v for v in dx if v is not None]
        if len(valid_dx) < period:
            return out
        adx_vals: List[Optional[float]] = [None] * len(valid_dx)
        adx_vals[period - 1] = sum(valid_dx[:period]) / period
        for i in range(period, len(valid_dx)):
            adx_vals[i] = (adx_vals[i - 1] * (period - 1) + valid_dx[i]) / period
        offset = n - len(valid_dx)
        for i, v in enumerate(adx_vals):
            if v is not None:
                out[offset + i] = v
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
             volumes: List[float], period: Optional[int] = 20) -> List[Optional[float]]:
        """Volume-weighted average price. With `period` set (default), this is
        a rolling VWAP over the last `period` bars — the useful definition
        for an ongoing memecoin trade, since a session-cumulative VWAP drifts
        further from price the longer a token has traded and stops being a
        meaningful mean-reversion reference. Pass period=None for a full
        cumulative-from-start VWAP instead.
        """
        out: List[Optional[float]] = [None] * len(closes)
        if period is None:
            cum_pv, cum_v = 0.0, 0.0
            for i in range(len(closes)):
                typical = (highs[i] + lows[i] + closes[i]) / 3
                cum_pv += typical * volumes[i]
                cum_v += volumes[i]
                if cum_v > 0:
                    out[i] = cum_pv / cum_v
            return out

        for i in range(len(closes)):
            start = max(0, i - period + 1)
            window_v = volumes[start:i + 1]
            cum_v = sum(window_v)
            if cum_v > 0:
                cum_pv = sum(((highs[j] + lows[j] + closes[j]) / 3) * volumes[j] for j in range(start, i + 1))
                out[i] = cum_pv / cum_v
        return out

    @staticmethod
    def cci(highs: List[float], lows: List[float], closes: List[float],
            period: int = 20) -> List[Optional[float]]:
        out: List[Optional[float]] = [None] * len(closes)
        tp = [(h + l + c) / 3 for h, l, c in zip(highs, lows, closes)]
        for i in range(period - 1, len(tp)):
            window = tp[i - period + 1:i + 1]
            m = sum(window) / period
            md = sum(abs(x - m) for x in window) / period
            out[i] = 0.0 if md == 0 else (tp[i] - m) / (0.015 * md)
        return out

    @staticmethod
    def williams_r(highs: List[float], lows: List[float], closes: List[float],
                   period: int = 14) -> List[Optional[float]]:
        out: List[Optional[float]] = [None] * len(closes)
        for i in range(period - 1, len(closes)):
            hh = max(highs[i - period + 1:i + 1])
            ll = min(lows[i - period + 1:i + 1])
            out[i] = -50.0 if hh == ll else (hh - closes[i]) / (hh - ll) * -100
        return out

    @staticmethod
    def realized_volatility(closes: List[float], period: int = 20) -> List[Optional[float]]:
        """Annualization-agnostic realized volatility (stdev of log returns) over `period`."""
        out: List[Optional[float]] = [None] * len(closes)
        if len(closes) < period + 1:
            return out
        log_returns = []
        for i in range(1, len(closes)):
            if closes[i - 1] > 0 and closes[i] > 0:
                log_returns.append(math.log(closes[i] / closes[i - 1]))
            else:
                log_returns.append(0.0)
        for i in range(period, len(closes)):
            window = log_returns[i - period:i]
            if len(window) >= 2:
                out[i] = statistics.pstdev(window)
        return out

    @staticmethod
    def volume_zscore(volumes: List[float], period: int = 20) -> List[Optional[float]]:
        """How many standard deviations the latest volume is above its rolling mean.
        Used for volume-spike detection, common in memecoin pump signatures.
        """
        out: List[Optional[float]] = [None] * len(volumes)
        for i in range(period, len(volumes)):
            window = volumes[i - period:i]
            mean = statistics.mean(window)
            sd = statistics.pstdev(window)
            if sd > 0:
                out[i] = (volumes[i] - mean) / sd
            elif volumes[i] > mean:
                # Zero variance in the lookback window but the current bar is
                # a clear spike — report a large finite z rather than 0 so
                # spike detection still fires on perfectly flat history.
                out[i] = 10.0
            elif volumes[i] < mean:
                out[i] = -10.0
            else:
                out[i] = 0.0
        return out

    @staticmethod
    def donchian(highs: List[float], lows: List[float], period: int = 20
                 ) -> Tuple[List[Optional[float]], List[Optional[float]]]:
        upper: List[Optional[float]] = [None] * len(highs)
        lower: List[Optional[float]] = [None] * len(lows)
        for i in range(period - 1, len(highs)):
            upper[i] = max(highs[i - period + 1:i + 1])
            lower[i] = min(lows[i - period + 1:i + 1])
        return upper, lower


# ================================================================================
#  STRATEGY FRAMEWORK
# ================================================================================

class Strategy(ABC):
    """Base class for all strategies. Strategies are pure signal generators —
    they never place orders directly; SignalEngine and RiskManager decide
    whether and how to act on a signal.
    """

    name = "base"

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        self.params = params or {}
        self._closes: List[float] = []
        self._highs: List[float] = []
        self._lows: List[float] = []
        self._volumes: List[float] = []
        self._max_history = int(self.params.get("max_history", 500))

    def update(self, candle: Candle) -> None:
        self._closes.append(candle.close)
        self._highs.append(candle.high)
        self._lows.append(candle.low)
        self._volumes.append(candle.volume)
        if len(self._closes) > self._max_history:
            self._closes.pop(0)
            self._highs.pop(0)
            self._lows.pop(0)
            self._volumes.pop(0)

    @property
    def closes(self) -> List[float]:
        return self._closes

    @property
    def highs(self) -> List[float]:
        return self._highs

    @property
    def lows(self) -> List[float]:
        return self._lows

    @property
    def volumes(self) -> List[float]:
        return self._volumes

    @property
    def last_price(self) -> Optional[float]:
        return self._closes[-1] if self._closes else None

    @abstractmethod
    def signal(self) -> Tuple[TradeSignal, str]:
        raise NotImplementedError

    def reset(self) -> None:
        self._closes.clear()
        self._highs.clear()
        self._lows.clear()
        self._volumes.clear()

    def describe(self) -> str:
        return f"{self.name}({self.params})"


class RsiStrategy(Strategy):
    """RSI mean reversion."""
    name = "rsi"

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        super().__init__(params)
        self.period = int(self.params.get("rsi_period", 14))
        self.oversold = float(self.params.get("rsi_oversold", 30))
        self.overbought = float(self.params.get("rsi_overbought", 70))

    def signal(self) -> Tuple[TradeSignal, str]:
        if len(self.closes) < self.period + 2:
            return TradeSignal.NEUTRAL, "not enough data"
        rsi = Indicators.rsi(self.closes, self.period)
        v = rsi[-1]
        if v is None:
            return TradeSignal.NEUTRAL, "rsi unavailable"
        if v < self.oversold - 5:
            return TradeSignal.STRONG_BUY, f"RSI {v:.1f} extremely oversold"
        if v < self.oversold:
            return TradeSignal.BUY, f"RSI {v:.1f} oversold"
        if v > self.overbought + 5:
            return TradeSignal.STRONG_SELL, f"RSI {v:.1f} extremely overbought"
        if v > self.overbought:
            return TradeSignal.SELL, f"RSI {v:.1f} overbought"
        return TradeSignal.NEUTRAL, f"RSI {v:.1f}"


class MacdStrategy(Strategy):
    """MACD crossover / trend continuation."""
    name = "macd"

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        super().__init__(params)
        self.fast = int(self.params.get("macd_fast", 12))
        self.slow = int(self.params.get("macd_slow", 26))
        self.sig = int(self.params.get("macd_signal", 9))

    def signal(self) -> Tuple[TradeSignal, str]:
        if len(self.closes) < self.slow + self.sig + 2:
            return TradeSignal.NEUTRAL, "not enough data"
        macd_line, sig_line, hist = Indicators.macd(self.closes, self.fast, self.slow, self.sig)
        if len(hist) < 2 or hist[-1] is None or hist[-2] is None or macd_line[-1] is None:
            return TradeSignal.NEUTRAL, "macd unavailable"
        h0, h1, m1 = hist[-2], hist[-1], macd_line[-1]
        if h0 < 0 and h1 > 0:
            return TradeSignal.STRONG_BUY, "MACD bullish crossover"
        if h0 > 0 and h1 < 0:
            return TradeSignal.STRONG_SELL, "MACD bearish crossover"
        if h1 > 0 and m1 > 0:
            return (TradeSignal.BUY if h1 > h0 else TradeSignal.NEUTRAL), "MACD rising"
        if h1 < 0 and m1 < 0:
            return (TradeSignal.SELL if h1 < h0 else TradeSignal.NEUTRAL), "MACD falling"
        return TradeSignal.NEUTRAL, f"hist {h1:.6g}"


class BollingerStrategy(Strategy):
    """Bollinger Band mean reversion."""
    name = "bollinger"

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        super().__init__(params)
        self.period = int(self.params.get("bb_period", 20))
        self.mult = float(self.params.get("bb_mult", 2.0))

    def signal(self) -> Tuple[TradeSignal, str]:
        if len(self.closes) < self.period + 2:
            return TradeSignal.NEUTRAL, "not enough data"
        lower, middle, upper = Indicators.bollinger(self.closes, self.period, self.mult)
        if lower[-1] is None or upper[-1] is None:
            return TradeSignal.NEUTRAL, "bands unavailable"
        p = self.closes[-1]
        if p < lower[-1]:
            return TradeSignal.STRONG_BUY, f"price {p:.10g} below lower band"
        if p > upper[-1]:
            return TradeSignal.STRONG_SELL, f"price {p:.10g} above upper band"
        return TradeSignal.NEUTRAL, "inside bands"


class EmaCrossStrategy(Strategy):
    """EMA fast/slow crossover (trend following)."""
    name = "ema_cross"

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        super().__init__(params)
        self.fast = int(self.params.get("ema_fast", 9))
        self.slow = int(self.params.get("ema_slow", 21))

    def signal(self) -> Tuple[TradeSignal, str]:
        if len(self.closes) < self.slow + 2:
            return TradeSignal.NEUTRAL, "not enough data"
        f = Indicators.ema(self.closes, self.fast)
        s = Indicators.ema(self.closes, self.slow)
        f0, f1, s0, s1 = f[-2], f[-1], s[-2], s[-1]
        if None in (f0, f1, s0, s1):
            return TradeSignal.NEUTRAL, "ema unavailable"
        if f0 <= s0 and f1 > s1:
            return TradeSignal.STRONG_BUY, f"EMA{self.fast} crossed above EMA{self.slow}"
        if f0 >= s0 and f1 < s1:
            return TradeSignal.STRONG_SELL, f"EMA{self.fast} crossed below EMA{self.slow}"
        if f1 > s1:
            return TradeSignal.BUY, "uptrend"
        if f1 < s1:
            return TradeSignal.SELL, "downtrend"
        return TradeSignal.NEUTRAL, "flat"


class BreakoutStrategy(Strategy):
    """Donchian-style breakout, the classic memecoin momentum entry."""
    name = "breakout"

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        super().__init__(params)
        self.lookback = int(self.params.get("breakout_lookback", 20))
        self.buffer_pct = float(self.params.get("breakout_buffer_pct", 0.5))

    def signal(self) -> Tuple[TradeSignal, str]:
        if len(self.closes) < self.lookback + 2:
            return TradeSignal.NEUTRAL, "not enough data"
        window_high = max(self.highs[-self.lookback - 1:-1])
        window_low = min(self.lows[-self.lookback - 1:-1])
        p = self.closes[-1]
        buffer = self.buffer_pct / 100
        if p > window_high * (1 + buffer):
            return TradeSignal.STRONG_BUY, f"broke above {window_high:.10g}"
        if p < window_low * (1 - buffer):
            return TradeSignal.STRONG_SELL, f"broke below {window_low:.10g}"
        return TradeSignal.NEUTRAL, f"range [{window_low:.10g}, {window_high:.10g}]"


class MomentumStrategy(Strategy):
    """Rate-of-change momentum."""
    name = "momentum"

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        super().__init__(params)
        self.lookback = int(self.params.get("momentum_lookback", 10))
        self.threshold = float(self.params.get("momentum_threshold_pct", 3.0))

    def signal(self) -> Tuple[TradeSignal, str]:
        if len(self.closes) < self.lookback + 1:
            return TradeSignal.NEUTRAL, "not enough data"
        past, now = self.closes[-self.lookback - 1], self.closes[-1]
        if past == 0:
            return TradeSignal.NEUTRAL, "zero base price"
        change = (now - past) / past * 100
        if change > self.threshold * 2:
            return TradeSignal.STRONG_BUY, f"momentum +{change:.2f}% over {self.lookback} bars"
        if change > self.threshold:
            return TradeSignal.BUY, f"momentum +{change:.2f}% over {self.lookback} bars"
        if change < -self.threshold * 2:
            return TradeSignal.STRONG_SELL, f"momentum {change:.2f}% over {self.lookback} bars"
        if change < -self.threshold:
            return TradeSignal.SELL, f"momentum {change:.2f}% over {self.lookback} bars"
        return TradeSignal.NEUTRAL, f"momentum {change:+.2f}%"


class VolumeSpikeStrategy(Strategy):
    """Detects abnormal volume spikes combined with directional price move —
    a common precursor / confirmation of memecoin pumps (and dumps)."""
    name = "volume_spike"

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        super().__init__(params)
        self.period = int(self.params.get("vol_period", 20))
        self.z_threshold = float(self.params.get("vol_z_threshold", 2.5))

    def signal(self) -> Tuple[TradeSignal, str]:
        if len(self.volumes) < self.period + 1:
            return TradeSignal.NEUTRAL, "not enough data"
        z = Indicators.volume_zscore(self.volumes, self.period)
        if z[-1] is None:
            return TradeSignal.NEUTRAL, "volume z-score unavailable"
        price_change = pct_change(self.closes[-2], self.closes[-1]) if len(self.closes) >= 2 else 0.0
        if z[-1] >= self.z_threshold and price_change > 0:
            sig = TradeSignal.STRONG_BUY if z[-1] >= self.z_threshold * 1.5 else TradeSignal.BUY
            return sig, f"volume spike z={z[-1]:.2f} with price +{price_change:.2f}%"
        if z[-1] >= self.z_threshold and price_change < 0:
            sig = TradeSignal.STRONG_SELL if z[-1] >= self.z_threshold * 1.5 else TradeSignal.SELL
            return sig, f"volume spike z={z[-1]:.2f} with price {price_change:.2f}% (distribution risk)"
        return TradeSignal.NEUTRAL, f"volume z={z[-1]:.2f}"


class TrendFollowingStrategy(Strategy):
    """ADX-gated trend following: only trust direction when ADX confirms a trend."""
    name = "trend_following"

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        super().__init__(params)
        self.adx_period = int(self.params.get("adx_period", 14))
        self.adx_threshold = float(self.params.get("adx_threshold", 25))
        self.ema_period = int(self.params.get("trend_ema_period", 20))

    def signal(self) -> Tuple[TradeSignal, str]:
        need = max(self.adx_period * 2, self.ema_period) + 2
        if len(self.closes) < need:
            return TradeSignal.NEUTRAL, "not enough data"
        adx = Indicators.adx(self.highs, self.lows, self.closes, self.adx_period)
        ema = Indicators.ema(self.closes, self.ema_period)
        if adx[-1] is None or ema[-1] is None:
            return TradeSignal.NEUTRAL, "trend indicators unavailable"
        if adx[-1] < self.adx_threshold:
            return TradeSignal.NEUTRAL, f"ADX {adx[-1]:.1f} — no confirmed trend"
        p = self.closes[-1]
        if p > ema[-1]:
            sig = TradeSignal.STRONG_BUY if adx[-1] > self.adx_threshold * 1.6 else TradeSignal.BUY
            return sig, f"confirmed uptrend, ADX {adx[-1]:.1f}"
        sig = TradeSignal.STRONG_SELL if adx[-1] > self.adx_threshold * 1.6 else TradeSignal.SELL
        return sig, f"confirmed downtrend, ADX {adx[-1]:.1f}"


class MeanReversionStrategy(Strategy):
    """VWAP + Williams %R mean reversion, tuned for choppy memecoin ranges."""
    name = "mean_reversion"

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        super().__init__(params)
        self.wr_period = int(self.params.get("wr_period", 14))
        self.deviation_pct = float(self.params.get("mr_deviation_pct", 4.0))

    def signal(self) -> Tuple[TradeSignal, str]:
        if len(self.closes) < self.wr_period + 2:
            return TradeSignal.NEUTRAL, "not enough data"
        vwap = Indicators.vwap(self.highs, self.lows, self.closes, self.volumes)
        wr = Indicators.williams_r(self.highs, self.lows, self.closes, self.wr_period)
        if vwap[-1] is None or wr[-1] is None:
            return TradeSignal.NEUTRAL, "mean reversion indicators unavailable"
        p = self.closes[-1]
        dev = pct_change(vwap[-1], p)
        if dev < -self.deviation_pct and wr[-1] < -80:
            return TradeSignal.STRONG_BUY, f"{dev:.2f}% below VWAP, Williams%R {wr[-1]:.1f} oversold"
        if dev > self.deviation_pct and wr[-1] > -20:
            return TradeSignal.STRONG_SELL, f"{dev:.2f}% above VWAP, Williams%R {wr[-1]:.1f} overbought"
        return TradeSignal.NEUTRAL, f"{dev:+.2f}% from VWAP"


class ScalpingStrategy(Strategy):
    """Short-horizon EMA + RSI scalping."""
    name = "scalping"

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        super().__init__(params)
        self.ema_fast = int(self.params.get("scalp_ema_fast", 5))
        self.ema_slow = int(self.params.get("scalp_ema_slow", 15))
        self.rsi_period = int(self.params.get("scalp_rsi_period", 7))
        self.rsi_buy = float(self.params.get("scalp_rsi_buy", 45))
        self.rsi_sell = float(self.params.get("scalp_rsi_sell", 55))

    def signal(self) -> Tuple[TradeSignal, str]:
        need = max(self.ema_slow, self.rsi_period) + 2
        if len(self.closes) < need:
            return TradeSignal.NEUTRAL, "not enough data"
        ef = Indicators.ema(self.closes, self.ema_fast)
        es = Indicators.ema(self.closes, self.ema_slow)
        rsi = Indicators.rsi(self.closes, self.rsi_period)
        if None in (ef[-1], es[-1], rsi[-1]):
            return TradeSignal.NEUTRAL, "scalp indicators unavailable"
        if ef[-1] > es[-1] and rsi[-1] < self.rsi_buy:
            return TradeSignal.BUY, f"EMA up + RSI {rsi[-1]:.1f}"
        if ef[-1] < es[-1] and rsi[-1] > self.rsi_sell:
            return TradeSignal.SELL, f"EMA down + RSI {rsi[-1]:.1f}"
        return TradeSignal.NEUTRAL, "no scalp setup"


class CompositeStrategy(Strategy):
    """Weighted ensemble of sub-strategies. Averages a numeric score per
    signal and re-maps it back to a TradeSignal.
    """
    name = "composite"

    SCORE_MAP = {
        TradeSignal.STRONG_BUY: 2.0,
        TradeSignal.BUY: 1.0,
        TradeSignal.NEUTRAL: 0.0,
        TradeSignal.SELL: -1.0,
        TradeSignal.STRONG_SELL: -2.0,
    }

    def __init__(self, params: Optional[Dict[str, Any]] = None):
        super().__init__(params)
        self.strategies: List[Tuple[Strategy, float]] = []

    def add(self, strategy: Strategy, weight: float = 1.0) -> None:
        self.strategies.append((strategy, weight))

    def update(self, candle: Candle) -> None:
        super().update(candle)
        for s, _ in self.strategies:
            s.update(candle)

    def signal(self) -> Tuple[TradeSignal, str]:
        if not self.strategies:
            return TradeSignal.NEUTRAL, "no sub-strategies configured"
        total_w = sum(w for _, w in self.strategies)
        if total_w <= 0:
            return TradeSignal.NEUTRAL, "zero total weight"
        acc = 0.0
        reasons = []
        for s, w in self.strategies:
            sig, reason = s.signal()
            acc += self.SCORE_MAP.get(sig, 0.0) * w
            reasons.append(f"{s.name}:{sig.value}")
        avg = acc / total_w
        joined = "; ".join(reasons)
        if avg >= 1.4:
            return TradeSignal.STRONG_BUY, joined
        if avg >= 0.4:
            return TradeSignal.BUY, joined
        if avg <= -1.4:
            return TradeSignal.STRONG_SELL, joined
        if avg <= -0.4:
            return TradeSignal.SELL, joined
        return TradeSignal.NEUTRAL, joined


STRATEGY_REGISTRY: Dict[str, type] = {
    "rsi": RsiStrategy,
    "macd": MacdStrategy,
    "bollinger": BollingerStrategy,
    "ema_cross": EmaCrossStrategy,
    "breakout": BreakoutStrategy,
    "momentum": MomentumStrategy,
    "volume_spike": VolumeSpikeStrategy,
    "trend_following": TrendFollowingStrategy,
    "mean_reversion": MeanReversionStrategy,
    "scalping": ScalpingStrategy,
}


def build_strategy(name: str, params: Optional[Dict[str, Any]] = None) -> Strategy:
    """Factory resolving a strategy name to an instance. 'composite' builds a
    sensible weighted ensemble tuned for memecoin volatility.
    """
    name = (name or "composite").lower()
    if name == "composite":
        comp = CompositeStrategy(params)
        comp.add(BreakoutStrategy(params), 1.3)
        comp.add(VolumeSpikeStrategy(params), 1.2)
        comp.add(MomentumStrategy(params), 1.0)
        comp.add(EmaCrossStrategy(params), 1.0)
        comp.add(RsiStrategy(params), 0.8)
        comp.add(MacdStrategy(params), 0.8)
        comp.add(TrendFollowingStrategy(params), 0.7)
        return comp
    if name not in STRATEGY_REGISTRY:
        logging.getLogger("lax.strategy").warning(f"Unknown strategy '{name}', falling back to composite")
        return build_strategy("composite", params)
    return STRATEGY_REGISTRY[name](params)


# ================================================================================
#  SIGNAL ENGINE (fusion of strategy signal + security + liquidity)
# ================================================================================

class SignalEngine:
    """Fuses a raw strategy TradeSignal with the token's security report and
    liquidity report into a single actionable Decision plus a 0-100
    opportunity score. This is the layer that turns "the RSI says buy" into
    "should we actually consider this specific memecoin at all".
    """

    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.min_security_score = float(cfg.get("security.min_security_score_to_trade", 60.0))
        self.max_slippage_bps = float(cfg.get("trading.max_allowed_slippage_bps", 500))
        self.logger = logging.getLogger("lax.signal")

    def fuse(self, mint: str, strategy_signal: TradeSignal, strategy_reason: str,
             security: Optional[SecurityReport], liquidity: Optional[LiquidityReport],
             intended_size_usd: float = 0.0) -> FusedSignal:
        reasons: List[str] = [f"strategy={strategy_signal.value} ({strategy_reason})"]

        security_score = security.risk_score if security else 0.0
        liquidity_ok = True

        # Hard security gate — no strategy signal can override a failed
        # security check. This mirrors what the RiskManager enforces later,
        # but rejecting here means we never even queue the trade.
        if security is not None:
            reasons.append(f"security_score={security_score:.1f} ({security.risk_level.value})")
            if not security.passed:
                return FusedSignal(
                    mint=mint, decision=Decision.REJECT, score=0.0,
                    strategy_signal=strategy_signal, strategy_reason=strategy_reason,
                    security_score=security_score, liquidity_ok=False,
                    reasons=reasons + ["security check failed"],
                )
        else:
            reasons.append("security_score=unknown (no report yet)")

        # Liquidity gate
        if liquidity is not None:
            if not liquidity.is_sufficient:
                liquidity_ok = False
                reasons.append("liquidity insufficient")
            if intended_size_usd > 0:
                est_slip = liquidity.estimated_slippage_bps.get(intended_size_usd)
                if est_slip is None:
                    # nearest bucket
                    keys = sorted(liquidity.estimated_slippage_bps.keys())
                    est_slip = liquidity.estimated_slippage_bps.get(keys[-1]) if keys else None
                if est_slip is not None and est_slip > self.max_slippage_bps:
                    liquidity_ok = False
                    reasons.append(f"estimated slippage {est_slip:.0f}bps exceeds max {self.max_slippage_bps:.0f}bps")

        if not liquidity_ok:
            return FusedSignal(
                mint=mint, decision=Decision.REJECT, score=0.0,
                strategy_signal=strategy_signal, strategy_reason=strategy_reason,
                security_score=security_score, liquidity_ok=False, reasons=reasons,
            )

        # Compose a 0..100 opportunity score: 60% strategy conviction, 40% security
        strategy_component = {
            TradeSignal.STRONG_BUY: 100.0, TradeSignal.BUY: 70.0,
            TradeSignal.NEUTRAL: 40.0, TradeSignal.SELL: 20.0, TradeSignal.STRONG_SELL: 0.0,
        }[strategy_signal]
        score = 0.6 * strategy_component + 0.4 * security_score

        if strategy_signal in (TradeSignal.STRONG_BUY, TradeSignal.BUY):
            decision = Decision.BUY if security_score >= self.min_security_score else Decision.REJECT
        elif strategy_signal in (TradeSignal.STRONG_SELL, TradeSignal.SELL):
            decision = Decision.SELL
        else:
            decision = Decision.HOLD

        if decision == Decision.REJECT:
            reasons.append(f"security score {security_score:.1f} below minimum {self.min_security_score:.1f}")

        return FusedSignal(
            mint=mint, decision=decision, score=clamp(score, 0.0, 100.0),
            strategy_signal=strategy_signal, strategy_reason=strategy_reason,
            security_score=security_score, liquidity_ok=liquidity_ok, reasons=reasons,
        )


# ================================================================================
#  RISK MANAGER  (can veto ANY trade regardless of signal)
# ================================================================================

class RiskManager:
    """Enforces position sizing limits, drawdown limits, daily loss limits,
    cooldowns, a circuit breaker, an emergency stop, and basic sanity checks
    on every proposed trade. This is the single choke point through which
    every BUY/SELL must pass before reaching the ExecutionEngine — nothing
    in this codebase is permitted to bypass it.
    """

    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.logger = logging.getLogger("lax.risk")
        self.peak_equity: float = 0.0
        self.start_of_day_equity: float = 0.0
        self.day_start_ts: int = now_ts()
        self.last_trade_ts: float = 0.0
        self.lock = threading.Lock()
        self.breaker = CircuitBreaker(
            failure_threshold=int(cfg.get("risk.circuit_breaker_failures", 5)),
            cooldown_seconds=float(cfg.get("risk.circuit_breaker_cooldown_seconds", 120)),
        )
        self.blacklist_path = Path(cfg.get("risk.blacklist_path", str(BLACKLIST_FILE)))
        self.blacklist: set = set()
        self._load_blacklist()
        self.open_position_count = 0

    # ─── Blacklist persistence ──────────────────────────────────────────────
    # Persisted per-instance at risk.blacklist_path (defaults to a shared file
    # under CONFIG_DIR). Tests and isolated bot instances should override
    # risk.blacklist_path so they never see each other's blacklisted mints.

    def _load_blacklist(self) -> None:
        try:
            if self.blacklist_path.exists():
                self.blacklist = set(json.loads(self.blacklist_path.read_text(encoding="utf-8")))
        except Exception as e:
            self.logger.warning(f"failed to load blacklist: {e}")

    def _save_blacklist(self) -> None:
        try:
            self.blacklist_path.parent.mkdir(parents=True, exist_ok=True)
            self.blacklist_path.write_text(json.dumps(sorted(self.blacklist)), encoding="utf-8")
        except Exception as e:
            self.logger.warning(f"failed to save blacklist: {e}")

    def blacklist_mint(self, mint: str, reason: str = "") -> None:
        with self.lock:
            self.blacklist.add(mint)
        self._save_blacklist()
        self.logger.warning(f"blacklisted {truncate_addr(mint)}: {reason}")

    def is_blacklisted(self, mint: str) -> bool:
        with self.lock:
            return mint in self.blacklist

    # ─── Equity tracking ─────────────────────────────────────────────────────

    def update_equity(self, equity: float) -> None:
        with self.lock:
            if equity > self.peak_equity:
                self.peak_equity = equity
            if self.start_of_day_equity <= 0:
                self.start_of_day_equity = equity
            now = now_ts()
            if now - self.day_start_ts >= 86400:
                self.day_start_ts = now
                self.start_of_day_equity = equity

    def max_drawdown_breached(self, equity: float) -> bool:
        with self.lock:
            if self.peak_equity <= 0:
                return False
            dd = (self.peak_equity - equity) / self.peak_equity * 100
            return dd >= float(self.cfg.get("risk.max_drawdown_pct", 20.0))

    def daily_loss_breached(self, equity: float) -> bool:
        with self.lock:
            if self.start_of_day_equity <= 0:
                return False
            loss = (self.start_of_day_equity - equity) / self.start_of_day_equity * 100
            return loss >= float(self.cfg.get("risk.daily_loss_limit_pct", 15.0))

    def cooldown_active(self) -> bool:
        with self.lock:
            cd = float(self.cfg.get("risk.cooldown_seconds", 45))
            return (time.time() - self.last_trade_ts) < cd

    def mark_trade(self) -> None:
        with self.lock:
            self.last_trade_ts = time.time()

    def emergency_stop_active(self) -> bool:
        return bool(self.cfg.get("risk.emergency_stop", False))

    def set_emergency_stop(self, active: bool) -> None:
        self.cfg.set("risk.emergency_stop", active)
        if active:
            self.logger.critical("EMERGENCY STOP ACTIVATED — all trading halted")
        else:
            self.logger.warning("Emergency stop cleared")

    # ─── Pre-trade validation ────────────────────────────────────────────────

    def validate_order(self, mint: str, side: Side, quantity: float, price: float,
                        equity: float, current_open_positions: int,
                        slippage_bps_estimate: Optional[float] = None) -> Tuple[bool, str]:
        """The single authoritative gate. Returns (approved, reason).

        Any RiskManager check failing means the order MUST NOT be sent to
        the ExecutionEngine, no matter how strong the signal was.
        """
        if self.emergency_stop_active():
            return False, "emergency stop is active"

        if not self.breaker.allow():
            return False, "circuit breaker is open (too many recent failures)"

        if self.is_blacklisted(mint):
            return False, f"{truncate_addr(mint)} is blacklisted"

        if not is_valid_solana_address(mint):
            return False, "invalid mint address"

        if quantity <= 0:
            return False, "quantity must be positive"

        if price <= 0:
            return False, "invalid price (<=0)"

        if not math.isfinite(price) or not math.isfinite(quantity):
            return False, "non-finite price/quantity — inconsistent market data"

        if side == Side.BUY:
            if self.cooldown_active():
                return False, "cooldown active since last trade"

            if current_open_positions >= int(self.cfg.get("risk.max_open_positions", 3)):
                return False, "max open positions reached"

            trade_value = quantity * price
            max_trade_pct = float(self.cfg.get("risk.max_trade_pct_of_equity", 0.20))
            if equity > 0 and trade_value > equity * max_trade_pct:
                return False, (f"trade value {trade_value:.6f} exceeds "
                               f"{max_trade_pct*100:.0f}% of equity ({equity:.6f})")

            max_position_quote = float(self.cfg.get("trading.max_position_quote", 0.20))
            if trade_value > max_position_quote:
                return False, f"trade value {trade_value:.6f} exceeds max_position_quote {max_position_quote:.6f}"

            min_order_quote = float(self.cfg.get("trading.min_order_quote", 0.01))
            if trade_value < min_order_quote:
                return False, f"trade value {trade_value:.6f} below min_order_quote {min_order_quote:.6f}"

            if self.max_drawdown_breached(equity):
                return False, "max drawdown breached — new entries blocked"

            if self.daily_loss_breached(equity):
                return False, "daily loss limit breached — new entries blocked"

            if slippage_bps_estimate is not None:
                max_slip = float(self.cfg.get("trading.max_allowed_slippage_bps", 500))
                if slippage_bps_estimate > max_slip:
                    return False, f"estimated slippage {slippage_bps_estimate:.0f}bps exceeds max {max_slip:.0f}bps"

        return True, "approved"

    def record_execution_result(self, success: bool) -> None:
        if success:
            self.breaker.record_success()
        else:
            self.breaker.record_failure()

    def compute_stops(self, entry_price: float) -> Tuple[Optional[float], Optional[float]]:
        sl_pct = float(self.cfg.get("risk.stop_loss_pct", 0.0))
        tp_pct = float(self.cfg.get("risk.take_profit_pct", 0.0))
        sl = entry_price * (1 - sl_pct / 100) if sl_pct > 0 else None
        tp = entry_price * (1 + tp_pct / 100) if tp_pct > 0 else None
        return sl, tp


# ================================================================================
#  POSITION SIZER
# ================================================================================

class PositionSizer:
    """Computes trade size from equity, config limits, and (optionally) the
    token's security score and estimated volatility — riskier or more
    volatile tokens receive proportionally smaller size.
    """

    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.base_pct = float(cfg.get("trading.position_size_pct", 0.08))
        self.max_position_quote = float(cfg.get("trading.max_position_quote", 0.20))
        self.min_order_quote = float(cfg.get("trading.min_order_quote", 0.01))

    def compute(self, equity: float, price: float,
                security_score: Optional[float] = None,
                volatility: Optional[float] = None) -> float:
        if price <= 0 or equity <= 0:
            return 0.0

        pct = self.base_pct

        # Scale down size for weaker security scores (never scale UP beyond base).
        if security_score is not None:
            factor = clamp(security_score / 100.0, 0.25, 1.0)
            pct *= factor

        # Scale down size for elevated realized volatility.
        if volatility is not None and volatility > 0:
            vol_factor = clamp(1.0 / (1.0 + volatility * 10), 0.3, 1.0)
            pct *= vol_factor

        budget = min(equity * pct, self.max_position_quote)
        if budget < self.min_order_quote:
            return 0.0
        return budget / price


# ================================================================================
#  PORTFOLIO
# ================================================================================

class Portfolio:
    """Tracks cash and multiple open positions (one per mint), realized PnL,
    and total fees. Supports partial position management for multi-token
    trading (unlike a single-symbol portfolio).
    """

    def __init__(self, starting_balance: float, quote_symbol: str = "SOL"):
        self.quote_symbol = quote_symbol
        self.cash = starting_balance
        self.positions: Dict[str, Position] = {}   # mint -> Position
        self.realized_pnl = 0.0
        self.total_fees = 0.0
        self.lock = threading.RLock()

    def equity(self, prices: Dict[str, float]) -> float:
        with self.lock:
            position_value = sum(
                pos.quantity * prices.get(mint, pos.entry_price)
                for mint, pos in self.positions.items()
            )
            return self.cash + position_value

    def has_position(self, mint: str) -> bool:
        with self.lock:
            return mint in self.positions and self.positions[mint].quantity > 0

    def open_position_count(self) -> int:
        with self.lock:
            return len(self.positions)

    def open_position(self, mint: str, symbol: str, price: float, quantity: float,
                      stop_loss: Optional[float] = None,
                      take_profit: Optional[float] = None) -> None:
        with self.lock:
            cost = price * quantity
            if cost > self.cash:
                quantity = safe_div(self.cash, price)
                cost = price * quantity
            self.cash -= cost
            if mint in self.positions:
                pos = self.positions[mint]
                total_qty = pos.quantity + quantity
                pos.entry_price = safe_div(pos.entry_price * pos.quantity + price * quantity, total_qty)
                pos.quantity = total_qty
            else:
                self.positions[mint] = Position(
                    symbol=symbol, mint=mint, quantity=quantity,
                    entry_price=price, entry_time=now_ts(),
                    stop_loss=stop_loss, take_profit=take_profit,
                    trailing_high=price,
                )

    def close_position(self, mint: str, price: float) -> Tuple[float, float, float]:
        """Close a position fully. Returns (quantity_closed, pnl, pnl_pct)."""
        with self.lock:
            if mint not in self.positions or self.positions[mint].quantity <= 0:
                return 0.0, 0.0, 0.0
            pos = self.positions[mint]
            qty = pos.quantity
            proceeds = price * qty
            self.cash += proceeds
            pnl = (price - pos.entry_price) * qty
            pnl_pct = pct_change(pos.entry_price, price)
            self.realized_pnl += pnl
            del self.positions[mint]
            return qty, pnl, pnl_pct

    def get_position(self, mint: str) -> Optional[Position]:
        with self.lock:
            return self.positions.get(mint)

    def snapshot(self, prices: Dict[str, float]) -> Dict[str, Any]:
        with self.lock:
            return {
                "cash": self.cash,
                "realized_pnl": self.realized_pnl,
                "total_fees": self.total_fees,
                "open_positions": {
                    mint: {
                        "symbol": pos.symbol,
                        "quantity": pos.quantity,
                        "entry_price": pos.entry_price,
                        "current_price": prices.get(mint),
                        "unrealized_pnl": pos.unrealized_pnl(prices.get(mint, pos.entry_price)),
                        "unrealized_pnl_pct": pos.unrealized_pnl_pct(prices.get(mint, pos.entry_price)),
                    }
                    for mint, pos in self.positions.items()
                },
                "equity": self.equity(prices),
            }


# ================================================================================
#  DATABASE (SQLite persistence)
# ================================================================================

class Database:
    """SQLite persistence for orders, fills, trades, equity curve, signals,
    and scan history. Thread-safe via a re-entrant lock around the shared
    connection (WAL mode is enabled for better read/write concurrency).
    """

    def __init__(self, path: Path):
        self.path = path
        path.parent.mkdir(parents=True, exist_ok=True)
        self._lock = threading.RLock()
        self._conn = sqlite3.connect(str(path), check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._conn.execute("PRAGMA journal_mode=WAL")
        self._conn.execute("PRAGMA foreign_keys=ON")
        self._init_schema()

    def _init_schema(self) -> None:
        with self._lock:
            self._conn.executescript("""
                CREATE TABLE IF NOT EXISTS orders (
                    id           INTEGER PRIMARY KEY AUTOINCREMENT,
                    client_id    TEXT UNIQUE,
                    mint         TEXT NOT NULL,
                    side         TEXT NOT NULL,
                    order_type   TEXT NOT NULL,
                    quantity     REAL NOT NULL,
                    price        REAL,
                    status       TEXT NOT NULL,
                    mode         TEXT NOT NULL DEFAULT 'paper',
                    created_at   INTEGER NOT NULL,
                    updated_at   INTEGER NOT NULL
                );
                CREATE TABLE IF NOT EXISTS fills (
                    id           INTEGER PRIMARY KEY AUTOINCREMENT,
                    order_id     INTEGER NOT NULL,
                    side         TEXT NOT NULL,
                    quantity     REAL NOT NULL,
                    price        REAL NOT NULL,
                    fee          REAL NOT NULL,
                    txid         TEXT,
                    created_at   INTEGER NOT NULL,
                    FOREIGN KEY(order_id) REFERENCES orders(id) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS trades (
                    id           INTEGER PRIMARY KEY AUTOINCREMENT,
                    mint         TEXT NOT NULL,
                    symbol       TEXT NOT NULL,
                    side         TEXT NOT NULL,
                    entry_price  REAL NOT NULL,
                    exit_price   REAL NOT NULL,
                    quantity     REAL NOT NULL,
                    entry_time   INTEGER NOT NULL,
                    exit_time    INTEGER NOT NULL,
                    pnl          REAL NOT NULL,
                    pnl_pct      REAL NOT NULL,
                    fees         REAL NOT NULL,
                    reason       TEXT,
                    mode         TEXT NOT NULL DEFAULT 'paper'
                );
                CREATE TABLE IF NOT EXISTS equity (
                    id             INTEGER PRIMARY KEY AUTOINCREMENT,
                    timestamp      INTEGER NOT NULL,
                    equity         REAL NOT NULL,
                    cash           REAL NOT NULL,
                    position_value REAL NOT NULL
                );
                CREATE TABLE IF NOT EXISTS signals (
                    id           INTEGER PRIMARY KEY AUTOINCREMENT,
                    mint         TEXT NOT NULL,
                    strategy     TEXT NOT NULL,
                    signal       TEXT NOT NULL,
                    decision     TEXT,
                    score        REAL,
                    price        REAL NOT NULL,
                    reason       TEXT,
                    created_at   INTEGER NOT NULL
                );
                CREATE TABLE IF NOT EXISTS scan_history (
                    id           INTEGER PRIMARY KEY AUTOINCREMENT,
                    mint         TEXT NOT NULL,
                    symbol       TEXT,
                    status       TEXT NOT NULL,
                    liquidity_usd REAL,
                    security_score REAL,
                    created_at   INTEGER NOT NULL
                );
                CREATE TABLE IF NOT EXISTS audit_log (
                    id           INTEGER PRIMARY KEY AUTOINCREMENT,
                    event        TEXT NOT NULL,
                    details      TEXT,
                    created_at   INTEGER NOT NULL
                );

                CREATE INDEX IF NOT EXISTS idx_trades_mint ON trades(mint);
                CREATE INDEX IF NOT EXISTS idx_trades_time ON trades(exit_time);
                CREATE INDEX IF NOT EXISTS idx_equity_time ON equity(timestamp);
                CREATE INDEX IF NOT EXISTS idx_signals_time ON signals(created_at);
                CREATE INDEX IF NOT EXISTS idx_scan_time ON scan_history(created_at);
            """)
            self._conn.commit()

    def execute(self, sql: str, params: tuple = ()) -> sqlite3.Cursor:
        with self._lock:
            try:
                cur = self._conn.execute(sql, params)
                self._conn.commit()
                return cur
            except sqlite3.Error as e:
                raise DatabaseError(str(e)) from e

    def fetchone(self, sql: str, params: tuple = ()) -> Optional[sqlite3.Row]:
        with self._lock:
            return self._conn.execute(sql, params).fetchone()

    def fetchall(self, sql: str, params: tuple = ()) -> List[sqlite3.Row]:
        with self._lock:
            return self._conn.execute(sql, params).fetchall()

    # ─── Orders / fills ──────────────────────────────────────────────────────

    def insert_order(self, mint: str, order: Order, status: OrderStatus, mode: str) -> int:
        now = now_ts()
        cur = self.execute(
            """INSERT INTO orders (client_id, mint, side, order_type, quantity, price, status, mode, created_at, updated_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (order.client_id, mint, order.side.value, order.order_type.value,
             order.quantity, order.price or 0.0, status.value, mode, now, now)
        )
        return cur.lastrowid

    def insert_fill(self, order_id: int, fill: Fill) -> int:
        cur = self.execute(
            """INSERT INTO fills (order_id, side, quantity, price, fee, txid, created_at)
               VALUES (?, ?, ?, ?, ?, ?, ?)""",
            (order_id, fill.side.value, fill.quantity, fill.price, fill.fee, fill.txid, fill.timestamp)
        )
        return cur.lastrowid

    # ─── Trades ──────────────────────────────────────────────────────────────

    def insert_trade(self, trade: Trade, mode: str) -> int:
        cur = self.execute(
            """INSERT INTO trades (mint, symbol, side, entry_price, exit_price, quantity,
                                   entry_time, exit_time, pnl, pnl_pct, fees, reason, mode)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
            (trade.mint, trade.symbol, trade.side.value, trade.entry_price, trade.exit_price,
             trade.quantity, trade.entry_time, trade.exit_time, trade.pnl, trade.pnl_pct,
             trade.fees, trade.reason, mode)
        )
        return cur.lastrowid

    def all_trades(self, mode: Optional[str] = None) -> List[sqlite3.Row]:
        if mode:
            return self.fetchall("SELECT * FROM trades WHERE mode = ? ORDER BY exit_time ASC", (mode,))
        return self.fetchall("SELECT * FROM trades ORDER BY exit_time ASC")

    # ─── Equity ──────────────────────────────────────────────────────────────

    def insert_equity(self, point: EquityPoint) -> None:
        self.execute(
            "INSERT INTO equity (timestamp, equity, cash, position_value) VALUES (?, ?, ?, ?)",
            (point.timestamp, point.equity, point.cash, point.position_value)
        )

    def equity_curve(self, limit: int = 5000) -> List[sqlite3.Row]:
        return self.fetchall("SELECT * FROM equity ORDER BY timestamp ASC LIMIT ?", (limit,))

    # ─── Signals ─────────────────────────────────────────────────────────────

    def insert_signal(self, mint: str, strategy: str, signal: TradeSignal,
                       decision: Optional[Decision], score: Optional[float],
                       price: float, reason: str = "") -> None:
        self.execute(
            """INSERT INTO signals (mint, strategy, signal, decision, score, price, reason, created_at)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?)""",
            (mint, strategy, signal.value, decision.value if decision else None,
             score, price, reason, now_ts())
        )

    def recent_signals(self, limit: int = 20) -> List[sqlite3.Row]:
        return self.fetchall("SELECT * FROM signals ORDER BY created_at DESC LIMIT ?", (limit,))

    # ─── Scan history ────────────────────────────────────────────────────────

    def insert_scan(self, mint: str, symbol: str, status: str,
                     liquidity_usd: float, security_score: Optional[float]) -> None:
        self.execute(
            """INSERT INTO scan_history (mint, symbol, status, liquidity_usd, security_score, created_at)
               VALUES (?, ?, ?, ?, ?, ?)""",
            (mint, symbol, status, liquidity_usd, security_score, now_ts())
        )

    # ─── Audit log ───────────────────────────────────────────────────────────

    def audit(self, event: str, details: Optional[Dict[str, Any]] = None) -> None:
        self.execute(
            "INSERT INTO audit_log (event, details, created_at) VALUES (?, ?, ?)",
            (event, json.dumps(details or {}, default=str), now_ts())
        )

    # ─── Stats ───────────────────────────────────────────────────────────────

    def stats(self, mode: Optional[str] = None) -> Dict[str, Any]:
        where = "WHERE mode = ?" if mode else ""
        params = (mode,) if mode else ()
        row = self.fetchone(f"""
            SELECT
              COUNT(*) AS total,
              COALESCE(SUM(CASE WHEN pnl > 0 THEN 1 ELSE 0 END), 0) AS wins,
              COALESCE(SUM(CASE WHEN pnl <= 0 THEN 1 ELSE 0 END), 0) AS losses,
              COALESCE(SUM(pnl), 0) AS total_pnl,
              COALESCE(SUM(CASE WHEN pnl > 0 THEN pnl ELSE 0 END), 0) AS gross_win,
              COALESCE(SUM(CASE WHEN pnl < 0 THEN -pnl ELSE 0 END), 0) AS gross_loss,
              COALESCE(MAX(pnl), 0) AS best,
              COALESCE(MIN(pnl), 0) AS worst,
              COALESCE(SUM(fees), 0) AS fees
            FROM trades {where}
        """, params)
        if not row:
            return {}
        total = row["total"] or 0
        return {
            "total_trades": total,
            "wins": row["wins"] or 0,
            "losses": row["losses"] or 0,
            "win_rate": (row["wins"] / total * 100) if total else 0.0,
            "total_pnl": row["total_pnl"] or 0.0,
            "gross_win": row["gross_win"] or 0.0,
            "gross_loss": row["gross_loss"] or 0.0,
            "profit_factor": safe_div(row["gross_win"], row["gross_loss"]),
            "best": row["best"] or 0.0,
            "worst": row["worst"] or 0.0,
            "fees": row["fees"] or 0.0,
        }

    def close(self) -> None:
        with self._lock:
            self._conn.close()


# ================================================================================
#  EXECUTION ENGINE
# ================================================================================

class ExecutionResult:
    def __init__(self, success: bool, price: float, quantity: float,
                 fee: float = 0.0, txid: str = "", message: str = ""):
        self.success = success
        self.price = price
        self.quantity = quantity
        self.fee = fee
        self.txid = txid
        self.message = message

    def __repr__(self) -> str:
        return (f"ExecutionResult(success={self.success}, price={self.price:.10g}, "
                f"qty={self.quantity:.10g}, fee={self.fee:.10g}, msg={self.message!r})")


class Executor(ABC):
    """Base executor interface. Implementations must never guess a price or
    quantity — if a required upstream value is unavailable, fail closed.
    """

    @abstractmethod
    def buy(self, mint: str, price: float, quantity: float, reason: str = "") -> ExecutionResult:
        ...

    @abstractmethod
    def sell(self, mint: str, price: float, quantity: float, reason: str = "") -> ExecutionResult:
        ...


class PaperExecutor(Executor):
    """Simulated execution with configurable fee and slippage, used for
    PAPER and SIMULATION modes. No network calls that could move real funds
    are ever made from this class.
    """

    def __init__(self, fee_pct: float = 0.01, slippage_pct: float = 0.005):
        self.fee_pct = fee_pct
        self.slippage_pct = slippage_pct
        self.logger = logging.getLogger("lax.exec.paper")

    def _apply_slippage(self, price: float, side: Side) -> float:
        slip = price * self.slippage_pct
        return price + slip if side == Side.BUY else price - slip

    def buy(self, mint: str, price: float, quantity: float, reason: str = "") -> ExecutionResult:
        exec_price = self._apply_slippage(price, Side.BUY)
        fee = exec_price * quantity * self.fee_pct
        self.logger.info(f"[PAPER BUY] {truncate_addr(mint)} qty={quantity:.6g} @ {exec_price:.10g} fee={fee:.6g} ({reason})")
        return ExecutionResult(True, exec_price, quantity, fee=fee, txid=f"paper_{uuid.uuid4().hex[:12]}")

    def sell(self, mint: str, price: float, quantity: float, reason: str = "") -> ExecutionResult:
        exec_price = self._apply_slippage(price, Side.SELL)
        fee = exec_price * quantity * self.fee_pct
        self.logger.info(f"[PAPER SELL] {truncate_addr(mint)} qty={quantity:.6g} @ {exec_price:.10g} fee={fee:.6g} ({reason})")
        return ExecutionResult(True, exec_price, quantity, fee=fee, txid=f"paper_{uuid.uuid4().hex[:12]}")


class JupiterLiveExecutor(Executor):
    """LIVE executor using the Jupiter swap API.

    IMPORTANT / INTENTIONAL SAFETY BOUNDARY
    ----------------------------------------
    This class fetches a real, on-chain-accurate quote from Jupiter so the
    rest of the system (risk checks, slippage checks, sizing) operates on
    real numbers. It deliberately does NOT implement transaction signing.
    Signing requires a Solana keypair/signing library the operator must
    supply themselves in a securely-reviewed deployment; wiring an
    unattended signer into a downloadable script is a well-known vector
    for private-key compromise, so this build stops at "build & simulate
    the swap" and refuses to broadcast a signed transaction. Attempting to
    call buy()/sell() in LIVE mode returns success=False with a clear
    message rather than silently doing nothing.
    """

    def __init__(self, cfg: Config, rpc: SolanaClient):
        self.cfg = cfg
        self.rpc = rpc
        self.quote_mint = cfg.get("trading.quote_mint", KNOWN_MINTS["SOL"])
        self.slippage_bps = int(cfg.get("trading.slippage_bps", 150))
        self.priority_fee = int(cfg.get("trading.priority_fee_lamports", 20000))
        self.session = requests.Session()
        self.session.headers.update({"User-Agent": f"LaxTrader/{VERSION}"})
        self.logger = logging.getLogger("lax.exec.live")

    def _get_quote(self, input_mint: str, output_mint: str, amount: int) -> Optional[Dict[str, Any]]:
        try:
            r = self.session.get(JUPITER_QUOTE_API, params={
                "inputMint": input_mint, "outputMint": output_mint,
                "amount": amount, "slippageBps": self.slippage_bps,
            }, timeout=20)
            r.raise_for_status()
            return r.json()
        except requests.RequestException as e:
            self.logger.error(f"Jupiter quote failed: {e}")
            return None

    def buy(self, mint: str, price: float, quantity: float, reason: str = "") -> ExecutionResult:
        if price <= 0 or quantity <= 0:
            return ExecutionResult(False, price, 0, message="invalid price/quantity")
        amount_in = int(price * quantity * LAMPORTS_PER_SOL)
        quote = self._get_quote(self.quote_mint, mint, amount_in)
        if not quote:
            return ExecutionResult(False, price, 0, message="quote failed")
        out_amount = int(quote.get("outAmount", 0))
        self.logger.info(f"[LIVE QUOTE] BUY {truncate_addr(mint)} in={amount_in} lamports out={out_amount} units — {reason}")
        return ExecutionResult(False, price, 0,
                               message="signing/broadcast intentionally not implemented for safety; "
                                       "supply your own signer to complete this integration")

    def sell(self, mint: str, price: float, quantity: float, reason: str = "") -> ExecutionResult:
        if price <= 0 or quantity <= 0:
            return ExecutionResult(False, price, 0, message="invalid price/quantity")
        amount_in = int(quantity * (10 ** 6))  # placeholder decimals; real usage should fetch mint decimals
        quote = self._get_quote(mint, self.quote_mint, amount_in)
        if not quote:
            return ExecutionResult(False, price, 0, message="quote failed")
        out_amount = int(quote.get("outAmount", 0))
        self.logger.info(f"[LIVE QUOTE] SELL {truncate_addr(mint)} out={out_amount} lamports")
        return ExecutionResult(False, price, 0,
                               message="signing/broadcast intentionally not implemented for safety; "
                                       "supply your own signer to complete this integration")


class ExecutionEngine:
    """Wraps an Executor with retry logic, timeout handling, and RiskManager
    approval. This is the ONLY class allowed to call an Executor's buy/sell.
    """

    def __init__(self, cfg: Config, executor: Executor, risk: RiskManager, db: Database, mode: Mode):
        self.cfg = cfg
        self.executor = executor
        self.risk = risk
        self.db = db
        self.mode = mode
        self.logger = logging.getLogger("lax.exec.engine")

    def submit_buy(self, mint: str, symbol: str, price: float, quantity: float,
                   equity: float, current_open_positions: int, reason: str,
                   slippage_bps_estimate: Optional[float] = None) -> ExecutionResult:
        approved, why = self.risk.validate_order(
            mint, Side.BUY, quantity, price, equity, current_open_positions, slippage_bps_estimate)
        if not approved:
            self.logger.warning(f"BUY blocked by RiskManager for {symbol or truncate_addr(mint)}: {why}")
            self.db.audit("order_blocked", {"mint": mint, "side": "buy", "reason": why})
            return ExecutionResult(False, price, 0, message=f"risk_blocked: {why}")

        order = Order(side=Side.BUY, quantity=quantity, price=price)
        order_id = self.db.insert_order(mint, order, OrderStatus.PENDING, self.mode.value)
        try:
            result = self._execute_with_retry(self.executor.buy, mint, price, quantity, reason)
        except ExecutionError as e:
            self.risk.record_execution_result(False)
            self.db.execute("UPDATE orders SET status=?, updated_at=? WHERE id=?",
                            (OrderStatus.FAILED.value, now_ts(), order_id))
            return ExecutionResult(False, price, 0, message=str(e))

        self.risk.record_execution_result(result.success)
        status = OrderStatus.FILLED if result.success else OrderStatus.REJECTED
        self.db.execute("UPDATE orders SET status=?, updated_at=? WHERE id=?",
                        (status.value, now_ts(), order_id))
        if result.success:
            self.risk.mark_trade()
            fill = Fill(order_id=order_id, side=Side.BUY, quantity=result.quantity,
                       price=result.price, fee=result.fee, timestamp=now_ts(), txid=result.txid)
            self.db.insert_fill(order_id, fill)
        return result

    def submit_sell(self, mint: str, symbol: str, price: float, quantity: float,
                    equity: float, current_open_positions: int, reason: str) -> ExecutionResult:
        approved, why = self.risk.validate_order(
            mint, Side.SELL, quantity, price, equity, current_open_positions)
        if not approved:
            self.logger.warning(f"SELL blocked by RiskManager for {symbol or truncate_addr(mint)}: {why}")
            self.db.audit("order_blocked", {"mint": mint, "side": "sell", "reason": why})
            return ExecutionResult(False, price, 0, message=f"risk_blocked: {why}")

        order = Order(side=Side.SELL, quantity=quantity, price=price)
        order_id = self.db.insert_order(mint, order, OrderStatus.PENDING, self.mode.value)
        try:
            result = self._execute_with_retry(self.executor.sell, mint, price, quantity, reason)
        except ExecutionError as e:
            self.risk.record_execution_result(False)
            self.db.execute("UPDATE orders SET status=?, updated_at=? WHERE id=?",
                            (OrderStatus.FAILED.value, now_ts(), order_id))
            return ExecutionResult(False, price, 0, message=str(e))

        self.risk.record_execution_result(result.success)
        status = OrderStatus.FILLED if result.success else OrderStatus.REJECTED
        self.db.execute("UPDATE orders SET status=?, updated_at=? WHERE id=?",
                        (status.value, now_ts(), order_id))
        if result.success:
            self.risk.mark_trade()
            fill = Fill(order_id=order_id, side=Side.SELL, quantity=result.quantity,
                       price=result.price, fee=result.fee, timestamp=now_ts(), txid=result.txid)
            self.db.insert_fill(order_id, fill)
        return result

    def _execute_with_retry(self, fn: Callable, mint: str, price: float, quantity: float,
                            reason: str, retries: int = 2) -> ExecutionResult:
        last_exc: Optional[Exception] = None
        for attempt in range(1, retries + 2):
            try:
                return fn(mint, price, quantity, reason)
            except Exception as e:  # noqa: BLE001
                last_exc = e
                self.logger.debug(f"execution attempt {attempt} failed: {e}")
                time.sleep(0.5 * attempt)
        raise ExecutionError(f"execution failed after retries: {last_exc}")


# ================================================================================
#  NOTIFICATION MANAGER
# ================================================================================

class NotificationManager:
    """Sends alerts to Discord webhooks and/or a Telegram bot. Never includes
    secrets in any outgoing payload.
    """

    LEVEL_COLORS = {
        "info": 0x5DA9FF, "success": 0x14F195, "warning": 0xFFB020,
        "error": 0xFF4D6D, "trade": 0x9945FF, "critical": 0xFF0033,
    }

    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.discord_webhook = cfg.get("notifications.discord_webhook", "")
        self.tg_token = cfg.get("notifications.telegram_bot_token", "")
        self.tg_chat = cfg.get("notifications.telegram_chat_id", "")
        self.session = requests.Session()
        self.session.headers.update({"User-Agent": f"LaxTrader/{VERSION}"})
        self.logger = logging.getLogger("lax.notify")
        self._queue: "queue.Queue[Tuple[str, str, str]]" = queue.Queue()
        self._worker: Optional[threading.Thread] = None
        self._running = False

    def start(self) -> None:
        if self._running:
            return
        self._running = True
        self._worker = threading.Thread(target=self._worker_loop, daemon=True)
        self._worker.start()

    def stop(self) -> None:
        self._running = False

    def _worker_loop(self) -> None:
        while self._running:
            try:
                title, body, level = self._queue.get(timeout=1.0)
            except queue.Empty:
                continue
            self._send_now(title, body, level)

    def send(self, title: str, body: str, level: str = "info") -> None:
        """Non-blocking send — queues the notification for the worker thread."""
        self._queue.put((title, body, level))

    def _send_now(self, title: str, body: str, level: str) -> None:
        if self.discord_webhook:
            try:
                self.session.post(self.discord_webhook, json={
                    "username": "LAX Trader",
                    "embeds": [{
                        "title": title, "description": body,
                        "color": self.LEVEL_COLORS.get(level, 0x9945FF),
                        "footer": {"text": f"{APP_NAME} v{VERSION}"},
                        "timestamp": utc_now_iso(),
                    }],
                }, timeout=10)
            except requests.RequestException as e:
                self.logger.debug(f"discord notify failed: {e}")
        if self.tg_token and self.tg_chat:
            try:
                self.session.post(
                    f"https://api.telegram.org/bot{self.tg_token}/sendMessage",
                    json={"chat_id": self.tg_chat, "text": f"*{title}*\n\n{body}",
                          "parse_mode": "Markdown", "disable_web_page_preview": True},
                    timeout=10,
                )
            except requests.RequestException as e:
                self.logger.debug(f"telegram notify failed: {e}")

    def trade(self, side: str, symbol: str, mint: str, price: float, quantity: float, reason: str) -> None:
        emoji = "\U0001F7E2" if side.lower() == "buy" else "\U0001F534"
        self.send(
            f"{emoji} {side.upper()} {symbol or truncate_addr(mint)}",
            f"Mint: `{truncate_addr(mint)}`\nPrice: `{price:.10g}`\nQty: `{quantity:.6g}`\nReason: {reason}",
            level="trade",
        )

    def scan_hit(self, token: TokenInfo, score: float) -> None:
        self.send(
            f"\U0001F50E New qualified candidate: {token.symbol or truncate_addr(token.mint)}",
            f"Liquidity: {fmt_usd(token.liquidity_usd)}\nMCap: {fmt_usd(token.market_cap_usd)}\n"
            f"Score: {score:.1f}/100",
            level="info",
        )

    def error(self, message: str) -> None:
        self.send("\u26A0\uFE0F Trader Error", f"```{message}```", level="error")

    def critical(self, message: str) -> None:
        self.send("\U0001F6A8 CRITICAL", f"```{message}```", level="critical")


# ================================================================================
#  BACKTEST ENGINE
# ================================================================================

class BacktestEngine:
    """Bar-by-bar backtester. Strategies only ever see closed candles up to
    and including the current bar at decision time — future bars are never
    peeked at, which avoids look-ahead bias. Fees and slippage are modeled
    symmetrically with the paper executor so backtest and paper-trading
    results are directly comparable.
    """

    def __init__(self, strategy: Strategy, starting_balance: float,
                 fee_pct: float = 0.01, slippage_pct: float = 0.005,
                 stop_loss_pct: float = 12.0, take_profit_pct: float = 35.0,
                 trailing_stop_pct: Optional[float] = None,
                 warmup_bars: int = 30):
        self.strategy = strategy
        self.starting_balance = starting_balance
        self.fee_pct = fee_pct
        self.slippage_pct = slippage_pct
        self.stop_loss_pct = stop_loss_pct
        self.take_profit_pct = take_profit_pct
        self.trailing_stop_pct = trailing_stop_pct
        self.warmup_bars = warmup_bars
        self.trades: List[Trade] = []
        self.equity_curve: List[EquityPoint] = []
        self.total_slippage_cost = 0.0
        self.total_fees_paid = 0.0

    def _exec_price(self, price: float, side: Side) -> float:
        slip = price * self.slippage_pct
        return price + slip if side == Side.BUY else price - slip

    def run(self, candles: List[Candle]) -> BacktestReport:
        if len(candles) < self.warmup_bars + 2:
            raise BacktestDataError(f"need at least {self.warmup_bars + 2} candles, got {len(candles)}")

        portfolio_cash = self.starting_balance
        quantity = 0.0
        entry_price: Optional[float] = None
        entry_time: Optional[int] = None
        stop_loss: Optional[float] = None
        take_profit: Optional[float] = None
        trailing_high: Optional[float] = None
        trailing_stop: Optional[float] = None

        self.trades.clear()
        self.equity_curve.clear()
        self.total_slippage_cost = 0.0
        self.total_fees_paid = 0.0

        for i, candle in enumerate(candles):
            # Strategy only sees data up to and including `candle` — no lookahead.
            self.strategy.update(candle)
            price = candle.close
            equity = portfolio_cash + quantity * price
            self.equity_curve.append(EquityPoint(
                timestamp=candle.timestamp, equity=equity, cash=portfolio_cash,
                position_value=quantity * price,
            ))

            if quantity > 0:
                if self.trailing_stop_pct and price > (trailing_high or 0):
                    trailing_high = price
                    trailing_stop = price * (1 - self.trailing_stop_pct / 100.0)

                exit_reason = None
                if stop_loss and price <= stop_loss:
                    exit_reason = "stop_loss"
                elif take_profit and price >= take_profit:
                    exit_reason = "take_profit"
                elif trailing_stop and price <= trailing_stop:
                    exit_reason = "trailing_stop"

                if exit_reason:
                    exec_price = self._exec_price(price, Side.SELL)
                    fee = exec_price * quantity * self.fee_pct
                    slip_cost = abs(price - exec_price) * quantity
                    pnl = (exec_price - entry_price) * quantity - fee
                    pnl_pct = pct_change(entry_price, exec_price)
                    portfolio_cash += exec_price * quantity - fee
                    self.total_fees_paid += fee
                    self.total_slippage_cost += slip_cost
                    self.trades.append(Trade(
                        symbol="BACKTEST", mint="BACKTEST", side=Side.BUY,
                        entry_price=entry_price, exit_price=exec_price, quantity=quantity,
                        entry_time=entry_time, exit_time=candle.timestamp,
                        pnl=pnl, pnl_pct=pnl_pct, fees=fee, reason=exit_reason,
                    ))
                    quantity = 0.0
                    entry_price = None
                    entry_time = None
                    stop_loss = take_profit = trailing_high = trailing_stop = None
                    continue

            if i < self.warmup_bars:
                continue

            sig, reason = self.strategy.signal()

            if sig in (TradeSignal.BUY, TradeSignal.STRONG_BUY) and quantity == 0:
                budget = portfolio_cash * 0.95
                qty = safe_div(budget, price)
                if qty > 0:
                    exec_price = self._exec_price(price, Side.BUY)
                    fee = exec_price * qty * self.fee_pct
                    slip_cost = abs(price - exec_price) * qty
                    cost = exec_price * qty + fee
                    if cost <= portfolio_cash:
                        portfolio_cash -= cost
                        quantity = qty
                        entry_price = exec_price
                        entry_time = candle.timestamp
                        stop_loss = exec_price * (1 - self.stop_loss_pct / 100.0)
                        take_profit = exec_price * (1 + self.take_profit_pct / 100.0)
                        trailing_high = exec_price
                        trailing_stop = exec_price * (1 - (self.trailing_stop_pct or 100) / 100.0)
                        self.total_fees_paid += fee
                        self.total_slippage_cost += slip_cost
            elif sig in (TradeSignal.SELL, TradeSignal.STRONG_SELL) and quantity > 0:
                exec_price = self._exec_price(price, Side.SELL)
                fee = exec_price * quantity * self.fee_pct
                slip_cost = abs(price - exec_price) * quantity
                pnl = (exec_price - entry_price) * quantity - fee
                pnl_pct = pct_change(entry_price, exec_price)
                portfolio_cash += exec_price * quantity - fee
                self.total_fees_paid += fee
                self.total_slippage_cost += slip_cost
                self.trades.append(Trade(
                    symbol="BACKTEST", mint="BACKTEST", side=Side.BUY,
                    entry_price=entry_price, exit_price=exec_price, quantity=quantity,
                    entry_time=entry_time, exit_time=candle.timestamp,
                    pnl=pnl, pnl_pct=pnl_pct, fees=fee, reason="signal",
                ))
                quantity = 0.0
                entry_price = None
                entry_time = None
                stop_loss = take_profit = trailing_high = trailing_stop = None

        # Force-close any open position at the final bar for a clean report.
        if quantity > 0 and candles:
            last = candles[-1]
            exec_price = self._exec_price(last.close, Side.SELL)
            fee = exec_price * quantity * self.fee_pct
            pnl = (exec_price - entry_price) * quantity - fee
            pnl_pct = pct_change(entry_price, exec_price)
            portfolio_cash += exec_price * quantity - fee
            self.total_fees_paid += fee
            self.trades.append(Trade(
                symbol="BACKTEST", mint="BACKTEST", side=Side.BUY,
                entry_price=entry_price, exit_price=exec_price, quantity=quantity,
                entry_time=entry_time, exit_time=last.timestamp,
                pnl=pnl, pnl_pct=pnl_pct, fees=fee, reason="end_of_data",
            ))

        return self._build_report()

    def _build_report(self) -> BacktestReport:
        if not self.equity_curve:
            raise BacktestDataError("no equity curve produced")

        start_eq = self.starting_balance
        end_eq = self.equity_curve[-1].equity
        peak = max(p.equity for p in self.equity_curve)
        trough = min(p.equity for p in self.equity_curve)

        max_dd = 0.0
        run_peak = self.equity_curve[0].equity
        for p in self.equity_curve:
            run_peak = max(run_peak, p.equity)
            dd = safe_div(run_peak - p.equity, run_peak) * 100
            max_dd = max(max_dd, dd)

        wins = [t for t in self.trades if t.pnl > 0]
        losses = [t for t in self.trades if t.pnl <= 0]
        gross_win = sum(t.pnl for t in wins)
        gross_loss = abs(sum(t.pnl for t in losses))
        profit_factor = safe_div(gross_win, gross_loss)
        win_rate = safe_div(len(wins), len(self.trades)) * 100 if self.trades else 0.0
        avg_win = safe_div(gross_win, len(wins))
        avg_loss = safe_div(gross_loss, len(losses))
        # Expectancy: average $ won/lost per trade, accounting for win rate
        expectancy = (win_rate / 100.0) * avg_win - (1 - win_rate / 100.0) * avg_loss

        returns = []
        downside_returns = []
        for i in range(1, len(self.equity_curve)):
            prev = self.equity_curve[i - 1].equity
            cur = self.equity_curve[i].equity
            if prev > 0:
                r = (cur - prev) / prev
                returns.append(r)
                if r < 0:
                    downside_returns.append(r)

        sharpe = 0.0
        sortino = 0.0
        if len(returns) > 1:
            mean_r = statistics.mean(returns)
            std_r = statistics.stdev(returns)
            periods_per_year = 365 * 24 * 60  # assume ~1-minute bars; caller may rescale externally
            sharpe = safe_div(mean_r, std_r) * math.sqrt(periods_per_year) if std_r else 0.0
            if len(downside_returns) > 1:
                downside_std = statistics.stdev(downside_returns)
                sortino = safe_div(mean_r, downside_std) * math.sqrt(periods_per_year) if downside_std else 0.0
            elif downside_returns:
                sortino = float("inf") if mean_r > 0 else 0.0

        return BacktestReport(
            starting_balance=start_eq,
            ending_balance=end_eq,
            net_pnl=end_eq - start_eq,
            net_pnl_pct=pct_change(start_eq, end_eq),
            total_trades=len(self.trades),
            wins=len(wins),
            losses=len(losses),
            win_rate=win_rate,
            avg_win=avg_win,
            avg_loss=avg_loss,
            profit_factor=profit_factor,
            expectancy=expectancy,
            max_drawdown_pct=max_dd,
            peak_equity=peak,
            trough_equity=trough,
            sharpe=sharpe,
            sortino=sortino,
            fees_paid=self.total_fees_paid,
            slippage_cost=self.total_slippage_cost,
        )


# ================================================================================
#  PERFORMANCE ANALYZER
# ================================================================================

class PerformanceAnalyzer:
    """Computes and formats performance statistics from the persistent
    database, independent of any live engine state.
    """

    def __init__(self, db: Database):
        self.db = db

    def summary(self, mode: Optional[str] = None) -> Dict[str, Any]:
        stats = self.db.stats(mode=mode)
        curve = self.db.equity_curve()
        max_dd = 0.0
        if curve:
            run_peak = curve[0]["equity"]
            for row in curve:
                run_peak = max(run_peak, row["equity"])
                dd = safe_div(run_peak - row["equity"], run_peak) * 100
                max_dd = max(max_dd, dd)
        stats["max_drawdown_pct"] = max_dd
        stats["equity_points"] = len(curve)
        return stats

    def by_mint(self, top_n: int = 10) -> List[Dict[str, Any]]:
        rows = self.db.fetchall("""
            SELECT mint, symbol, COUNT(*) as trades, SUM(pnl) as pnl,
                   AVG(pnl_pct) as avg_pnl_pct
            FROM trades GROUP BY mint ORDER BY pnl DESC LIMIT ?
        """, (top_n,))
        return [dict(r) for r in rows]

    def recent_trades(self, limit: int = 20) -> List[Dict[str, Any]]:
        rows = self.db.fetchall("SELECT * FROM trades ORDER BY exit_time DESC LIMIT ?", (limit,))
        return [dict(r) for r in rows]

    def render_text_report(self, mode: Optional[str] = None) -> str:
        s = self.summary(mode=mode)
        if not s or s.get("total_trades", 0) == 0:
            return "No trades recorded yet."
        lines = [
            f"Total trades      : {s['total_trades']}",
            f"Wins / Losses     : {s['wins']} / {s['losses']}",
            f"Win rate          : {s['win_rate']:.2f}%",
            f"Total PnL         : {s['total_pnl']:+.6f}",
            f"Gross win/loss    : {s['gross_win']:.6f} / {s['gross_loss']:.6f}",
            f"Profit factor     : {s['profit_factor']:.2f}",
            f"Best / Worst trade: {s['best']:+.6f} / {s['worst']:+.6f}",
            f"Fees paid         : {s['fees']:.6f}",
            f"Max drawdown      : {s['max_drawdown_pct']:.2f}%",
        ]
        return "\n".join(lines)


# ================================================================================
#  LIVE-MODE CONFIRMATION GATE
# ================================================================================

def assert_live_mode_confirmed(cfg: Config, cli_flag_present: bool) -> None:
    """Live trading must clear THREE independent gates before a single
    order can ever reach an Executor:

      1. The CLI was invoked with --i-understand-the-risk
      2. The config explicitly sets live_confirmation.config_flag_enabled = true
      3. The environment variable named in live_confirmation.required_env_var
         is set to exactly live_confirmation.required_env_value

    Any missing gate raises LiveTradingNotConfirmedError and the process
    must not proceed into live trading.
    """
    if not cli_flag_present:
        raise LiveTradingNotConfirmedError(
            "Live mode requires the --i-understand-the-risk CLI flag."
        )
    if not bool(cfg.get("live_confirmation.config_flag_enabled", False)):
        raise LiveTradingNotConfirmedError(
            "Live mode requires 'live_confirmation.config_flag_enabled: true' in your config file. "
            "This is not enabled by default."
        )
    env_var = cfg.get("live_confirmation.required_env_var", "LAX_LIVE_CONFIRM")
    expected = cfg.get("live_confirmation.required_env_value", "I_UNDERSTAND_THE_RISK")
    actual = os.environ.get(env_var, "")
    if actual != expected:
        raise LiveTradingNotConfirmedError(
            f"Live mode requires environment variable {env_var}={expected!r} to be set exactly."
        )
    if not cfg.get_private_key():
        raise LiveTradingNotConfirmedError(
            f"No private key found in environment variable "
            f"'{cfg.get('wallet.private_key_env', 'LAX_PRIVATE_KEY')}'."
        )


# ================================================================================
#  LOCAL STATUS DASHBOARD (dependency-free HTTP server)
# ================================================================================

class _DashboardState:
    """Thread-safe shared state the dashboard HTTP handler reads from."""
    def __init__(self):
        self.lock = threading.Lock()
        self.payload: Dict[str, Any] = {}

    def update(self, payload: Dict[str, Any]) -> None:
        with self.lock:
            self.payload = payload

    def get(self) -> Dict[str, Any]:
        with self.lock:
            return dict(self.payload)


class _DashboardHandler(http.server.BaseHTTPRequestHandler):
    state: _DashboardState = None  # type: ignore  # set by DashboardServer

    def log_message(self, fmt: str, *args) -> None:  # silence default access logs
        logging.getLogger("lax.dashboard").debug(fmt % args)

    def do_GET(self) -> None:
        if self.path in ("/", "/status"):
            self._send_json(self.state.get())
        elif self.path == "/health":
            self._send_json({"status": "ok", "time": utc_now_iso()})
        else:
            self.send_response(404)
            self.end_headers()

    def _send_json(self, obj: Dict[str, Any]) -> None:
        body = json.dumps(obj, indent=2, default=str).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


class DashboardServer:
    """A minimal, dependency-free HTTP status endpoint (GET /status) so the
    bot's state can be inspected from a browser or curl without exposing any
    control surface (this server is strictly read-only).
    """

    def __init__(self, host: str = "127.0.0.1", port: int = 8787):
        self.host = host
        self.port = port
        self.state = _DashboardState()
        self._httpd: Optional[socketserver.TCPServer] = None
        self._thread: Optional[threading.Thread] = None
        self.logger = logging.getLogger("lax.dashboard")

    def update(self, payload: Dict[str, Any]) -> None:
        self.state.update(payload)

    def start(self) -> None:
        handler_cls = type("BoundHandler", (_DashboardHandler,), {"state": self.state})
        try:
            self._httpd = socketserver.TCPServer((self.host, self.port), handler_cls)
        except OSError as e:
            self.logger.warning(f"dashboard failed to bind {self.host}:{self.port}: {e}")
            return
        self._thread = threading.Thread(target=self._httpd.serve_forever, daemon=True)
        self._thread.start()
        self.logger.info(f"Dashboard listening on http://{self.host}:{self.port}/status")

    def stop(self) -> None:
        if self._httpd:
            self._httpd.shutdown()
            self._httpd.server_close()


# ================================================================================
#  TRADING BOT  (main orchestrator)
# ================================================================================

class TradingBot:
    """Wires every subsystem together and runs the scan -> analyze -> signal
    -> risk -> execute loop for PAPER, SIMULATION, and LIVE modes.

    PAPER and SIMULATION behave identically except SIMULATION additionally
    disables all outbound notifications (useful for quick local dry runs).
    LIVE requires assert_live_mode_confirmed() to have already passed.
    """

    def __init__(self, cfg: Config, mode: Mode):
        self.cfg = cfg
        self.mode = mode
        self.logger = logging.getLogger("lax.bot")

        problems = cfg.validate()
        if problems:
            raise ConfigError("Invalid configuration: " + "; ".join(problems))

        self.db = Database(Path(cfg.get("database.path", str(DB_FILE))))
        self.rpc = SolanaClient(cfg)
        self.market = MarketData(cfg)
        self.scanner = TokenScanner(cfg, self.market)
        self.security = TokenSecurityAnalyzer(cfg, self.rpc, self.market)
        self.liquidity = LiquidityAnalyzer(cfg, self.market)
        self.wallets = WalletAnalyzer(cfg, self.rpc)
        self.signal_engine = SignalEngine(cfg)
        self.risk = RiskManager(cfg)
        self.sizer = PositionSizer(cfg)
        self.notifier = NotificationManager(cfg)
        self.notifier.start()

        starting_balance = float(cfg.get("trading.starting_balance_quote", 1.0))
        self.portfolio = Portfolio(starting_balance)
        self.quote_mint = cfg.get("trading.quote_mint", KNOWN_MINTS["SOL"])

        if mode in (Mode.PAPER, Mode.SIMULATION):
            self.executor: Executor = PaperExecutor()
        elif mode == Mode.LIVE:
            self.executor = JupiterLiveExecutor(cfg, self.rpc)
        else:
            raise ConfigError(f"TradingBot cannot be constructed directly for mode={mode}")

        self.exec_engine = ExecutionEngine(cfg, self.executor, self.risk, self.db, mode)

        # One strategy instance per tracked mint so histories don't bleed
        # across unrelated tokens.
        self._strategies: Dict[str, Strategy] = {}
        self._last_equity_write = 0.0
        self._last_scan = 0.0
        self.running = False

        dash_cfg = cfg.get("dashboard", {})
        self.dashboard: Optional[DashboardServer] = None
        if dash_cfg.get("enabled"):
            self.dashboard = DashboardServer(dash_cfg.get("host", "127.0.0.1"), int(dash_cfg.get("port", 8787)))

    # ─── Strategy management ────────────────────────────────────────────────

    def _get_strategy(self, mint: str) -> Strategy:
        if mint not in self._strategies:
            self._strategies[mint] = build_strategy(
                self.cfg.get("strategy.name", "composite"), self.cfg.get("strategy.params", {}))
        return self._strategies[mint]

    # ─── Core per-token pipeline ─────────────────────────────────────────────

    def analyze_token(self, mint: str) -> Optional[ScanCandidate]:
        """Full pipeline for a single mint: fetch token info, run security +
        liquidity analysis, and return an updated ScanCandidate (or None if
        market data could not be retrieved at all).
        """
        token = self.market.build_token_info(mint)
        if token is None:
            return None
        try:
            sec_report = self.security.analyze(token)
        except Exception as e:
            self.logger.warning(f"security analysis failed for {truncate_addr(mint)}: {e}")
            sec_report = SecurityReport(mint=mint, risk_score=0.0, risk_level=RiskLevel.CRITICAL, passed=False)
            sec_report.add("ANALYSIS_ERROR", RiskLevel.CRITICAL, str(e))
        liq_report = self.liquidity.analyze(token)

        candidate = ScanCandidate(token=token, security=sec_report, liquidity=liq_report)
        candidate.score = 0.6 * (100 if sec_report.passed else 0) + 0.4 * sec_report.risk_score
        self.db.insert_scan(mint, token.symbol, "analyzed", token.liquidity_usd, sec_report.risk_score)
        return candidate

    def evaluate_and_maybe_trade(self, mint: str, candidate: Optional[ScanCandidate] = None) -> Optional[FusedSignal]:
        """Runs strategy + fusion + risk + (possibly) execution for one mint."""
        token_info = candidate.token if candidate else self.market.build_token_info(mint)
        if token_info is None or token_info.price_usd <= 0:
            return None

        candle_price = self.market.poll_and_update_candles(mint)
        strategy = self._get_strategy(mint)
        # candle price already updates the builder; feed the strategy from
        # the builder's closed candles so indicator windows are consistent.
        candles = self.market.get_candles(mint)
        if candles:
            latest = candles[-1]
            if not strategy.closes or strategy.closes[-1] != latest.close:
                strategy.update(latest)

        if len(strategy.closes) < 10:
            return None

        raw_signal, reason = strategy.signal()
        intended_size_usd = self.sizer.compute(
            equity=self.portfolio.equity({mint: token_info.price_usd}),
            price=token_info.price_usd,
            security_score=candidate.security.risk_score if candidate and candidate.security else None,
        ) * token_info.price_usd

        fused = self.signal_engine.fuse(
            mint, raw_signal, reason,
            security=candidate.security if candidate else None,
            liquidity=candidate.liquidity if candidate else None,
            intended_size_usd=intended_size_usd,
        )
        self.db.insert_signal(mint, strategy.name, raw_signal, fused.decision, fused.score, token_info.price_usd, reason)

        if self.cfg.get("notifications.notify_on_signal") and fused.decision != Decision.HOLD:
            self.notifier.send(f"Signal: {fused.decision.value.upper()} {token_info.symbol or truncate_addr(mint)}",
                              "; ".join(fused.reasons), level="info")

        self._act_on_signal(mint, token_info, fused)
        return fused

    def _act_on_signal(self, mint: str, token: TokenInfo, fused: FusedSignal) -> None:
        prices = {mint: token.price_usd}
        equity = self.portfolio.equity(prices)
        self.risk.update_equity(equity)

        # Global protective checks run BEFORE any new-entry logic, and can
        # force an exit even without a fresh SELL signal.
        if self.risk.max_drawdown_breached(equity) or self.risk.daily_loss_breached(equity):
            if self.portfolio.has_position(mint):
                self._close_position(mint, token, "risk_limit_breached")
            return

        pos = self.portfolio.get_position(mint)
        if pos:
            if self.cfg.get("risk.use_trailing_stop"):
                pos.update_trailing(token.price_usd, float(self.cfg.get("risk.trailing_stop_pct", 10.0)))
            if pos.stop_loss and token.price_usd <= pos.stop_loss:
                self._close_position(mint, token, "stop_loss")
                return
            if pos.take_profit and token.price_usd >= pos.take_profit:
                self._close_position(mint, token, "take_profit")
                return
            if pos.trailing_stop and token.price_usd <= pos.trailing_stop:
                self._close_position(mint, token, "trailing_stop")
                return

        if fused.decision == Decision.BUY and not self.portfolio.has_position(mint):
            self._open_position(mint, token, fused)
        elif fused.decision == Decision.SELL and self.portfolio.has_position(mint):
            self._close_position(mint, token, "signal:" + fused.strategy_reason)

    def _open_position(self, mint: str, token: TokenInfo, fused: FusedSignal) -> None:
        equity = self.portfolio.equity({mint: token.price_usd})
        qty = self.sizer.compute(equity, token.price_usd, security_score=fused.security_score)
        if qty <= 0:
            return
        slip_bps = self.liquidity.estimate_slippage_bps(token, qty * token.price_usd)
        result = self.exec_engine.submit_buy(
            mint, token.symbol, token.price_usd, qty, equity,
            self.portfolio.open_position_count(), "; ".join(fused.reasons),
            slippage_bps_estimate=slip_bps,
        )
        if not result.success:
            self.logger.info(f"buy not executed for {token.symbol or truncate_addr(mint)}: {result.message}")
            return
        sl, tp = self.risk.compute_stops(result.price)
        self.portfolio.open_position(mint, token.symbol, result.price, result.quantity, sl, tp)
        self.portfolio.total_fees += result.fee
        if self.cfg.get("notifications.notify_on_trade"):
            self.notifier.trade("buy", token.symbol, mint, result.price, result.quantity, fused.strategy_reason)
        self.logger.info(f"BUY {token.symbol or truncate_addr(mint)} qty={result.quantity:.6g} @ {result.price:.10g}")

    def _close_position(self, mint: str, token: TokenInfo, reason: str) -> None:
        pos = self.portfolio.get_position(mint)
        if not pos:
            return
        equity = self.portfolio.equity({mint: token.price_usd})
        result = self.exec_engine.submit_sell(
            mint, pos.symbol, token.price_usd, pos.quantity, equity, self.portfolio.open_position_count(), reason)
        if not result.success:
            self.logger.info(f"sell not executed for {pos.symbol or truncate_addr(mint)}: {result.message}")
            return
        qty, pnl, pnl_pct = self.portfolio.close_position(mint, result.price)
        self.portfolio.total_fees += result.fee
        trade = Trade(
            symbol=pos.symbol, mint=mint, side=Side.BUY,
            entry_price=pos.entry_price, exit_price=result.price, quantity=qty,
            entry_time=pos.entry_time, exit_time=now_ts(),
            pnl=pnl, pnl_pct=pnl_pct, fees=result.fee, reason=reason,
        )
        self.db.insert_trade(trade, self.mode.value)
        if self.cfg.get("notifications.notify_on_trade"):
            self.notifier.trade("sell", pos.symbol, mint, result.price, qty,
                               f"{reason} PnL={pnl:+.6f} ({pnl_pct:+.2f}%)")
        self.logger.info(f"SELL {pos.symbol or truncate_addr(mint)} qty={qty:.6g} @ {result.price:.10g} PnL={pnl:+.6f}")

    # ─── Scan loop ───────────────────────────────────────────────────────────

    def run_scan_cycle(self) -> List[ScanCandidate]:
        new_candidates = self.scanner.scan_once()
        qualified: List[ScanCandidate] = []
        for cand in new_candidates:
            full = self.analyze_token(cand.token.mint)
            if full is None:
                continue
            if full.security and full.security.passed:
                self.scanner.mark_qualified(full.token.mint, full.score)
                qualified.append(full)
                if self.cfg.get("notifications.notify_on_scan_hit"):
                    self.notifier.scan_hit(full.token, full.score)
            else:
                reason = full.security.summary() if full.security else "unknown"
                self.scanner.mark_rejected(full.token.mint, reason)
        return qualified

    # ─── Main loop ───────────────────────────────────────────────────────────

    def _tracked_mints(self) -> List[str]:
        mints = set(self.portfolio.positions.keys())
        for cand in self.scanner.get_watchlist():
            mints.add(cand.token.mint)
        if LAX_MINT:
            mints.add(LAX_MINT)
        return list(mints)

    def _tick(self) -> None:
        if bool(self.cfg.get("scanner.enabled", True)):
            interval = float(self.cfg.get("scanner.poll_interval_seconds", 15))
            if time.time() - self._last_scan >= interval:
                self._last_scan = time.time()
                try:
                    self.run_scan_cycle()
                except Exception as e:
                    self.logger.exception(f"scan cycle error: {e}")
                    if self.cfg.get("notifications.notify_on_error"):
                        self.notifier.error(f"scan cycle error: {e}")

        for mint in self._tracked_mints():
            try:
                candidate = None
                if self.portfolio.has_position(mint) or mint in [c.token.mint for c in self.scanner.get_watchlist()]:
                    candidate = self.analyze_token(mint)
                self.evaluate_and_maybe_trade(mint, candidate)
            except (MarketDataError, RpcError) as e:
                self.logger.debug(f"data error for {truncate_addr(mint)}: {e}")
            except Exception as e:
                self.logger.exception(f"tick error for {truncate_addr(mint)}: {e}")
                if self.cfg.get("notifications.notify_on_error"):
                    self.notifier.error(f"tick error for {truncate_addr(mint)}: {e}")

        if time.time() - self._last_equity_write > 30:
            self._last_equity_write = time.time()
            prices = {m: (self.market.get_price_usd(m) or 0) for m in self.portfolio.positions.keys()}
            equity = self.portfolio.equity(prices)
            self.db.insert_equity(EquityPoint(
                timestamp=now_ts(), equity=equity, cash=self.portfolio.cash,
                position_value=equity - self.portfolio.cash,
            ))
            if self.dashboard:
                self.dashboard.update(self.status_snapshot())

    def status_snapshot(self) -> Dict[str, Any]:
        prices = {m: (self.market.get_price_usd(m) or 0) for m in self.portfolio.positions.keys()}
        return {
            "app": APP_NAME,
            "version": VERSION,
            "mode": self.mode.value,
            "time": utc_now_iso(),
            "portfolio": self.portfolio.snapshot(prices),
            "watchlist_size": len(self.scanner.get_watchlist()),
            "circuit_breaker": self.risk.breaker.state.value,
            "emergency_stop": self.risk.emergency_stop_active(),
            "stats": self.db.stats(mode=self.mode.value),
        }

    def run(self) -> None:
        self.running = True
        interval = int(self.cfg.get("monitor.interval_seconds", 15))
        self.logger.info(f"{APP_NAME} v{VERSION} starting in {self.mode.value.upper()} mode")
        self.logger.info(f"Strategy: {self.cfg.get('strategy.name')}  Interval: {interval}s")
        self.db.audit("engine_start", {"mode": self.mode.value})

        if self.dashboard:
            self.dashboard.start()

        self.notifier.send(
            f"\U0001F680 {APP_NAME} started",
            f"Mode: `{self.mode.value}`\nStrategy: `{self.cfg.get('strategy.name')}`\n"
            f"Starting balance: `{self.cfg.get('trading.starting_balance_quote')}`",
            level="success",
        )

        try:
            while self.running:
                try:
                    self._tick()
                except Exception as e:
                    self.logger.exception(f"main loop error: {e}")
                    if self.cfg.get("notifications.notify_on_error"):
                        self.notifier.error(str(e))
                time.sleep(interval)
        except KeyboardInterrupt:
            self.logger.info("Stopped by user (Ctrl+C)")
        finally:
            self.running = False
            self._shutdown()

    def stop(self) -> None:
        self.running = False

    def _shutdown(self) -> None:
        self.logger.info("Shutting down...")
        # Safety: in paper/simulation, flatten any open positions so the
        # session's stats reflect a clean close rather than a stranded
        # "open" position with no further price updates.
        if self.mode in (Mode.PAPER, Mode.SIMULATION):
            for mint in list(self.portfolio.positions.keys()):
                price = self.market.get_price_usd(mint)
                if price:
                    token = TokenInfo(mint=mint, price_usd=price)
                    self._close_position(mint, token, "shutdown")

        stats = self.db.stats(mode=self.mode.value)
        self.db.audit("engine_stop", stats)
        self.logger.info(f"Session stats: {stats}")
        self.notifier.send(
            f"\U0001F6D1 {APP_NAME} stopped",
            f"Trades: {stats.get('total_trades', 0)}\nPnL: {stats.get('total_pnl', 0):+.6f}\n"
            f"Win rate: {stats.get('win_rate', 0):.1f}%",
            level="info",
        )
        time.sleep(0.3)  # give the notifier worker a moment to flush
        self.notifier.stop()
        if self.dashboard:
            self.dashboard.stop()
        self.db.close()


# ================================================================================
#  TERMINAL UI HELPERS
# ================================================================================

def print_banner() -> None:
    print()
    print(f"{C.BMAGENTA}{C.BOLD}  +============================================================+{C.RESET}")
    print(f"{C.BMAGENTA}{C.BOLD}  |{C.RESET}  {C.BOLD}LAXIRONIX TRADING BOT{C.RESET}  {C.DIM}v{VERSION}{C.RESET}" + " " * 26 + f"{C.BMAGENTA}{C.BOLD}|{C.RESET}")
    print(f"{C.BMAGENTA}{C.BOLD}  |{C.RESET}  {C.DIM}Algorithmic memecoin trading for Solana{C.RESET}" + " " * 19 + f"{C.BMAGENTA}{C.BOLD}|{C.RESET}")
    print(f"{C.BMAGENTA}{C.BOLD}  +============================================================+{C.RESET}")
    print()


def print_risk_warning() -> None:
    print(f"  {C.BYELLOW}{C.BOLD}WARNING{C.RESET}  Memecoin trading is extremely high risk. You can lose")
    print(f"          all of your funds. This software does not guarantee profit")
    print(f"          and is provided for educational purposes only.")
    print()


def info(msg: str) -> None:
    print(f"  {C.BCYAN}i{C.RESET}  {msg}")


def ok(msg: str) -> None:
    print(f"  {C.BGREEN}OK{C.RESET}  {msg}")


def error(msg: str) -> None:
    print(f"  {C.BRED}X{C.RESET}  {msg}")


def warning(msg: str) -> None:
    print(f"  {C.BYELLOW}!{C.RESET}  {msg}")


def print_table(headers: List[str], rows: List[List[str]]) -> None:
    widths = [len(h) for h in headers]
    for row in rows:
        for i, cell in enumerate(row):
            widths[i] = max(widths[i], len(str(cell)))
    header_line = "  ".join(h.ljust(widths[i]) for i, h in enumerate(headers))
    print(f"  {C.BCYAN}{header_line}{C.RESET}")
    print(f"  {C.DIM}{'-' * len(header_line)}{C.RESET}")
    for row in rows:
        print("  " + "  ".join(str(c).ljust(widths[i]) for i, c in enumerate(row)))


# ================================================================================
#  CLI COMMANDS
# ================================================================================

def _load_config(args: argparse.Namespace) -> Config:
    path = Path(args.config) if getattr(args, "config", None) else CONFIG_FILE
    cfg = Config(path=path)
    setup_logging(cfg)
    return cfg


def cmd_paper(args: argparse.Namespace) -> int:
    print_banner()
    print_risk_warning()
    cfg = _load_config(args)
    cfg.set("mode", "paper")
    if args.strategy:
        cfg.set("strategy.name", args.strategy)
    if args.interval:
        cfg.set("monitor.interval_seconds", args.interval)
    bot = TradingBot(cfg, Mode.PAPER)
    bot.run()
    return 0


def cmd_simulation(args: argparse.Namespace) -> int:
    print_banner()
    cfg = _load_config(args)
    cfg.set("mode", "simulation")
    cfg.set("notifications.notify_on_trade", False, persist=False)
    cfg.set("notifications.notify_on_signal", False, persist=False)
    cfg.set("notifications.notify_on_scan_hit", False, persist=False)
    if args.strategy:
        cfg.set("strategy.name", args.strategy)
    if args.interval:
        cfg.set("monitor.interval_seconds", args.interval)
    bot = TradingBot(cfg, Mode.SIMULATION)
    bot.run()
    return 0


def cmd_live(args: argparse.Namespace) -> int:
    print_banner()
    print_risk_warning()
    cfg = _load_config(args)
    try:
        assert_live_mode_confirmed(cfg, cli_flag_present=bool(args.i_understand_the_risk))
    except LiveTradingNotConfirmedError as e:
        error(str(e))
        print()
        info("Live trading was NOT started. See the README section on live-mode")
        info("confirmation gates, or run 'paper' mode instead.")
        return 1

    cfg.set("mode", "live")
    if args.strategy:
        cfg.set("strategy.name", args.strategy)
    if args.interval:
        cfg.set("monitor.interval_seconds", args.interval)

    warning("LIVE MODE CONFIRMED. Real funds may be at risk once signing is")
    warning("implemented by the operator. This build intentionally stops short")
    warning("of broadcasting signed transactions (see JupiterLiveExecutor).")
    print()

    bot = TradingBot(cfg, Mode.LIVE)
    bot.run()
    return 0


def cmd_backtest(args: argparse.Namespace) -> int:
    print_banner()
    cfg = _load_config(args)
    strategy_name = args.strategy or cfg.get("strategy.name", "composite")
    strategy = build_strategy(strategy_name, cfg.get("strategy.params", {}))
    balance = args.balance or float(cfg.get("trading.starting_balance_quote", 1.0))

    if not args.synthetic:
        warning("Only synthetic data is supported in this build (no bundled")
        warning("historical OHLC provider). Pass --synthetic to proceed.")
        return 1

    info(f"Generating {args.candles} synthetic candles (seed={args.seed})...")
    candles = generate_synthetic_candles(n=args.candles, seed=args.seed)

    engine = BacktestEngine(
        strategy, balance,
        stop_loss_pct=float(cfg.get("risk.stop_loss_pct", 12.0)),
        take_profit_pct=float(cfg.get("risk.take_profit_pct", 35.0)),
        trailing_stop_pct=float(cfg.get("risk.trailing_stop_pct", 10.0)) if cfg.get("risk.use_trailing_stop") else None,
    )
    try:
        report = engine.run(candles)
    except BacktestDataError as e:
        error(str(e))
        return 1

    print()
    print(f"  {C.BCYAN}{C.BOLD}Backtest Report{C.RESET}  ({strategy_name}, {len(candles)} candles)")
    print(f"  {C.DIM}{'-' * 56}{C.RESET}")
    for k, v in report.to_dict().items():
        if isinstance(v, float):
            print(f"  {k:<20} {v:>18.6f}")
        else:
            print(f"  {k:<20} {v:>18}")
    print()
    return 0


def cmd_scan(args: argparse.Namespace) -> int:
    print_banner()
    cfg = _load_config(args)
    market = MarketData(cfg)
    scanner = TokenScanner(cfg, market)
    queries = args.query or ["solana meme", "pump", "sol"]
    info(f"Scanning DexScreener for: {', '.join(queries)}")
    candidates = scanner.scan_once(queries)
    if not candidates:
        warning("No new candidates passed basic filters this pass.")
        return 0
    rows = [
        [c.token.symbol or "?", truncate_addr(c.token.mint), fmt_usd(c.token.liquidity_usd),
         fmt_usd(c.token.volume_24h_usd), fmt_usd(c.token.market_cap_usd), c.status.value]
        for c in candidates
    ]
    print()
    print_table(["Symbol", "Mint", "Liquidity", "Vol24h", "MCap", "Status"], rows)
    print()
    return 0


def cmd_status(args: argparse.Namespace) -> int:
    print_banner()
    cfg = _load_config(args)
    db = Database(Path(cfg.get("database.path", str(DB_FILE))))
    analyzer = PerformanceAnalyzer(db)
    print(f"  {C.BCYAN}{C.BOLD}Status{C.RESET}")
    print(f"  {C.DIM}{'-' * 40}{C.RESET}")
    print(f"  Config mode        : {cfg.get('mode')}")
    print(f"  Strategy           : {cfg.get('strategy.name')}")
    print(f"  Database           : {db.path}")
    print(f"  Emergency stop     : {cfg.get('risk.emergency_stop')}")
    print()
    print(analyzer.render_text_report())
    print()
    db.close()
    return 0


def cmd_performance(args: argparse.Namespace) -> int:
    print_banner()
    cfg = _load_config(args)
    db = Database(Path(cfg.get("database.path", str(DB_FILE))))
    analyzer = PerformanceAnalyzer(db)
    mode_filter = args.mode
    print(f"  {C.BCYAN}{C.BOLD}Performance{C.RESET}" + (f"  (mode={mode_filter})" if mode_filter else ""))
    print(f"  {C.DIM}{'-' * 40}{C.RESET}")
    print(analyzer.render_text_report(mode=mode_filter))
    print()
    top = analyzer.by_mint()
    if top:
        print(f"  {C.BCYAN}Top mints by PnL{C.RESET}")
        rows = [[r["symbol"] or "?", truncate_addr(r["mint"]), r["trades"],
                f"{r['pnl']:+.6f}", f"{r['avg_pnl_pct']:+.2f}%"] for r in top]
        print_table(["Symbol", "Mint", "Trades", "PnL", "AvgPnL%"], rows)
        print()
    db.close()
    return 0


def cmd_config(args: argparse.Namespace) -> int:
    print_banner()
    cfg = _load_config(args)
    if args.set:
        key, value = args.set
        try:
            value = json.loads(value)
        except json.JSONDecodeError:
            pass
        cfg.set(key, value)
        ok(f"Set '{key}' = {value!r}")
        return 0
    if args.reset:
        cfg.data = json.loads(json.dumps(DEFAULT_CONFIG))
        cfg.save()
        ok("Config reset to defaults")
        return 0
    print(f"  {C.BCYAN}{C.BOLD}Config{C.RESET}  ({cfg.path})")
    print(f"  {C.DIM}{'-' * 56}{C.RESET}")
    print(json.dumps(cfg.data, indent=2, ensure_ascii=False))
    print()
    return 0


def cmd_wallet(args: argparse.Namespace) -> int:
    print_banner()
    if not is_valid_solana_address(args.address):
        error("Invalid Solana address")
        return 1
    cfg = _load_config(args)
    rpc = SolanaClient(cfg)
    analyzer = WalletAnalyzer(cfg, rpc)
    info(f"Profiling wallet {args.address}")
    profile = analyzer.profile(args.address)
    print()
    print(f"  SOL balance      : {profile.sol_balance:.6f}")
    print(f"  Token accounts   : {profile.token_accounts}")
    print(f"  Tx count (est)   : {profile.tx_count_estimate}")
    print(f"  Age (days, est)  : {profile.age_days if profile.age_days is not None else 'unknown'}")
    print(f"  Whale            : {profile.is_whale}")
    print(f"  Suspicious       : {profile.is_suspicious}")
    if profile.notes:
        print(f"  Notes            :")
        for n in profile.notes:
            print(f"    - {n}")
    print()
    return 0


def cmd_analyze(args: argparse.Namespace) -> int:
    print_banner()
    if not is_valid_solana_address(args.mint):
        error("Invalid mint address")
        return 1
    cfg = _load_config(args)
    rpc = SolanaClient(cfg)
    market = MarketData(cfg)
    security = TokenSecurityAnalyzer(cfg, rpc, market)
    liquidity = LiquidityAnalyzer(cfg, market)

    info(f"Fetching market data for {args.mint}")
    token = market.build_token_info(args.mint)
    if token is None:
        error("Could not find any DEX pair for this mint")
        return 1

    print()
    print(f"  Symbol      : {token.symbol}")
    print(f"  Price       : {fmt_usd(token.price_usd)}")
    print(f"  Market cap  : {fmt_usd(token.market_cap_usd)}")
    print(f"  Liquidity   : {fmt_usd(token.liquidity_usd)}")
    print(f"  Volume 24h  : {fmt_usd(token.volume_24h_usd)}")
    print()

    info("Running security analysis...")
    sec = security.analyze(token)
    print()
    print(f"  {C.BCYAN}{C.BOLD}Security Report{C.RESET}  score={sec.risk_score:.1f}/100  level={sec.risk_level.value}  passed={sec.passed}")
    for f in sec.findings:
        color = {RiskLevel.CRITICAL: C.BRED, RiskLevel.HIGH: C.BRED, RiskLevel.MEDIUM: C.BYELLOW,
                 RiskLevel.LOW: C.BGREEN, RiskLevel.VERY_LOW: C.BGREEN}.get(f.severity, C.RESET)
        print(f"    [{color}{f.severity.value}{C.RESET}] {f.message}")

    liq = liquidity.analyze(token)
    print()
    print(f"  {C.BCYAN}{C.BOLD}Liquidity Report{C.RESET}")
    print(f"    Depth for 1% impact (buy) : {fmt_usd(liq.depth_buy_1pct)}")
    print(f"    Depth for 1% impact (sell): {fmt_usd(liq.depth_sell_1pct)}")
    for size, bps in sorted(liq.estimated_slippage_bps.items()):
        print(f"    ${size:>8.0f} trade -> ~{bps:.0f} bps slippage")
    print()
    return 0


def cmd_test(args: argparse.Namespace) -> int:
    print_banner()
    info("Running built-in test suite...")
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromModule(sys.modules[__name__])
    runner = unittest.TextTestRunner(verbosity=2 if args.verbose else 1)
    result = runner.run(suite)
    return 0 if result.wasSuccessful() else 1


# ================================================================================
#  BUILT-IN TESTS  (python trading.py --test)
# ================================================================================

class TestIndicators(unittest.TestCase):
    def setUp(self):
        random.seed(42)
        self.closes = [1.0 + math.sin(i / 5.0) * 0.1 + i * 0.001 for i in range(200)]
        self.highs = [c * 1.01 for c in self.closes]
        self.lows = [c * 0.99 for c in self.closes]
        self.volumes = [1000 + (50 * (i % 7)) for i in range(200)]

    def test_sma_length_and_none_prefix(self):
        out = Indicators.sma(self.closes, 10)
        self.assertEqual(len(out), len(self.closes))
        self.assertTrue(all(v is None for v in out[:9]))
        self.assertIsNotNone(out[9])

    def test_sma_matches_manual_average(self):
        out = Indicators.sma(self.closes, 5)
        manual = sum(self.closes[10:15]) / 5
        self.assertAlmostEqual(out[14], manual, places=9)

    def test_ema_converges_towards_price_trend(self):
        out = Indicators.ema(self.closes, 20)
        self.assertIsNotNone(out[-1])
        self.assertGreater(out[-1], out[19])  # uptrend drift should raise EMA over time

    def test_rsi_bounds(self):
        out = Indicators.rsi(self.closes, 14)
        values = [v for v in out if v is not None]
        self.assertTrue(all(0.0 <= v <= 100.0 for v in values))

    def test_rsi_extreme_uptrend_is_high(self):
        rising = [1.0 * (1.01 ** i) for i in range(60)]
        out = Indicators.rsi(rising, 14)
        self.assertGreater(out[-1], 70)

    def test_macd_shapes(self):
        macd_line, signal_line, hist = Indicators.macd(self.closes)
        self.assertEqual(len(macd_line), len(self.closes))
        self.assertEqual(len(signal_line), len(self.closes))
        self.assertEqual(len(hist), len(self.closes))

    def test_bollinger_upper_gte_lower(self):
        lower, middle, upper = Indicators.bollinger(self.closes, 20, 2.0)
        for lo, up in zip(lower, upper):
            if lo is not None and up is not None:
                self.assertGreaterEqual(up, lo)

    def test_atr_non_negative(self):
        out = Indicators.atr(self.highs, self.lows, self.closes, 14)
        for v in out:
            if v is not None:
                self.assertGreaterEqual(v, 0.0)

    def test_stochastic_bounds(self):
        k, d = Indicators.stochastic(self.highs, self.lows, self.closes)
        for v in k:
            if v is not None:
                self.assertTrue(-0.001 <= v <= 100.001)

    def test_adx_non_negative(self):
        out = Indicators.adx(self.highs, self.lows, self.closes)
        for v in out:
            if v is not None:
                self.assertGreaterEqual(v, 0.0)

    def test_obv_monotonic_on_pure_uptrend(self):
        rising = [1.0 + i * 0.01 for i in range(30)]
        vols = [100.0] * 30
        out = Indicators.obv(rising, vols)
        self.assertTrue(all(out[i] <= out[i + 1] for i in range(len(out) - 1)))

    def test_vwap_within_price_range(self):
        period = 20
        out = Indicators.vwap(self.highs, self.lows, self.closes, self.volumes, period=period)
        for i, v in enumerate(out):
            if v is None:
                continue
            start = max(0, i - period + 1)
            window_low = min(self.lows[start:i + 1])
            window_high = max(self.highs[start:i + 1])
            # A volume-weighted average over the window must lie within that
            # window's own high/low bounds (with a small tolerance for
            # floating point rounding).
            self.assertTrue(window_low * 0.999 <= v <= window_high * 1.001,
                            f"vwap {v} outside window [{window_low}, {window_high}] at i={i}")

    def test_volume_zscore_flags_spike(self):
        vols = [100.0] * 50 + [5000.0]
        out = Indicators.volume_zscore(vols, period=20)
        self.assertGreater(out[-1], 3.0)

    def test_donchian_channel_contains_price(self):
        upper, lower = Indicators.donchian(self.highs, self.lows, 20)
        for i in range(19, len(self.closes)):
            if upper[i] is not None:
                self.assertGreaterEqual(upper[i], lower[i])


class TestStrategies(unittest.TestCase):
    def _feed(self, strategy: Strategy, candles: List[Candle]) -> None:
        for c in candles:
            strategy.update(c)

    def test_breakout_detects_upside_break(self):
        candles = generate_synthetic_candles(n=60, seed=1, volatility=0.001, drift=0.0)
        # engineer an explicit breakout on the final candle
        last = candles[-1]
        candles[-1] = Candle(last.timestamp, last.open, last.high, last.low,
                              close=max(c.high for c in candles[-21:-1]) * 1.05, volume=last.volume)
        strat = BreakoutStrategy({"breakout_lookback": 20})
        self._feed(strat, candles)
        sig, _ = strat.signal()
        self.assertIn(sig, (TradeSignal.BUY, TradeSignal.STRONG_BUY))

    def test_rsi_strategy_neutral_without_data(self):
        strat = RsiStrategy()
        strat.update(Candle(0, 1, 1, 1, 1))
        sig, _ = strat.signal()
        self.assertEqual(sig, TradeSignal.NEUTRAL)

    def test_composite_returns_valid_signal(self):
        candles = generate_synthetic_candles(n=120, seed=7)
        strat = build_strategy("composite")
        self._feed(strat, candles)
        sig, reason = strat.signal()
        self.assertIsInstance(sig, TradeSignal)
        self.assertIsInstance(reason, str)

    def test_unknown_strategy_falls_back_to_composite(self):
        strat = build_strategy("does_not_exist")
        self.assertEqual(strat.name, "composite")

    def test_momentum_strategy_flags_strong_rally(self):
        candles = generate_synthetic_candles(n=30, seed=3, volatility=0.0001, drift=0.0)
        base = candles[-11].close
        candles[-1] = Candle(candles[-1].timestamp, candles[-1].open, candles[-1].high,
                             candles[-1].low, close=base * 1.10, volume=candles[-1].volume)
        strat = MomentumStrategy({"momentum_lookback": 10, "momentum_threshold_pct": 3.0})
        self._feed(strat, candles)
        sig, _ = strat.signal()
        self.assertIn(sig, (TradeSignal.BUY, TradeSignal.STRONG_BUY))


class TestRiskManager(unittest.TestCase):
    def setUp(self):
        self.cfg = Config(path=Path("/tmp/lax_test_config.json"))
        self.cfg.set("risk.max_open_positions", 2, persist=False)
        self.cfg.set("risk.cooldown_seconds", 0, persist=False)
        self.cfg.set("trading.max_position_quote", 1.0, persist=False)
        self.cfg.set("trading.min_order_quote", 0.001, persist=False)
        self.cfg.set("risk.max_trade_pct_of_equity", 0.5, persist=False)
        self.cfg.set("risk.blacklist_path", f"/tmp/lax_test_blacklist_{uuid.uuid4().hex}.json", persist=False)
        self.risk = RiskManager(self.cfg)

    def test_valid_buy_is_approved(self):
        ok_, reason = self.risk.validate_order(
            KNOWN_MINTS["BONK"], Side.BUY, quantity=1.0, price=0.1,
            equity=10.0, current_open_positions=0)
        self.assertTrue(ok_, reason)

    def test_zero_quantity_is_rejected(self):
        ok_, reason = self.risk.validate_order(
            KNOWN_MINTS["BONK"], Side.BUY, quantity=0.0, price=0.1,
            equity=10.0, current_open_positions=0)
        self.assertFalse(ok_)

    def test_invalid_address_is_rejected(self):
        ok_, reason = self.risk.validate_order(
            "not-a-real-address", Side.BUY, quantity=1.0, price=0.1,
            equity=10.0, current_open_positions=0)
        self.assertFalse(ok_)

    def test_emergency_stop_blocks_everything(self):
        self.risk.set_emergency_stop(True)
        ok_, reason = self.risk.validate_order(
            KNOWN_MINTS["BONK"], Side.BUY, quantity=1.0, price=0.1,
            equity=10.0, current_open_positions=0)
        self.assertFalse(ok_)
        self.assertIn("emergency", reason)

    def test_blacklisted_mint_is_rejected(self):
        self.risk.blacklist_mint(KNOWN_MINTS["BONK"], "test")
        ok_, reason = self.risk.validate_order(
            KNOWN_MINTS["BONK"], Side.BUY, quantity=1.0, price=0.1,
            equity=10.0, current_open_positions=0)
        self.assertFalse(ok_)

    def test_max_open_positions_enforced(self):
        ok_, reason = self.risk.validate_order(
            KNOWN_MINTS["BONK"], Side.BUY, quantity=0.01, price=0.1,
            equity=10.0, current_open_positions=2)
        self.assertFalse(ok_)

    def test_drawdown_blocks_new_entries(self):
        self.risk.update_equity(100.0)
        ok_, reason = self.risk.validate_order(
            KNOWN_MINTS["BONK"], Side.BUY, quantity=0.01, price=0.1,
            equity=50.0, current_open_positions=0)
        self.assertFalse(ok_)

    def test_sell_ignores_cooldown_and_position_limits(self):
        # Selling to reduce risk should never itself be blocked by open-position
        # or cooldown checks (only emergency stop / blacklist / bad data can).
        self.risk.last_trade_ts = time.time()
        self.cfg.set("risk.cooldown_seconds", 999, persist=False)
        ok_, reason = self.risk.validate_order(
            KNOWN_MINTS["BONK"], Side.SELL, quantity=1.0, price=0.1,
            equity=10.0, current_open_positions=99)
        self.assertTrue(ok_, reason)

    def tearDown(self):
        try:
            Path("/tmp/lax_test_config.json").unlink()
        except FileNotFoundError:
            pass


class TestPositionSizer(unittest.TestCase):
    def setUp(self):
        self.cfg = Config(path=Path("/tmp/lax_test_sizer.json"))
        self.cfg.set("trading.position_size_pct", 0.10, persist=False)
        self.cfg.set("trading.max_position_quote", 1.0, persist=False)
        self.cfg.set("trading.min_order_quote", 0.001, persist=False)
        self.sizer = PositionSizer(self.cfg)

    def test_basic_sizing(self):
        qty = self.sizer.compute(equity=10.0, price=1.0)
        self.assertAlmostEqual(qty, 1.0, places=6)  # 10% of 10 = 1.0, under max_position_quote cap? capped at 1.0

    def test_security_score_scales_down_size(self):
        qty_full = self.sizer.compute(equity=10.0, price=1.0, security_score=100.0)
        qty_weak = self.sizer.compute(equity=10.0, price=1.0, security_score=25.0)
        self.assertLess(qty_weak, qty_full)

    def test_zero_price_returns_zero(self):
        self.assertEqual(self.sizer.compute(equity=10.0, price=0.0), 0.0)

    def test_below_min_order_returns_zero(self):
        self.cfg.set("trading.position_size_pct", 0.0001, persist=False)
        sizer = PositionSizer(self.cfg)
        self.assertEqual(sizer.compute(equity=1.0, price=1.0), 0.0)

    def tearDown(self):
        try:
            Path("/tmp/lax_test_sizer.json").unlink()
        except FileNotFoundError:
            pass


class TestPortfolio(unittest.TestCase):
    def test_open_and_close_position_pnl(self):
        pf = Portfolio(starting_balance=10.0)
        pf.open_position("MINT1", "TEST", price=1.0, quantity=5.0)
        self.assertTrue(pf.has_position("MINT1"))
        qty, pnl, pnl_pct = pf.close_position("MINT1", price=1.5)
        self.assertAlmostEqual(qty, 5.0)
        self.assertAlmostEqual(pnl, 2.5)
        self.assertAlmostEqual(pnl_pct, 50.0)
        self.assertFalse(pf.has_position("MINT1"))

    def test_equity_reflects_open_position_value(self):
        pf = Portfolio(starting_balance=10.0)
        pf.open_position("MINT1", "TEST", price=2.0, quantity=2.0)
        eq = pf.equity({"MINT1": 3.0})
        self.assertAlmostEqual(eq, (10.0 - 4.0) + 2.0 * 3.0)

    def test_cannot_overspend_cash(self):
        pf = Portfolio(starting_balance=1.0)
        pf.open_position("MINT1", "TEST", price=1.0, quantity=100.0)
        pos = pf.get_position("MINT1")
        self.assertAlmostEqual(pos.quantity, 1.0)
        self.assertAlmostEqual(pf.cash, 0.0, places=6)


class TestSecurityAnalyzer(unittest.TestCase):
    class _FakeRpc:
        def __init__(self, mint_auth=None, freeze_auth=None, largest=None, supply=None):
            self._mint_auth = mint_auth
            self._freeze_auth = freeze_auth
            self._largest = largest or []
            self._supply = supply or {"uiAmount": 1_000_000.0}

        def get_account_info(self, mint, encoding="jsonParsed"):
            return {"owner": TOKEN_PROGRAM_ID,
                    "data": {"parsed": {"info": {"mintAuthority": self._mint_auth,
                                                 "freezeAuthority": self._freeze_auth}}}}

        def get_token_supply(self, mint):
            return self._supply

        def get_token_largest_accounts(self, mint):
            return self._largest

    def _make_token(self, liquidity=50000.0, mcap=200000.0, created_ago=3600):
        return TokenInfo(mint=KNOWN_MINTS["BONK"], symbol="TEST",
                          liquidity_usd=liquidity, market_cap_usd=mcap,
                          created_at=now_ts() - created_ago)

    def test_active_mint_authority_fails_hard(self):
        cfg = Config(path=Path("/tmp/lax_test_sec1.json"))
        rpc = self._FakeRpc(mint_auth="SomeAuthorityAddress111111111111111111111")
        analyzer = TokenSecurityAnalyzer(cfg, rpc, MarketData(cfg))
        report = analyzer.analyze(self._make_token())
        self.assertFalse(report.passed)
        try:
            Path("/tmp/lax_test_sec1.json").unlink()
        except FileNotFoundError:
            pass

    def test_clean_token_with_distributed_holders_passes(self):
        cfg = Config(path=Path("/tmp/lax_test_sec2.json"))
        holders = [{"address": f"Holder{i}" + "1" * 30, "amount": 20000.0} for i in range(20)]
        rpc = self._FakeRpc(mint_auth=None, freeze_auth=None, largest=holders,
                            supply={"uiAmount": 1_000_000.0})
        analyzer = TokenSecurityAnalyzer(cfg, rpc, MarketData(cfg))
        token = self._make_token(liquidity=80000.0, mcap=150000.0)
        token.holder_count = 200
        report = analyzer.analyze(token)
        self.assertTrue(report.passed, report.summary())
        try:
            Path("/tmp/lax_test_sec2.json").unlink()
        except FileNotFoundError:
            pass

    def test_high_concentration_reduces_score(self):
        cfg = Config(path=Path("/tmp/lax_test_sec3.json"))
        whale_holders = [{"address": "Whale" + "1" * 35, "amount": 800000.0}]
        rpc = self._FakeRpc(mint_auth=None, freeze_auth=None, largest=whale_holders,
                            supply={"uiAmount": 1_000_000.0})
        analyzer = TokenSecurityAnalyzer(cfg, rpc, MarketData(cfg))
        report = analyzer.analyze(self._make_token())
        self.assertLess(report.risk_score, 70.0)
        try:
            Path("/tmp/lax_test_sec3.json").unlink()
        except FileNotFoundError:
            pass


class TestLiquidityAnalyzer(unittest.TestCase):
    def test_zero_liquidity_is_insufficient(self):
        cfg = Config(path=Path("/tmp/lax_test_liq1.json"))
        analyzer = LiquidityAnalyzer(cfg, MarketData(cfg))
        token = TokenInfo(mint=KNOWN_MINTS["BONK"], liquidity_usd=0.0)
        report = analyzer.analyze(token)
        self.assertFalse(report.is_sufficient)
        try:
            Path("/tmp/lax_test_liq1.json").unlink()
        except FileNotFoundError:
            pass

    def test_larger_trade_has_more_slippage(self):
        cfg = Config(path=Path("/tmp/lax_test_liq2.json"))
        analyzer = LiquidityAnalyzer(cfg, MarketData(cfg))
        token = TokenInfo(mint=KNOWN_MINTS["BONK"], liquidity_usd=20000.0)
        small = analyzer.estimate_slippage_bps(token, 50)
        large = analyzer.estimate_slippage_bps(token, 5000)
        self.assertLess(small, large)
        try:
            Path("/tmp/lax_test_liq2.json").unlink()
        except FileNotFoundError:
            pass


class TestBacktestEngine(unittest.TestCase):
    def test_backtest_produces_valid_report(self):
        candles = generate_synthetic_candles(n=300, seed=11)
        strat = build_strategy("composite")
        engine = BacktestEngine(strat, starting_balance=1.0, warmup_bars=30)
        report = engine.run(candles)
        self.assertGreaterEqual(report.starting_balance, 0)
        self.assertIsInstance(report.sharpe, float)
        self.assertGreaterEqual(report.max_drawdown_pct, 0.0)

    def test_backtest_raises_on_insufficient_data(self):
        strat = build_strategy("rsi")
        engine = BacktestEngine(strat, starting_balance=1.0, warmup_bars=30)
        with self.assertRaises(BacktestDataError):
            engine.run(generate_synthetic_candles(n=5, seed=1))

    def test_backtest_no_lookahead_bias(self):
        """Truncating the candle series must not change EARLIER entry
        decisions — i.e. the strategy never had access to future bars.

        Note: this deliberately compares ENTRY times, not exit times/trade
        counts. A trade still open at the truncation point will legitimately
        be force-closed early in the truncated run (end_of_data) but would
        keep running in the full series — that divergence is correct
        behaviour, not lookahead bias.
        """
        candles = generate_synthetic_candles(n=200, seed=99)
        cutoff_ts = candles[149].timestamp

        strat1 = build_strategy("ema_cross")
        engine1 = BacktestEngine(strat1, starting_balance=1.0, warmup_bars=30)
        engine1.run(candles)

        strat2 = build_strategy("ema_cross")
        engine2 = BacktestEngine(strat2, starting_balance=1.0, warmup_bars=30)
        engine2.run(candles[:150])

        entries_full = sorted(t.entry_time for t in engine1.trades if t.entry_time <= cutoff_ts)
        entries_partial = sorted(t.entry_time for t in engine2.trades if t.entry_time <= cutoff_ts)
        self.assertEqual(entries_full, entries_partial)


class TestUtils(unittest.TestCase):
    def test_valid_solana_address(self):
        self.assertTrue(is_valid_solana_address(KNOWN_MINTS["SOL"]))
        self.assertFalse(is_valid_solana_address("too_short"))
        self.assertFalse(is_valid_solana_address(None))
        self.assertFalse(is_valid_solana_address("0OIl" * 10))  # invalid base58 chars

    def test_pct_change(self):
        self.assertAlmostEqual(pct_change(100, 110), 10.0)
        self.assertAlmostEqual(pct_change(0, 110), 0.0)

    def test_safe_div(self):
        self.assertEqual(safe_div(10, 0), 0.0)
        self.assertEqual(safe_div(10, 2), 5.0)

    def test_mask_secret_never_leaks(self):
        secret = "super-secret-private-key-value"
        masked = mask_secret(secret)
        self.assertNotIn(secret, masked)

    def test_rate_limiter_throttles(self):
        limiter = TokenBucketRateLimiter(rate_per_sec=1000, burst=2)
        start = time.monotonic()
        for _ in range(2):
            limiter.acquire()
        elapsed = time.monotonic() - start
        self.assertLess(elapsed, 1.0)

    def test_circuit_breaker_opens_after_threshold(self):
        cb = CircuitBreaker(failure_threshold=3, cooldown_seconds=1000)
        for _ in range(3):
            cb.record_failure()
        self.assertFalse(cb.allow())

    def test_lru_cache_ttl_expiry(self):
        cache = LRUCache(maxsize=10, ttl=0.05)
        cache.set("k", "v")
        self.assertEqual(cache.get("k"), "v")
        time.sleep(0.1)
        self.assertIsNone(cache.get("k"))


# ================================================================================
#  ARGUMENT PARSER
# ================================================================================

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="trading.py",
        description=f"{APP_NAME} v{VERSION} — algorithmic memecoin trading for Solana.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent(f"""
        examples:
          python trading.py --mode paper
          python trading.py --mode backtest --synthetic
          python trading.py --mode simulation --strategy breakout
          python trading.py --scan
          python trading.py --status
          python trading.py --performance
          python trading.py --test

        project links:
          Discord  {PROJECT['discord']}
          X        {PROJECT['x']}
          GitHub   {PROJECT['github']}

        WARNING: memecoin trading is extremely high risk. Default mode is
        PAPER (no real funds at risk). Live mode requires explicit,
        multi-step confirmation — see the 'live' subcommand's --help.
        """),
    )
    p.add_argument("--version", action="version", version=f"%(prog)s {VERSION}")
    p.add_argument("-c", "--config", help="Path to config file (default: %s)" % CONFIG_FILE)

    # Legacy-style top-level convenience flags (--mode X, --scan, --status, ...)
    p.add_argument("--mode", choices=[m.value for m in Mode], help="Shortcut for the matching subcommand")
    p.add_argument("--scan", action="store_true", help="Shortcut for the 'scan' subcommand")
    p.add_argument("--status", action="store_true", help="Shortcut for the 'status' subcommand")
    p.add_argument("--performance", action="store_true", help="Shortcut for the 'performance' subcommand")
    p.add_argument("--test", action="store_true", help="Shortcut for the 'test' subcommand")
    p.add_argument("--strategy", help="Strategy name (used with --mode)")
    p.add_argument("--interval", type=int, help="Polling interval in seconds (used with --mode)")
    p.add_argument("--synthetic", action="store_true", help="Use synthetic data (used with --mode backtest)")
    p.add_argument("--candles", type=int, default=500, help="Number of synthetic candles for backtest")
    p.add_argument("--seed", type=int, help="Random seed for synthetic data")
    p.add_argument("--balance", type=float, help="Starting balance override")
    p.add_argument("--i-understand-the-risk", action="store_true",
                    help="Required (one of three gates) to enable --mode live")
    p.add_argument("-v", "--verbose", action="store_true", help="Verbose output")

    sub = p.add_subparsers(dest="command", metavar="<command>")

    sp = sub.add_parser("paper", help="Run in paper trading mode (default, no real funds)")
    sp.add_argument("--strategy")
    sp.add_argument("--interval", type=int)
    sp.set_defaults(func=cmd_paper)

    sp = sub.add_parser("simulation", help="Run a quiet dry run (no notifications)")
    sp.add_argument("--strategy")
    sp.add_argument("--interval", type=int)
    sp.set_defaults(func=cmd_simulation)

    sp = sub.add_parser("live", help="Run in LIVE mode (requires explicit multi-step confirmation)")
    sp.add_argument("--strategy")
    sp.add_argument("--interval", type=int)
    sp.add_argument("--i-understand-the-risk", action="store_true", dest="i_understand_the_risk")
    sp.set_defaults(func=cmd_live)

    sp = sub.add_parser("backtest", help="Backtest a strategy on synthetic data")
    sp.add_argument("--strategy")
    sp.add_argument("--balance", type=float)
    sp.add_argument("--candles", type=int, default=500)
    sp.add_argument("--synthetic", action="store_true")
    sp.add_argument("--seed", type=int)
    sp.set_defaults(func=cmd_backtest)

    sp = sub.add_parser("scan", help="Run one scanner pass and print qualified candidates")
    sp.add_argument("--query", nargs="*", help="Search queries (default: solana meme pump sol)")
    sp.set_defaults(func=cmd_scan)

    sp = sub.add_parser("status", help="Show current configuration and stats summary")
    sp.set_defaults(func=cmd_status)

    sp = sub.add_parser("performance", help="Show detailed performance analytics")
    sp.add_argument("--mode", choices=[m.value for m in Mode])
    sp.set_defaults(func=cmd_performance)

    sp = sub.add_parser("config", help="View or edit configuration")
    sp.add_argument("--set", nargs=2, metavar=("KEY", "VALUE"))
    sp.add_argument("--reset", action="store_true")
    sp.set_defaults(func=cmd_config)

    sp = sub.add_parser("wallet", help="Profile a Solana wallet (balances, activity, whale/suspicious heuristics)")
    sp.add_argument("address")
    sp.set_defaults(func=cmd_wallet)

    sp = sub.add_parser("analyze", help="Run security + liquidity analysis on a single token mint")
    sp.add_argument("mint")
    sp.set_defaults(func=cmd_analyze)

    sp = sub.add_parser("test", help="Run the built-in test suite")
    sp.add_argument("-v", "--verbose", action="store_true")
    sp.set_defaults(func=cmd_test)

    return p


# ================================================================================
#  MAIN
# ================================================================================

_MODE_TO_FUNC = {
    Mode.PAPER: cmd_paper,
    Mode.SIMULATION: cmd_simulation,
    Mode.LIVE: cmd_live,
    Mode.BACKTEST: cmd_backtest,
}


def _install_signal_handlers() -> None:
    """Ensure Ctrl+C / SIGTERM triggers a graceful shutdown path rather than
    an abrupt kill mid-trade. Handlers just set a flag; the run loops already
    check `running` and their own KeyboardInterrupt handling.
    """
    def _handler(signum, frame):  # noqa: ARG001
        raise KeyboardInterrupt()
    try:
        signal.signal(signal.SIGTERM, _handler)
    except (ValueError, OSError):
        pass  # not available on this platform/thread


def main() -> int:
    _install_signal_handlers()
    parser = build_parser()

    if len(sys.argv) == 1:
        print_banner()
        print_risk_warning()
        parser.print_help()
        print()
        return 0

    args = parser.parse_args()

    # Route top-level convenience flags to the same handlers as subcommands.
    if getattr(args, "command", None) is None:
        if args.test:
            return cmd_test(args)
        if args.scan:
            return cmd_scan(args)
        if args.status:
            return cmd_status(args)
        if args.performance:
            return cmd_performance(args)
        if args.mode:
            mode = Mode(args.mode)
            func = _MODE_TO_FUNC[mode]
            return func(args)
        print_banner()
        parser.print_help()
        print()
        return 0

    if not hasattr(args, "func"):
        print_banner()
        parser.print_help()
        print()
        return 0

    try:
        return args.func(args)
    except LaxError as e:
        error(f"{type(e).__name__}: {e}")
        return 1
    except KeyboardInterrupt:
        print()
        warning("Interrupted by user")
        return 0
    except Exception as e:  # noqa: BLE001
        error(f"Unexpected error: {e}")
        logging.getLogger("lax").debug(traceback.format_exc())
        return 1


if __name__ == "__main__":
    sys.exit(main())
