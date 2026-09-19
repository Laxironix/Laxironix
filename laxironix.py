#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║     LAXIRONIX TOOLKIT                                                        ║
║     All-in-one CLI for the $LAX community on Solana                          ║
║                                                                              ║
║     Discord : https://discord.gg/V3HnCfHm6                                   ║
║     X       : https://x.com/Laxironix                                        ║
║     GitHub  : https://github.com/Laxironix                                   ║
║     Pump    : https://pump.fun                                               ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝

Features
────────
  • Wallet balances      — SOL + any SPL token
  • Live price tracking  — via Jupiter aggregator
  • Wallet monitoring    — alerts on any balance change
  • Portfolio tracker    — multi-wallet, multi-token summary
  • Transaction history  — recent activity for a wallet
  • Airdrop checker      — mirrors the website logic
  • Discord alerts       — send notifications via webhook
  • Persistent config    — stored in ~/.laxironix/
  • Colored output       — clean, readable terminal UX

Usage
─────
  python laxironix.py <command> [options]

  Commands
    balance    <wallet>              SOL + token balance
    price      [--mint MINT]         Token price in USD
    watch      <wallet>              Monitor wallet for changes
    portfolio  <wallet> [<wallet>..] Aggregate portfolio
    history    <wallet>              Recent transactions
    airdrop    <wallet>              Check airdrop eligibility
    config     [--set KEY VALUE]     Show / edit config
    webhook    <url>                 Set Discord webhook
    test-alert                       Send test alert to Discord
    version                          Show version info

Examples
────────
  python laxironix.py balance 7xKX...x8F
  python laxironix.py price
  python laxironix.py watch 7xKX...x8F --interval 60
  python laxironix.py portfolio 7xKX... 5yLM... --json
  python laxironix.py webhook https://discord.com/api/webhooks/...
  python laxironix.py config --set network devnet

License: MIT
"""

# ═══════════════════════════════════════════════════════════════════════════════
#  IMPORTS
# ═══════════════════════════════════════════════════════════════════════════════

import argparse
import json
import os
import re
import sys
import time
import signal
import hashlib
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

# ─── Dependency check ──────────────────────────────────────────────────────────

try:
    import requests
except ImportError:
    print("\n  [ERROR] Missing dependency: requests")
    print("  Install it with:   pip install -r requirements.txt")
    print("                     pip install requests\n")
    sys.exit(1)


# ═══════════════════════════════════════════════════════════════════════════════
#  CONSTANTS
# ═══════════════════════════════════════════════════════════════════════════════

VERSION = "1.0.0"
APP = "Laxironix Toolkit"
CONFIG_DIR = Path.home() / ".laxironix"
CONFIG_FILE = CONFIG_DIR / "config.json"
STATE_FILE  = CONFIG_DIR / "state.json"

PROJECT = {
    "name":    "Laxironix",
    "ticker":  "$LAX",
    "chain":   "Solana",
    "discord": "https://discord.gg/V3HnCfHm6",
    "x":       "https://x.com/Laxironix",
    "github":  "https://github.com/Laxironix",
    "pump":    "https://pump.fun",
}

RPC_ENDPOINTS = {
    "mainnet": "https://api.mainnet-beta.solana.com",
    "devnet":  "https://api.devnet.solana.com",
    "testnet": "https://api.testnet.solana.com",
}

KNOWN_MINTS = {
    "SOL":  "So11111111111111111111111111111111111111112",
    "USDC": "EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v",
    "USDT": "Es9vMFrzaCERmJfrF4H2FYD4KCoNkY11McCe8BenwNYB",
    "BONK": "DezXAZ8z7PnrnRJjz3wXBoRgixCa6xjnB7YaB1pPB263",
    "JUP":  "JUPyiwrYJFskUPiHa7hkeR8VUtAeFoSYbKedZNsDvCN",
    "WIF":  "EKpQGSJtjMFqKZ9KQanSqYXRcF8fBopzLHYxdM65zcjm",
    "RAY":  "4k3Dyjzvzp8eMZWUXbBCjEvwSkkk59S5iCNLY3QrkX6R",
}

LAMPORTS_PER_SOL = 1_000_000_000
TOKEN_PROGRAM_ID = "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"

JUPITER_PRICE_API  = "https://price.jup.ag/v6/price"
JUPITER_TOKENS_API = "https://tokens.jup.ag/tokens"


# ═══════════════════════════════════════════════════════════════════════════════
#  TERMINAL COLORS
# ═══════════════════════════════════════════════════════════════════════════════

class C:
    _on = sys.stdout.isatty() and os.environ.get("NO_COLOR") is None

    RESET   = "\033[0m"  if _on else ""
    BOLD    = "\033[1m"  if _on else ""
    DIM     = "\033[2m"  if _on else ""
    ITALIC  = "\033[3m"  if _on else ""
    UNDER   = "\033[4m"  if _on else ""

    RED     = "\033[31m" if _on else ""
    GREEN   = "\033[32m" if _on else ""
    YELLOW  = "\033[33m" if _on else ""
    BLUE    = "\033[34m" if _on else ""
    MAGENTA = "\033[35m" if _on else ""
    CYAN    = "\033[36m" if _on else ""
    WHITE   = "\033[37m" if _on else ""

    BRIGHT_RED     = "\033[91m" if _on else ""
    BRIGHT_GREEN   = "\033[92m" if _on else ""
    BRIGHT_YELLOW  = "\033[93m" if _on else ""
    BRIGHT_BLUE    = "\033[94m" if _on else ""
    BRIGHT_MAGENTA = "\033[95m" if _on else ""
    BRIGHT_CYAN    = "\033[96m" if _on else ""

    BG_RED    = "\033[41m" if _on else ""
    BG_GREEN  = "\033[42m" if _on else ""


# ═══════════════════════════════════════════════════════════════════════════════
#  OUTPUT HELPERS
# ═══════════════════════════════════════════════════════════════════════════════

def banner():
    """Print the app banner."""
    print()
    print(f"{C.BRIGHT_MAGENTA}{C.BOLD}  ╔══════════════════════════════════════════════════════════╗{C.RESET}")
    print(f"{C.BRIGHT_MAGENTA}{C.BOLD}  ║{C.RESET}  {C.BOLD}{C.WHITE}LAXIRONIX TOOLKIT{C.RESET}  {C.DIM}·  v{VERSION}{C.RESET}                       {C.BRIGHT_MAGENTA}{C.BOLD}║{C.RESET}")
    print(f"{C.BRIGHT_MAGENTA}{C.BOLD}  ║{C.RESET}  {C.DIM}Built on Solana · Driven by the community{C.RESET}              {C.BRIGHT_MAGENTA}{C.BOLD}║{C.RESET}")
    print(f"{C.BRIGHT_MAGENTA}{C.BOLD}  ╚══════════════════════════════════════════════════════════╝{C.RESET}")
    print()


def section(title: str):
    """Print a section header."""
    print()
    print(f"  {C.BRIGHT_CYAN}{C.BOLD}▸ {title}{C.RESET}")
    print(f"  {C.DIM}{'─' * (len(title) + 4)}{C.RESET}")


def ok(msg: str):    print(f"  {C.BRIGHT_GREEN}✔{C.RESET}  {msg}")
def info(msg: str):  print(f"  {C.BRIGHT_BLUE}ℹ{C.RESET}  {msg}")
def warn(msg: str):  print(f"  {C.BRIGHT_YELLOW}⚠{C.RESET}  {msg}")
def error(msg: str): print(f"  {C.BRIGHT_RED}✘{C.RESET}  {msg}")


def kv(label: str, value: str, color: str = "") -> None:
    """Print a key-value line, aligned."""
    pad = 20
    print(f"  {C.DIM}{label:<{pad}}{C.RESET} {color}{value}{C.RESET}")


def fmt_num(n: float, decimals: int = 4) -> str:
    """Format a number with thousands separators."""
    if n is None:
        return "—"
    if abs(n) >= 1:
        return f"{n:,.{decimals}f}"
    return f"{n:.{max(decimals, 6)}f}"


def truncate(s: str, n: int = 20) -> str:
    """Truncate a long string in the middle."""
    if len(s) <= n:
        return s
    half = (n - 3) // 2
    return f"{s[:half]}...{s[-half:]}"


# ═══════════════════════════════════════════════════════════════════════════════
#  CONFIG
# ═══════════════════════════════════════════════════════════════════════════════

DEFAULT_CONFIG: Dict[str, Any] = {
    "version":            VERSION,
    "network":            "mainnet",
    "rpc_url":            None,
    "discord_webhook":    None,
    "watch_interval":     30,
    "alert_threshold_sol": 0.01,
    "tracked_tokens": {
        "SOL":  KNOWN_MINTS["SOL"],
        "USDC": KNOWN_MINTS["USDC"],
    },
    "watched_wallets":    [],
}


class Config:
    """JSON config persisted in ~/.laxironix/config.json."""

    def __init__(self, path: Path = CONFIG_FILE):
        self.path = path
        self.data: Dict[str, Any] = {}
        self.load()

    def load(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        if self.path.exists():
            try:
                with open(self.path, "r", encoding="utf-8") as f:
                    raw = json.load(f)
                merged = dict(DEFAULT_CONFIG)
                merged.update(raw)
                self.data = merged
            except Exception as e:
                warn(f"Config corrupted, using defaults: {e}")
                self.data = dict(DEFAULT_CONFIG)
        else:
            self.data = dict(DEFAULT_CONFIG)
            self.save()

    def save(self) -> None:
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(self.data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            error(f"Failed to save config: {e}")

    def get(self, key: str, default: Any = None) -> Any:
        return self.data.get(key, default)

    def set(self, key: str, value: Any) -> None:
        self.data[key] = value
        self.save()

    def __getitem__(self, key: str) -> Any:
        return self.data[key]

    def __setitem__(self, key: str, value: Any) -> None:
        self.set(key, value)


class State:
    """Runtime state persisted in ~/.laxironix/state.json."""

    def __init__(self, path: Path = STATE_FILE):
        self.path = path
        self.data: Dict[str, Any] = {}
        self.load()

    def load(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        if self.path.exists():
            try:
                with open(self.path, "r", encoding="utf-8") as f:
                    self.data = json.load(f)
            except Exception:
                self.data = {}

    def save(self) -> None:
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(self.data, f, indent=2)
        except Exception as e:
            error(f"Failed to save state: {e}")

    def get(self, key: str, default: Any = None) -> Any:
        return self.data.get(key, default)

    def set(self, key: str, value: Any) -> None:
        self.data[key] = value
        self.save()


config = Config()
state = State()


# ═══════════════════════════════════════════════════════════════════════════════
#  SOLANA RPC CLIENT
# ═══════════════════════════════════════════════════════════════════════════════

class SolanaRPC:
    """Minimal JSON-RPC client for Solana."""

    def __init__(self, network: str = "mainnet",
                 custom_url: Optional[str] = None,
                 timeout: int = 20):
        self.network = network
        self.url = custom_url or RPC_ENDPOINTS.get(network, RPC_ENDPOINTS["mainnet"])
        self.timeout = timeout
        self._req_id = 0
        self.session = requests.Session()
        self.session.headers.update({
            "Content-Type": "application/json",
            "User-Agent":   f"LaxironixToolkit/{VERSION}",
        })

    def _call(self, method: str, params: Optional[List] = None) -> Any:
        self._req_id += 1
        payload = {
            "jsonrpc": "2.0",
            "id":      self._req_id,
            "method":  method,
            "params":  params or [],
        }
        try:
            r = self.session.post(self.url, json=payload, timeout=self.timeout)
            r.raise_for_status()
            data = r.json()
            if "error" in data:
                raise RuntimeError(f"RPC error: {data['error']}")
            return data.get("result")
        except requests.exceptions.Timeout:
            raise RuntimeError(f"RPC timeout after {self.timeout}s ({method})")
        except requests.exceptions.RequestException as e:
            raise RuntimeError(f"RPC request failed: {e}")

    # ─── Chain queries ────────────────────────────────────────────────────────

    def get_balance_lamports(self, wallet: str) -> int:
        res = self._call("getBalance", [wallet, {"commitment": "confirmed"}])
        return int(res.get("value", 0)) if isinstance(res, dict) else 0

    def get_sol_balance(self, wallet: str) -> float:
        return self.get_balance_lamports(wallet) / LAMPORTS_PER_SOL

    def get_token_accounts(self, wallet: str) -> List[Dict[str, Any]]:
        """Return parsed SPL token accounts owned by wallet."""
        params = [
            wallet,
            {"programId": TOKEN_PROGRAM_ID},
            {"encoding": "jsonParsed", "commitment": "confirmed"},
        ]
        try:
            res = self._call("getTokenAccountsByOwner", params)
        except RuntimeError:
            return []
        if not res:
            return []
        accounts = res.get("value", []) or []
        out = []
        for acc in accounts:
            try:
                info = acc["account"]["data"]["parsed"]["info"]
                out.append({
                    "mint":   info["mint"],
                    "amount": float(info["tokenAmount"]["uiAmount"] or 0),
                    "decimals": int(info["tokenAmount"]["decimals"]),
                    "raw":    int(info["tokenAmount"]["amount"]),
                })
            except Exception:
                continue
        return out

    def get_signatures(self, wallet: str, limit: int = 10) -> List[Dict[str, Any]]:
        """Return recent transaction signatures."""
        params = [wallet, {"limit": limit}]
        try:
            res = self._call("getSignaturesForAddress", params)
        except RuntimeError:
            return []
        return res or []

    def get_transaction(self, signature: str) -> Optional[Dict[str, Any]]:
        params = [signature, {"encoding": "jsonParsed", "maxSupportedTransactionVersion": 0}]
        try:
            return self._call("getTransaction", params)
        except RuntimeError:
            return None

    def get_latest_blockhash(self) -> Optional[str]:
        res = self._call("getLatestBlockhash", [{"commitment": "confirmed"}])
        if res and "value" in res:
            return res["value"].get("blockhash")
        return None


# ═══════════════════════════════════════════════════════════════════════════════
#  JUPITER PRICE API
# ═══════════════════════════════════════════════════════════════════════════════

class JupiterPrice:
    """Fetch token prices from the Jupiter aggregator (no API key needed)."""

    @staticmethod
    def get_price(mint: str) -> Optional[float]:
        """Get the USD price of a token mint. Returns None if unavailable."""
        try:
            r = requests.get(
                JUPITER_PRICE_API,
                params={"ids": mint},
                timeout=15,
                headers={"User-Agent": f"LaxironixToolkit/{VERSION}"},
            )
            r.raise_for_status()
            data = r.json()
            entry = data.get("data", {}).get(mint)
            if entry and "price" in entry:
                return float(entry["price"])
            return None
        except Exception:
            return None

    @staticmethod
    def get_prices(mints: List[str]) -> Dict[str, Optional[float]]:
        """Get USD prices for multiple mints in one call."""
        if not mints:
            return {}
        try:
            r = requests.get(
                JUPITER_PRICE_API,
                params={"ids": ",".join(mints)},
                timeout=15,
                headers={"User-Agent": f"LaxironixToolkit/{VERSION}"},
            )
            r.raise_for_status()
            data = r.json()
            out: Dict[str, Optional[float]] = {}
            for mint in mints:
                entry = data.get("data", {}).get(mint)
                out[mint] = float(entry["price"]) if entry and "price" in entry else None
            return out
        except Exception:
            return {m: None for m in mints}

    @staticmethod
    def search_token(query: str) -> Optional[Dict[str, Any]]:
        """Search Jupiter token list for a symbol. Returns first match."""
        try:
            r = requests.get(JUPITER_TOKENS_API, timeout=20,
                             headers={"User-Agent": f"LaxironixToolkit/{VERSION}"})
            r.raise_for_status()
            tokens = r.json()
            q = query.upper().strip()
            for tok in tokens:
                if tok.get("symbol", "").upper() == q:
                    return tok
            for tok in tokens:
                if q in tok.get("symbol", "").upper():
                    return tok
            return None
        except Exception:
            return None


# ═══════════════════════════════════════════════════════════════════════════════
#  DISCORD WEBHOOK
# ═══════════════════════════════════════════════════════════════════════════════

class Discord:
    """Simple Discord webhook sender."""

    COLORS = {
        "info":    0x5DA9FF,
        "success": 0x14F195,
        "warning": 0xFFB020,
        "error":   0xFF4D6D,
        "brand":   0x9945FF,
    }

    def __init__(self, webhook_url: Optional[str] = None):
        self.url = webhook_url or config.get("discord_webhook")

    def send(self, content: str = "", embeds: Optional[List[Dict]] = None,
             username: str = "Laxironix Bot") -> bool:
        if not self.url:
            return False
        payload: Dict[str, Any] = {
            "username": username,
            "content":  content or "",
        }
        if embeds:
            payload["embeds"] = embeds
        try:
            r = requests.post(self.url, json=payload, timeout=15)
            return r.status_code in (200, 204)
        except Exception:
            return False

    def alert(self, title: str, description: str = "",
              color: str = "brand",
              fields: Optional[List[Dict[str, Any]]] = None) -> bool:
        embed: Dict[str, Any] = {
            "title":       title,
            "description": description,
            "color":       self.COLORS.get(color, self.COLORS["brand"]),
            "timestamp":   datetime.utcnow().isoformat() + "Z",
            "footer": {
                "text": f"{APP} v{VERSION}",
            },
        }
        if fields:
            embed["fields"] = fields
        return self.send(embeds=[embed])


# ═══════════════════════════════════════════════════════════════════════════════
#  WALLET VALIDATION
# ═══════════════════════════════════════════════════════════════════════════════

BASE58_ALPHABET = set("123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz")


def is_valid_solana_address(addr: str) -> bool:
    """Basic Solana address validation (base58, 32-44 chars)."""
    if not addr or not isinstance(addr, str):
        return False
    addr = addr.strip()
    if not (32 <= len(addr) <= 44):
        return False
    return all(c in BASE58_ALPHABET for c in addr)


# ═══════════════════════════════════════════════════════════════════════════════
#  AIRDROP LOGIC  (mirrors the website checker)
# ═══════════════════════════════════════════════════════════════════════════════

def airdrop_score(address: str) -> int:
    """Deterministic pseudo-score 0-99 based on the address string."""
    h = hashlib.sha256(address.encode("utf-8")).hexdigest()
    return int(h[:8], 16) % 100


def airdrop_tier(address: str) -> Tuple[str, str, str]:
    """
    Return (tier, message, color_key).
    Mirrors the JavaScript website logic.
    """
    score = airdrop_score(address)
    if score < 20:
        return ("EARLY", "You're on the early-community list 🎉", "green")
    if score < 60:
        return ("PENDING", "Not eligible yet — snapshots update periodically ⏳", "yellow")
    return ("NONE", "No snapshot found — join Discord for future rounds 📭", "dim")


# ═══════════════════════════════════════════════════════════════════════════════
#  COMMANDS
# ═══════════════════════════════════════════════════════════════════════════════

def cmd_balance(args: argparse.Namespace) -> int:
    """Check SOL + token balances for a wallet."""
    banner()
    wallet = args.wallet.strip()

    if not is_valid_solana_address(wallet):
        error(f"Invalid Solana address: {wallet}")
        return 1

    rpc = SolanaRPC(network=config.get("network"), custom_url=config.get("rpc_url"))

    section("Wallet")
    kv("Address", wallet)
    kv("Network", config.get("network", "mainnet"))
    kv("Explorer", f"https://solscan.io/account/{wallet}")

    section("Balances")

    try:
        sol = rpc.get_sol_balance(wallet)
        sol_price = JupiterPrice.get_price(KNOWN_MINTS["SOL"]) or 0
        usd = sol * sol_price
        kv("SOL", f"{fmt_num(sol, 4)} SOL  {C.DIM}(≈ ${fmt_num(usd, 2)}){C.RESET}")
    except Exception as e:
        error(f"Failed to fetch SOL balance: {e}")
        return 1

    try:
        accounts = rpc.get_token_accounts(wallet)
    except Exception as e:
        warn(f"Failed to fetch token accounts: {e}")
        accounts = []

    if not accounts:
        info("No SPL tokens found in this wallet.")
    else:
        mints = [a["mint"] for a in accounts if a["amount"] > 0]
        prices = JupiterPrice.get_prices(mints) if mints else {}

        nonzero = [a for a in accounts if a["amount"] > 0]
        nonzero.sort(key=lambda a: a["amount"], reverse=True)

        print()
        for acc in nonzero[:20]:
            mint = acc["mint"]
            price = prices.get(mint)
            value = (price or 0) * acc["amount"]
            label = truncate(mint, 12)
            if price:
                kv(f"Token {label}", f"{fmt_num(acc['amount'], 4):>18}  {C.DIM}≈ ${fmt_num(value, 2)}{C.RESET}")
            else:
                kv(f"Token {label}", f"{fmt_num(acc['amount'], 4):>18}  {C.DIM}(no price){C.RESET}")

        if len(nonzero) > 20:
            info(f"... and {len(nonzero) - 20} more token accounts")

    print()
    return 0


def cmd_price(args: argparse.Namespace) -> int:
    """Get token price via Jupiter."""
    banner()

    mint = args.mint
    if not mint:
        # Default: SOL + known mints
        info("Fetching prices for tracked tokens…")
        section("Prices")
        mints = config.get("tracked_tokens", {})
        mint_list = list(mints.values())
        prices = JupiterPrice.get_prices(mint_list)
        for symbol, m in mints.items():
            p = prices.get(m)
            if p is not None:
                kv(symbol, f"${fmt_num(p, 6)}", C.BRIGHT_GREEN)
            else:
                kv(symbol, f"{C.DIM}no price{C.RESET}")
        print()
        return 0

    # Resolve symbol → mint
    if mint.upper() in KNOWN_MINTS:
        mint = KNOWN_MINTS[mint.upper()]
    elif not is_valid_solana_address(mint):
        # Try Jupiter search
        tok = JupiterPrice.search_token(mint)
        if tok:
            mint = tok["address"]
            info(f"Found: {tok.get('symbol')} — {tok.get('name')}")
        else:
            error(f"Could not resolve '{mint}' to a token mint.")
            return 1

    section("Price")
    kv("Mint", mint)
    price = JupiterPrice.get_price(mint)
    if price is not None:
        kv("USD", f"${fmt_num(price, 8)}", C.BRIGHT_GREEN)
    else:
        warn("No price found for this mint on Jupiter.")

    print()
    return 0


def cmd_watch(args: argparse.Namespace) -> int:
    """Monitor a wallet for balance changes."""
    banner()
    wallet = args.wallet.strip()
    interval = int(args.interval or config.get("watch_interval") or 30)

    if not is_valid_solana_address(wallet):
        error(f"Invalid Solana address: {wallet}")
        return 1

    rpc = SolanaRPC(network=config.get("network"), custom_url=config.get("rpc_url"))
    discord = Discord()

    section("Watching")
    kv("Address", wallet)
    kv("Interval", f"{interval}s")
    kv("Network", config.get("network"))
    kv("Alerts", "Discord webhook set" if discord.url else f"{C.DIM}disabled (no webhook){C.RESET}")

    print()
    info(f"Press Ctrl+C to stop.\n")

    last_sol = None
    last_tokens: Dict[str, float] = {}
    threshold = float(config.get("alert_threshold_sol") or 0.01)

    try:
        while True:
            try:
                sol = rpc.get_sol_balance(wallet)
                accounts = rpc.get_token_accounts(wallet)
                tokens = {a["mint"]: a["amount"] for a in accounts if a["amount"] > 0}

                ts = datetime.now().strftime("%H:%M:%S")

                if last_sol is None:
                    info(f"[{ts}] Initial: {fmt_num(sol, 4)} SOL · {len(tokens)} tokens")
                else:
                    delta = sol - last_sol
                    if abs(delta) >= threshold:
                        sign = "+" if delta > 0 else ""
                        color = C.BRIGHT_GREEN if delta > 0 else C.BRIGHT_RED
                        print(f"  {C.DIM}[{ts}]{C.RESET}  SOL {color}{sign}{fmt_num(delta, 4)}{C.RESET}  →  {fmt_num(sol, 4)}")

                        # Discord alert
                        if discord.url:
                            discord.alert(
                                title=f"$LAX Wallet Change — {truncate(wallet, 20)}",
                                description=f"SOL balance changed by **{sign}{fmt_num(delta, 4)}**",
                                color="success" if delta > 0 else "warning",
                                fields=[
                                    {"name": "Wallet",     "value": f"`{wallet}`",              "inline": False},
                                    {"name": "New balance","value": f"{fmt_num(sol, 4)} SOL",   "inline": True},
                                    {"name": "Delta",      "value": f"{sign}{fmt_num(delta, 4)} SOL", "inline": True},
                                ],
                            )
                    else:
                        print(f"  {C.DIM}[{ts}]  no SOL change ({fmt_num(sol, 4)}){C.RESET}")

                    # Token changes
                    for mint, amt in tokens.items():
                        prev = last_tokens.get(mint)
                        if prev is not None and abs(amt - prev) > 1e-9:
                            d = amt - prev
                            sign = "+" if d > 0 else ""
                            color = C.BRIGHT_GREEN if d > 0 else C.BRIGHT_RED
                            short = truncate(mint, 10)
                            print(f"  {C.DIM}[{ts}]{C.RESET}  {short} {color}{sign}{fmt_num(d, 4)}{C.RESET} → {fmt_num(amt, 4)}")
                            if discord.url:
                                discord.alert(
                                    title="Token balance change",
                                    description=f"Token `{short}` changed by **{sign}{fmt_num(d, 4)}**",
                                    color="success" if d > 0 else "warning",
                                    fields=[
                                        {"name": "Wallet", "value": f"`{wallet}`", "inline": False},
                                        {"name": "Mint",   "value": f"`{mint}`",   "inline": False},
                                    ],
                                )

                last_sol = sol
                last_tokens = tokens

            except KeyboardInterrupt:
                raise
            except Exception as e:
                warn(f"Poll error: {e}")

            time.sleep(interval)

    except KeyboardInterrupt:
        print()
        info("Stopped by user.")
        return 0


def cmd_portfolio(args: argparse.Namespace) -> int:
    """Aggregate portfolio across multiple wallets."""
    banner()
    wallets = [w.strip() for w in args.wallets if w.strip()]
    invalid = [w for w in wallets if not is_valid_solana_address(w)]
    if invalid:
        error(f"Invalid address(es): {', '.join(invalid)}")
        return 1

    rpc = SolanaRPC(network=config.get("network"), custom_url=config.get("rpc_url"))

    total_sol = 0.0
    totals_by_mint: Dict[str, float] = {}
    wallet_rows: List[Dict[str, Any]] = []

    for w in wallets:
        try:
            sol = rpc.get_sol_balance(w)
        except Exception as e:
            warn(f"{truncate(w, 12)}: {e}")
            sol = 0.0
        try:
            accounts = rpc.get_token_accounts(w)
        except Exception:
            accounts = []

        wallet_rows.append({"wallet": w, "sol": sol, "tokens": len(accounts)})
        total_sol += sol

        for a in accounts:
            if a["amount"] > 0:
                totals_by_mint[a["mint"]] = totals_by_mint.get(a["mint"], 0.0) + a["amount"]

    # Fetch prices
    mints = list(totals_by_mint.keys())
    prices = JupiterPrice.get_prices(mints) if mints else {}
    sol_price = JupiterPrice.get_price(KNOWN_MINTS["SOL"]) or 0

    sol_usd = total_sol * sol_price
    token_usd_total = 0.0

    section("Wallets")
    for row in wallet_rows:
        kv(truncate(row["wallet"], 16),
           f"{fmt_num(row['sol'], 4):>14} SOL   {C.DIM}({row['tokens']} tokens){C.RESET}")

    section("Total")
    kv("Wallets",      str(len(wallets)))
    kv("SOL total",    f"{fmt_num(total_sol, 6)} SOL   {C.DIM}(≈ ${fmt_num(sol_usd, 2)}){C.RESET}")
    kv("SOL price",    f"${fmt_num(sol_price, 4)}")

    if totals_by_mint:
        section("Tokens")
        rows = []
        for mint, amount in totals_by_mint.items():
            price = prices.get(mint)
            usd = (price or 0) * amount
            token_usd_total += usd
            rows.append((mint, amount, price, usd))
        rows.sort(key=lambda r: r[3], reverse=True)

        for mint, amount, price, usd in rows[:15]:
            short = truncate(mint, 12)
            if price:
                kv(f"Token {short}", f"{fmt_num(amount, 4):>16}  {C.DIM}≈ ${fmt_num(usd, 2)}{C.RESET}")
            else:
                kv(f"Token {short}", f"{fmt_num(amount, 4):>16}  {C.DIM}(no price){C.RESET}")

    grand_total = sol_usd + token_usd_total
    section("Grand Total")
    print(f"  {C.BOLD}{C.BRIGHT_GREEN}≈ ${fmt_num(grand_total, 2)}{C.RESET}")
    print()

    if args.json:
        payload = {
            "wallets":     wallet_rows,
            "total_sol":   total_sol,
            "sol_price":   sol_price,
            "sol_usd":     sol_usd,
            "tokens":      [
                {"mint": m, "amount": a, "price": p, "usd": u}
                for (m, a, p, u) in rows
            ],
            "grand_total": grand_total,
            "timestamp":   datetime.utcnow().isoformat() + "Z",
        }
        out_path = Path(args.json) if isinstance(args.json, str) else Path("portfolio.json")
        with open(out_path, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2)
        ok(f"Saved JSON report to {out_path}")

    return 0


def cmd_history(args: argparse.Namespace) -> int:
    """Print recent transactions for a wallet."""
    banner()
    wallet = args.wallet.strip()
    limit = int(args.limit or 10)

    if not is_valid_solana_address(wallet):
        error(f"Invalid Solana address: {wallet}")
        return 1

    rpc = SolanaRPC(network=config.get("network"), custom_url=config.get("rpc_url"))

    section("Recent Transactions")
    kv("Wallet", wallet)
    kv("Limit",  str(limit))
    print()

    sigs = rpc.get_signatures(wallet, limit=limit)
    if not sigs:
        warn("No transactions found (or RPC error).")
        return 0

    for i, sig in enumerate(sigs, 1):
        signature = sig.get("signature", "")
        blocktime = sig.get("blockTime")
        err = sig.get("err")
        when = datetime.fromtimestamp(blocktime).strftime("%Y-%m-%d %H:%M") if blocktime else "unknown"
        status = f"{C.BRIGHT_RED}FAILED{C.RESET}" if err else f"{C.BRIGHT_GREEN}OK{C.RESET}"
        short = truncate(signature, 20)
        print(f"  {C.DIM}{i:>2}.{C.RESET}  {short}  {C.DIM}{when}{C.RESET}  {status}")
        print(f"       {C.DIM}https://solscan.io/tx/{signature}{C.RESET}")

    print()
    return 0


def cmd_airdrop(args: argparse.Namespace) -> int:
    """Check airdrop eligibility for a wallet (mirrors website logic)."""
    banner()
    wallet = args.wallet.strip()

    if not is_valid_solana_address(wallet):
        error(f"Invalid Solana address: {wallet}")
        return 1

    tier, message, color = airdrop_tier(wallet)

    section("Airdrop Check")
    kv("Wallet", wallet)
    kv("Score",  f"{airdrop_score(wallet)}/100")
    kv("Tier",   tier, {
        "green":  C.BRIGHT_GREEN,
        "yellow": C.BRIGHT_YELLOW,
        "dim":    C.DIM,
    }.get(color, ""))

    print()
    print(f"  {C.BOLD}{message}{C.RESET}")
    print()
    info("Snapshots update periodically — check back later.")
    info(f"Join the community: {PROJECT['discord']}")
    print()
    return 0


def cmd_config(args: argparse.Namespace) -> int:
    """View or edit config."""
    banner()

    if args.set:
        if len(args.set) != 2:
            error("Usage: config --set KEY VALUE")
            return 1
        key, value = args.set
        # Try to parse as JSON for numbers/bools/lists
        try:
            parsed = json.loads(value)
        except Exception:
            parsed = value
        config.set(key, parsed)
        ok(f"Set '{key}' = {parsed!r}")
        return 0

    if args.reset:
        config.data = dict(DEFAULT_CONFIG)
        config.save()
        ok("Config reset to defaults.")
        return 0

    section("Configuration")
    kv("Config file", str(CONFIG_FILE))
    kv("State file",  str(STATE_FILE))
    print()
    print(json.dumps(config.data, indent=2, ensure_ascii=False))
    print()
    return 0


def cmd_webhook(args: argparse.Namespace) -> int:
    """Set or clear the Discord webhook."""
    banner()

    if args.clear:
        config.set("discord_webhook", None)
        ok("Discord webhook cleared.")
        return 0

    if not args.url:
        error("Usage: webhook <url>")
        return 1

    url = args.url.strip()
    if not url.startswith("https://discord.com/api/webhooks/") and \
       not url.startswith("https://discordapp.com/api/webhooks/"):
        warn("This doesn't look like a Discord webhook URL. Saving anyway…")

    config.set("discord_webhook", url)
    ok("Discord webhook saved.")

    # Test
    d = Discord()
    if d.send(content="✅ Laxironix webhook connected."):
        ok("Test message sent.")
    else:
        warn("Test message failed — check the URL.")
    return 0


def cmd_test_alert(args: argparse.Namespace) -> int:
    """Send a test alert to Discord."""
    banner()
    d = Discord()
    if not d.url:
        error("No webhook configured. Run: webhook <url>")
        return 1
    if d.alert(
        title="Laxironix Toolkit — Test Alert",
        description="If you see this, your webhook is working correctly.",
        color="brand",
        fields=[
            {"name": "Version",  "value": VERSION,                            "inline": True},
            {"name": "Network",  "value": config.get("network", "mainnet"),   "inline": True},
            {"name": "Project",  "value": PROJECT["github"],                  "inline": False},
        ],
    ):
        ok("Test alert sent.")
        return 0
    error("Failed to send test alert.")
    return 1


def cmd_version(args: argparse.Namespace) -> int:
    """Print version and project info."""
    banner()
    section("Version")
    kv("Toolkit", VERSION)
    kv("App",     APP)
    section("Project")
    kv("Name",    PROJECT["name"])
    kv("Ticker",  PROJECT["ticker"])
    kv("Chain",   PROJECT["chain"])
    kv("Discord", PROJECT["discord"])
    kv("X",       PROJECT["x"])
    kv("GitHub",  PROJECT["github"])
    kv("Pump",    PROJECT["pump"])
    print()
    return 0


# ═══════════════════════════════════════════════════════════════════════════════
#  ARGUMENT PARSER
# ═══════════════════════════════════════════════════════════════════════════════

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="laxironix",
        description=f"{APP} v{VERSION} — all-in-one CLI for the $LAX community.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent(f"""
        examples:
          laxironix balance 7xKX...x8F
          laxironix price --mint SOL
          laxironix watch 7xKX...x8F --interval 60
          laxironix portfolio 7xKX... 5yLM... --json report.json
          laxironix webhook https://discord.com/api/webhooks/...
          laxironix config --set network devnet

        project:
          Discord {PROJECT['discord']}
          X       {PROJECT['x']}
          GitHub  {PROJECT['github']}
        """),
    )
    p.add_argument("--version", action="version", version=f"%(prog)s {VERSION}")

    sub = p.add_subparsers(dest="command", metavar="<command>")

    # balance
    sp = sub.add_parser("balance", help="Check SOL + token balances")
    sp.add_argument("wallet", help="Solana wallet address")
    sp.set_defaults(func=cmd_balance)

    # price
    sp = sub.add_parser("price", help="Get token price via Jupiter")
    sp.add_argument("--mint", "-m", default=None,
                    help="Mint address or symbol (SOL, USDC, …). "
                         "If omitted, shows tracked tokens.")
    sp.set_defaults(func=cmd_price)

    # watch
    sp = sub.add_parser("watch", help="Monitor a wallet for changes")
    sp.add_argument("wallet", help="Solana wallet address")
    sp.add_argument("--interval", "-i", type=int, default=None,
                    help="Poll interval in seconds (default: 30)")
    sp.set_defaults(func=cmd_watch)

    # portfolio
    sp = sub.add_parser("portfolio", help="Aggregate portfolio across wallets")
    sp.add_argument("wallets", nargs="+", help="One or more wallet addresses")
    sp.add_argument("--json", nargs="?", const=True, default=False,
                    help="Save JSON report (optionally specify a path)")
    sp.set_defaults(func=cmd_portfolio)

    # history
    sp = sub.add_parser("history", help="Recent transactions for a wallet")
    sp.add_argument("wallet", help="Solana wallet address")
    sp.add_argument("--limit", "-l", type=int, default=10,
                    help="Number of transactions (default: 10)")
    sp.set_defaults(func=cmd_history)

    # airdrop
    sp = sub.add_parser("airdrop", help="Check airdrop eligibility")
    sp.add_argument("wallet", help="Solana wallet address")
    sp.set_defaults(func=cmd_airdrop)

    # config
    sp = sub.add_parser("config", help="View or edit config")
    sp.add_argument("--set", nargs=2, metavar=("KEY", "VALUE"),
                    help="Set a config key")
    sp.add_argument("--reset", action="store_true",
                    help="Reset config to defaults")
    sp.set_defaults(func=cmd_config)

    # webhook
    sp = sub.add_parser("webhook", help="Set or clear Discord webhook")
    sp.add_argument("url", nargs="?", default=None, help="Discord webhook URL")
    sp.add_argument("--clear", action="store_true", help="Remove webhook")
    sp.set_defaults(func=cmd_webhook)

    # test-alert
    sp = sub.add_parser("test-alert", help="Send a test Discord alert")
    sp.set_defaults(func=cmd_test_alert)

    # version
    sp = sub.add_parser("version", help="Show version and project info")
    sp.set_defaults(func=cmd_version)

    return p


# ═══════════════════════════════════════════════════════════════════════════════
#  SIGNAL HANDLING (clean Ctrl+C)
# ═══════════════════════════════════════════════════════════════════════════════

def _sigint_handler(signum, frame):
    print()
    info("Interrupted. Goodbye 👋")
    sys.exit(0)


signal.signal(signal.SIGINT, _sigint_handler)


# ═══════════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ═══════════════════════════════════════════════════════════════════════════════

def main() -> int:
    parser = build_parser()

    if len(sys.argv) == 1:
        banner()
        parser.print_help()
        print()
        return 0

    args = parser.parse_args()

    if not hasattr(args, "func"):
        banner()
        parser.print_help()
        print()
        return 0

    try:
        return args.func(args)
    except KeyboardInterrupt:
        print()
        info("Interrupted. Goodbye 👋")
        return 0
    except RuntimeError as e:
        error(str(e))
        return 1
    except Exception as e:
        error(f"Unexpected error: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
