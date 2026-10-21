"""Shared reporting helpers for the experiment scripts."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

DISCLAIMER = "Illustrations and exact arithmetic checks only; they are not proofs."


@dataclass(frozen=True)
class Check:
    """One named check: ``ok`` records whether it passed, ``detail`` the numbers behind it."""

    name: str
    ok: bool
    detail: str = ""


def print_report(title: str, checks: Sequence[Check]) -> int:
    """Print a short report and return a process exit code (0 when every check passed)."""
    print(title)
    print("=" * len(title))
    for check in checks:
        status = "ok  " if check.ok else "FAIL"
        suffix = f": {check.detail}" if check.detail else ""
        print(f"[{status}] {check.name}{suffix}")
    passed = sum(check.ok for check in checks)
    print(f"{passed}/{len(checks)} checks passed. {DISCLAIMER}")
    return 0 if passed == len(checks) else 1
