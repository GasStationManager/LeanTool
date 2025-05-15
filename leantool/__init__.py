"""LeanTool public API.

This lightweight shim just re-exports the helper routines implemented in
`leanmcp.py` so that external callers can do

    import leantool
    leantool.check_lean_code(...)

without importing from private modules.
"""

from __future__ import annotations

from typing import Any, Dict

__all__ = ["check_lean_code"]


def check_lean_code(code: str, json_output: bool = False) -> Dict[str, Any]:
    """Lazy-import implementation from ``leanmcp`` to avoid circular deps."""

    from leanmcp import check_lean_code as impl  # type: ignore  # local import

    return impl(code, json_output)
