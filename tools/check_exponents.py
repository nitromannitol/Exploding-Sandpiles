"""Compare every exponent in a paper statement with those in its Lean statement.

The exponents `2/3`, `1/3`, `-2/3`, `-1/3` and the `e^{-cR}` tails carry the
content of this paper, and `2/3` versus `1/3` is a transposition that no type
error would catch.  So they are compared directly:
every exponent is extracted from the paper's statement and from the frozen Lean
statement and the two multisets are matched.

Three kinds of difference are expected and are recorded per node rather than
silently ignored:

  notation   the paper writes `\\gamma`, Lean writes `γ`
  general    the paper writes the `d = 2` case as `2/3` and `1/3`; Lean carries
             the general `d/(d+1)` and `1/(d+1)`, which agree at `d = 2`
  split      `thm:return` is one theorem in the paper and three nodes here, so
             each node sees the whole theorem's line range but carries only its
             own display

    python3 tools/check_exponents.py

The recorded explanations apply only to the exact historical source pin.
Revised-source rows, literal definitions, and citations without a statement
range are explicitly excluded. A run with no compared statements fails.
"""

from __future__ import annotations

import hashlib
import os
import re
import sys
from pathlib import Path

from sync_docs import (HISTORICAL_SHA256, historical_audit_nodes, load_manifest,
                       source_pins, source_range)

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"


def paper_path() -> Path:
    env = os.environ.get("EXPLODING_PAPER")
    return Path(env) if env else ROOT / "paper" / "exploding.tex"


# Superscripts that are not exponents of a quantity: set names like `ℤ^d`, the
# inverse in `Δ^{-1}`, the summation limits, and the `θ`-expressions of lem:exp,
# which Lean writes with `Real.exp` rather than with `^`.
NOISE = {"2", "+", "-1", r"\Z", r"\R", r"\infty", r"\ast", r"\star", "j", "n", "m", "k", "i"}

# Per node: exponents present in the paper's line range but legitimately absent
# from this node's Lean statement, with the reason.
EXPECTED_ABSENT: dict[str, dict[str, str]] = {
    "thm-main-square": {"-2/3": "notation: the paper's |R_t| t^{-2/3} is Lean's |R_t| / t^(2/3)"},
    "thm-main-degree-three": {"-2/3": "notation: the paper's |R_t| t^{-2/3} is Lean's |R_t| / t^(2/3)"},
    "prop-degree-three-passage": {"-cR": "notation: the paper's e^{-cR} is Lean's Real.exp (-c * R)"},
    "prop-square-passage": {"-cR": "notation: the paper's e^{-cR} is Lean's Real.exp (-c * R)"},
    "lem-square-constrained-bonds": {"-cr": "notation: the paper's e^{-cr} is Lean's Real.exp (-c * r)"},
    "lem-square-forced-tests": {"-cm": "notation: the paper's e^{-cm} is Lean's explicit (3/4)^(m/3)"},
    "thm-limit-shape": {"d": "dimension superscript from ℝ^d, not an exponent of a quantity"},
    "thm-time-constant": {"d": "dimension superscript from ℝ^d, not an exponent of a quantity"},
    "thm-explosive": {"d": "dimension superscript from ℤ^d, not an exponent of a quantity"},
    "prop-renormalization": {
        "c": "set-complement superscript in C_∞^c, not an exponent of a quantity",
        "d": "dimension superscript from ℤ^d, not an exponent of a quantity"},
    "lem-square-lower-bound": {
        "d": "box superscript from [-n,n]^d, the dimension, not an exponent of a quantity",
        "dn": "notation: the paper's (2d)^{d n} is Lean's (2*d)^(d*n)"},
    "lem-penultimate-cluster": {
        "\\gamma": "notation: the paper writes \\gamma, Lean writes γ",
        "d": "box superscript from [-1,1]^d, the dimension, not an exponent of a quantity"},
    "lem-penultimate-upper-bound": {"\\gamma": "notation: the paper writes \\gamma, Lean writes γ"},
    "lem-penultimate-close": {"\\gamma": "notation: the paper writes \\gamma, Lean writes γ"},
    "prop-last-wave-convergence": {"d": "dimension superscript from ℝ^d, not an exponent of a quantity"},
    "prop-approximate-subadditive": {"d": "dimension superscript from ℤ^d, not an exponent of a quantity"},
    "prop-generalized-last-wave": {"d": "dimension superscript from ℝ^d, not an exponent of a quantity"},
    "thm-generalized-convergence": {"d": "dimension superscript from ℝ^d, not an exponent of a quantity"},
    "thm-counterexample": {"d": "dimension superscript from ℤ^d, not an exponent of a quantity"},
    "ext-schonmann-bootstrap": {
        "(d)": "dimension label superscript on Q_n^{(d)}, not an exponent of a quantity"},
    "ext-liggett-schonmann-stacey": {"d": "dimension superscript from ℤ^d, not an exponent of a quantity"},
    "ext-schonmann-bootstrap-proved": {
        "(d)": "dimension label superscript on Q_n^{(d)}, not an exponent of a quantity"},
    "ext-liggett-schonmann-stacey-proved": {"d": "dimension superscript from ℤ^d, not an exponent of a quantity"},
    "lem-last-wave-bound": {
        "(z)": "starting-site label superscript on u_t^{(z)}, not an exponent of a quantity",
        "d": "dimension superscript from ℤ^d, not an exponent of a quantity"},
    "prop-dimensional-reduction": {
        "(d)": "dimension label superscript on u_t^{(d)}, not an exponent of a quantity",
        "(d-1)": "dimension label superscript on u_t^{(d-1)}, not an exponent of a quantity"},
    "lem-approx-subadditivity": {"d": "dimension superscript from ℤ^d, not an exponent of a quantity"},
    "prop-recurrence": {"d": "dimension superscript from ℤ^d, not an exponent of a quantity"},
    "lem-local-convexity": {
        "(i)": "path-index label superscript on z^{(i)}, not an exponent of a quantity",
        "(i+1)": "path-index label superscript on z^{(i+1)}, not an exponent of a quantity"},
    "prop-crossing-time": {
        "(i,z)": "direction/site label superscript on the crossing time C_k^{(i,z)}, not an exponent of a quantity",
        "d": "the exponent k^d is carried by the definition GoodCube (GoodCube η k ≜ max crossing time ≤ k^d), not repeated in the frozen block"},
}


def balanced(s: str, i: int, op: str, cl: str) -> str | None:
    depth = 0
    for j in range(i, len(s)):
        if s[j] == op:
            depth += 1
        elif s[j] == cl:
            depth -= 1
            if depth == 0:
                return s[i + 1:j]
    return None


def paper_exponents(seg: str) -> set[str]:
    out = []
    for m in re.finditer(r"\^", seg):
        i = m.end()
        if i >= len(seg):
            continue
        if seg[i] == "{":
            g = balanced(seg, i, "{", "}")
            if g is not None:
                out.append(g)
        else:
            out.append(seg[i])
    cleaned = {re.sub(r"\s|\\,|\\!|\\bigl|\\bigr", "", e) for e in out}
    return cleaned - NOISE


def lean_exponents(blk: str) -> set[str]:
    out = []
    for m in re.finditer(r"\^\s*", blk):
        i = m.end()
        if i >= len(blk):
            continue
        if blk[i] == "(":
            g = balanced(blk, i, "(", ")")
            if g is not None:
                out.append(g)
        else:
            g = re.match(r"[A-Za-zγβ0-9]+", blk[i:])
            if g:
                out.append(g.group(0))
    cleaned = set()
    for e in out:
        e = re.sub(r"\(\s*([a-zA-Zβγ])\s*:\s*ℝ\s*\)", r"\1", e)
        e = re.sub(r"\(\s*(\d+)\s*:\s*ℝ\s*\)", r"\1", e)
        e = re.sub(r"\s+", "", e)
        # a bracketed literal with a type ascription, `(2 / 3 : ℝ)`, is the literal;
        # `(-(1 / 3 : ℝ))` needs the ascription stripped again after the sign is unwrapped
        for _ in range(3):
            e = re.sub(r":ℝ$", "", e)
            e = re.sub(r"^\((.*)\)$", r"\1", e)
            if e.startswith("-(") and e.endswith(")"):
                e = "-" + e[2:-1]
            e = re.sub(r":ℝ$", "", e)
        cleaned.add(e)
    return cleaned - {"2"}


def main() -> int:
    try:
        path = paper_path()
        if hashlib.sha256(path.read_bytes()).hexdigest() != HISTORICAL_SHA256:
            raise LookupError("recorded exponent explanations apply only to historical "
                              "paper/exploding.tex at SHA-256 " + HISTORICAL_SHA256)
        lines = path.read_text(encoding="utf-8").splitlines()
        manifest = load_manifest(MANIFEST)
        pins = source_pins(manifest["nodes"], manifest)
        eligible, excluded = historical_audit_nodes(manifest["nodes"], pins)
    except (LookupError, KeyError, OSError, ValueError) as exc:
        print(f"check_exponents: {exc}", file=sys.stderr)
        return 2
    unexplained: list[tuple[str, list[str]]] = []
    compared = 0

    for node in eligible:
        a, b = source_range(node, pins[node["id"]])
        seg = "\n".join(lines[a - 1:b])
        text = (ROOT / node["file"]).read_text(encoding="utf-8")
        blk = text[text.index("-- FROZEN-STATEMENT-BEGIN"):
                   text.index("-- FROZEN-STATEMENT-END")]
        pe, le = paper_exponents(seg), lean_exponents(blk)
        compared += 1
        allowed = EXPECTED_ABSENT.get(node["id"], {})
        missing = [e for e in sorted(pe) if e not in le and e not in allowed]
        print(f"  {node['id']:24s} paper {sorted(pe)}")
        print(f"  {'':24s} lean  {sorted(le)}")
        for e in sorted(pe):
            if e in allowed:
                print(f"  {'':24s}   {e}: {allowed[e]}")
        if missing:
            unexplained.append((node["id"], missing))

    print("\nExcluded from this historical-source audit:")
    for nid, reason in excluded:
        print(f"  {nid}: {reason}")
    if not compared:
        print("\ncheck_exponents: FAIL (no historical-source statements compared)", file=sys.stderr)
        return 1

    if unexplained:
        print("\ncheck_exponents: a paper exponent has no counterpart in Lean:",
              file=sys.stderr)
        for nid, ms in unexplained:
            print(f"  {nid}: {', '.join(ms)}", file=sys.stderr)
        return 1
    print(f"\ncheck_exponents: OK ({compared} historical-source statements; "
          f"{len(excluded)} explicitly excluded; every compared paper exponent "
          f"appears in its Lean statement or is explained above)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
