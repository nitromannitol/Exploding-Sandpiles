"""Check that every constant depends only on the dimension.

A constant of the paper (a real number whose existence a statement asserts) may
depend on the dimension and on the parameters the statement fixes before it, such
as `p`, but not on the scale, time or site variables that come after it.  In Lean
that is a property of quantifier order: the existential must be bound before those
variables.  Writing

    theorem foo {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : ∃ c : ℝ, ... n ...

reads as `∀ n, ∃ c(n)`, which lets the constant absorb any function of `n` and
makes a rate decorative.  That is a silent weakening, invisible to every other
check here, so it gets its own.

The rule enforced: in a frozen statement that binds a real-valued existential,
none of the names in `FORBIDDEN` may be a *parameter* of the theorem; they must
be quantified inside the conclusion, after the existential.  A statement in which
such a name is a parameter by the paper's own standing assumption is listed in
`REVIEWED` with the reason.

    python3 tools/check_constants.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_constants.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"

# Names that must never be theorem parameters when a constant is existential.
FORBIDDEN = ("R", "n", "t", "m", "r", "s", "L", "x", "y", "u", "v", "e", "z", "ε", "η", "δ")

# Statements read against the paper where a forbidden name is a parameter by the
# paper's own standing assumption, with the reason recorded.  A statement whose
# existential is an honest constant of the paper (`∃ c ∀ n`) is never listed here.
REVIEWED: dict[str, dict[str, str]] = {
}

# Only a real-valued existential is a *constant*; an existential over sets, sites
# or natural numbers may depend on the variables bound before it.
CONSTANT = re.compile(r"∃\s+[^,:]*:\s*ℝ")


def split_statement(block: str) -> tuple[str, str]:
    """(binders, conclusion), split at the FIRST `:` outside every bracket.

    Every theorem parameter is bracketed, so its own `:` sits at depth one or
    more; the first `:` at depth zero is the one that ends the binder list.
    Taking the last such `:` instead would cut inside `∃ c : ℝ` and hide the
    existential in the binders, which is precisely the thing being looked for."""
    depth = 0
    for i, ch in enumerate(block):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and not block.startswith(":=", i):
            return block[:i], block[i + 1:]
    return block, ""


def parameters(binders: str) -> set[str]:
    """Variable names bound as theorem parameters."""
    names: set[str] = set()
    for m in re.finditer(r"[({\[]([^:()\[\]{}]+):", binders):
        for tok in m.group(1).split():
            names.add(tok)
    return names


def main() -> int:
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    bad, ok = [], 0
    print(f"{'node':28s} {'real constant?':15s} {'bad parameters':22s}")
    for node in manifest.get("nodes") or []:
        text = (ROOT / node["file"]).read_text(encoding="utf-8")
        blk = text[text.index("-- FROZEN-STATEMENT-BEGIN") + len("-- FROZEN-STATEMENT-BEGIN"):
                   text.index("-- FROZEN-STATEMENT-END")]
        binders, concl = split_statement(blk)
        has_exists = bool(CONSTANT.search(concl))
        params = parameters(binders)
        offenders = sorted(params & set(FORBIDDEN))
        reviewed = REVIEWED.get(node["id"], {})
        for name in sorted(set(offenders) & set(reviewed)):
            print(f"  {node['id']:26s} reviewed {name}: {reviewed[name]}")
        offenders = [o for o in offenders if o not in reviewed]
        mark = ""
        if has_exists and offenders:
            bad.append((node["id"], offenders))
            mark = "  <-- CONSTANT MAY DEPEND ON " + ", ".join(offenders)
        else:
            ok += 1
        print(f"  {node['id']:26s} {'yes' if has_exists else 'no':13s} "
              f"{', '.join(offenders) if offenders else '-':20s}{mark}")

    if bad:
        print("\ncheck_constants: a constant is bound after a quantity it must not "
              "depend on:", file=sys.stderr)
        for nid, off in bad:
            print(f"  {nid}: move {', '.join(off)} inside the existential", file=sys.stderr)
        return 1
    print(f"\ncheck_constants: OK ({ok} statements; every existential constant is "
          f"bound before every paper parameter, so it is a genuine constant)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
