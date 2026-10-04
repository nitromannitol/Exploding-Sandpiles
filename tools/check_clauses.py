"""Compare how much each paper statement asserts with how much its Lean node does.

Every other checker here compares a statement with *itself*: the hash pins the
bytes, the axiom check pins the proof.  None of them notices when a frozen
statement quietly asserts less than the paper statement it claims to transcribe.
That is how, in the ORRW formalization this tooling comes from, `lem:schur`
came to be frozen without one of the three displays its paper statement
asserts, while every other gate passed.

This counts assertion units on each side and reports the pairs where the paper
asserts more:

  paper   displayed equations and enumerated items inside the statement
  Lean    top-level conjuncts of the frozen statement's conclusion

The counts are a heuristic, not a proof of correspondence: one Lean conjunct can
faithfully carry two paper displays, and one paper display can need three Lean
conjuncts.  So a mismatch is a prompt to look, not a verdict, and every node is
listed with its counts so the reader can judge.  Nodes whose `source` names no
paper label are skipped: they have no paper statement to compare against.

    python3 tools/check_clauses.py            # report
    python3 tools/check_clauses.py --strict   # exit 1 if any node is unreviewed
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_clauses.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"

# Nodes whose count mismatch has been looked at and explained.  The value is the
# reason, which is printed, so a stale entry is visible rather than silent.
# Every node with a paper statement must appear here, with a sentence saying
# what the paper asserts and what the Lean statement asserts.  The counts below
# are advisory -- a regex cannot decide correspondence -- so the guarantee this
# file gives is the weaker but honest one: every statement has been read against
# the paper and the reading is written down.  A node missing from this table
# fails the check.
REVIEWED: dict[str, str] = {
    "thm-limit-shape":
        "one display (the positive set converges in measure to a convex domain B(p)); "
        "the Tendsto/symmDiff conjunct is that assertion, and Convex/IsOpen/Nonempty "
        "render the paper's 'convex domain'",
    "thm-time-constant":
        "one prose assertion (rescaled arrival times converge locally uniformly to a "
        "continuous, convex, one-homogeneous N_p); Lean carries Continuous, ConvexOn, "
        "one-homogeneity and the ε-N convergence, and adds Explosive and finiteness of "
        "arrival on the a.s. event (triage: benign explicit rendering)",
    "thm-explosive":
        "one assertion (a.s. explosiveness under β ≥ d and positive mass at 2d−1); "
        "hlow and hhit render the two hypotheses, and the SchonmannBootstrap external "
        "is the paper's proof input carried explicitly",
    "prop-renormalization":
        "three enumerated items under the opening 'constants c, C on an event of "
        "probability 1'; the count 5 is the three items plus the two relations of item "
        "3's two-sided display, while Lean carries them as three conjuncts (Cinf; "
        "component volume < (log n)^{5/2}; c|x−y| ≤ m ≤ C|x−y|), so its two-sided bound "
        "is one conjunct",
    "lem-square-lower-bound":
        "one assertion (the m-wave support contains [-n,n]^d), rendered as a "
        "positive-time hit for every site of the cube; η ≥ 0 and n ≥ 1 are the paper's "
        "hypotheses and m ≥ (2d)^{dn} the threshold",
    "lem-penultimate-cluster":
        "one display (P(x) ⊂ x + [−(log n)^γ, (log n)^γ]^d); Lean states the same "
        "coordinatewise bound |y i − x i| ≤ (log n)^γ",
    "lem-penultimate-upper-bound":
        "one display (T̂(x) ≤ C|x| + (log n)^γ); Lean splits it into the finiteness "
        "witness lastArrival = m and the inequality m ≤ C|x| + (log n)^γ",
    "lem-penultimate-close":
        "one display with a two-sided chain (T̂(x) ≤ T̃(x) ≤ T̂(x) + (log n)^γ); Lean "
        "carries lastArrival ≤ clusterArrival and the finiteness witnesses a, b with "
        "the upper bound",
    "prop-last-wave-convergence":
        "one prose assertion (rescaled last-wave arrival times converge locally "
        "uniformly to a continuous, convex, one-homogeneous N); Lean carries Continuous, "
        "ConvexOn, one-homogeneity and the ε-N convergence, and adds finiteness of "
        "lastArrival on the a.s. event",
    "prop-approximate-subadditive":
        "two displays (T(x) ≤ T̂(x) + C₁(η) and T̂(x) ≤ T(x) + C₂(η)); the two Lean "
        "conjuncts are exactly these, with finite constants C₁, C₂ : ℕ",
    "prop-generalized-last-wave":
        "one prose assertion (η is explosive and n^{-1}T̂([nx]) converges locally "
        "uniformly to a deterministic continuous convex one-homogeneous N_η); Lean "
        "carries the three named hypotheses as h1/h3/h4 plus the stationarity, "
        "ergodicity and support assumptions, and the registered External inputs",
    "thm-counterexample":
        "two displays (limsup ≥ 3/2 and liminf = 1) plus the prose 'explosive "
        "backgrounds η not ≥ (2d−2) failing to have a limit shape'; Lean carries the "
        "two limits as conjuncts and spells out Explosive, the failure of η ≥ 2d−2 "
        "and finiteness of the arrival times",
    "prop-explosion-criteria":
        "one prose assertion (finite range of dependence plus box-crossing plus "
        "recurrence implies explosiveness); Lean states it as FiniteRangeOfDependence "
        "→ BoxCrossingHyp → RecurrentLaw → ExplosiveLaw",
    "ext-fey-levine-peres":
        "one assertion (p > 0 implies a.s. explosiveness); the Lean def carries p < 1 "
        "as the toy-model range",
    "ext-schonmann-bootstrap":
        "one inequality display (P(Q_n^(d) is η'-internally spanned) ≥ 1 − c e^{−Cn}), "
        "with the two-line cases definition of η' counted as the extra relation; Lean "
        "carries the inequality as ofReal(1 − c e^{−Cn}) ≤ productLaw d (2d) d p "
        "{InternallySpanned η n}",
    "lem-last-wave-bound":
        "one display (u_t^{(z)}(x) ≤ 1 + ũ^{(z)}(x)); the first sentence is its case "
        "'outside the penultimate cluster', where penultimateWave vanishes "
        "(triage: faithful)",
    "prop-dimensional-reduction":
        "two displays (the odometer equality and the sandpile equality under "
        "u_t^{(d)} = 0); the count 3 is the two displays plus the condition on the "
        "second, and Lean's second conjunct carries that condition as an implication "
        "hypothesis",
    "lem-approx-subadditivity":
        "one display (T̃(a,z) ≤ T̃(a,b) + T̃(b,z)); the Lean conjunct is the same "
        "inequality for clusterArrival",
    "prop-recurrence":
        "one assertion (η ≡ d is recurrent for every d ≥ 1); Lean states Recurrent "
        "(fun _ => d)",
    "lem-local-convexity":
        "one assertion (w_t|_{br(A)} = 1 for all t ≥ |br(A)|); Lean carries it as "
        "fodo A η (indicator A 1) t x = 1, with hlow/hhigh the model's standing range "
        "(triage) and the finite-path and initial-condition hypotheses explicit",
    "lem-finite-exploding":
        "the paper asserts the last wave is well-defined as M̂_η(0) < ∞; Lean asserts "
        "the existence half, ∀ᵐη ∃ n ≥ 1, ¬ WaveStabilizable η n 0, and not the "
        "finiteness of M̂ (flagged: partial transcription, triage)",
    "prop-crossing-time":
        "one display (max_{i,z} C_k^{(i,z)} ≤ k^d with probability ≥ 1 − δ); Lean's "
        "measure conjunct GoodCube η k unpacks to ∀ i z ∈ closureN, crossingTime ≤ k^d "
        "(so the k^d exponent lives in the definition), and 1 ≤ k is made explicit",
}

# Nodes known from hand reading to assert strictly less than their paper
# statement, which the count heuristic misses when the missing assertion is not
# a displayed relation.  Like the heuristic flags, these are printed and
# explained but do not fail the check; only `unreviewed` does.
FLAGGED: set[str] = {
    "lem-finite-exploding",
}


def paper_path() -> Path:
    """The paper: the copy pinned in this repository, or `$EXPLODING_PAPER`."""
    env = os.environ.get("EXPLODING_PAPER")
    return Path(env) if env else ROOT / "paper" / "exploding.tex"


RELATION = re.compile(r"\\leq|\\geq|\\neq|\\subseteq|(?<!\\not)\\in\b|<|>|=")


def paper_units(segment: str) -> int:
    """Assertions in a statement: relations inside displays, plus enumerated items.

    Counting displays alone undercounts, because the paper often puts three
    assertions in one display separated by `\\qquad` -- `lem:max-exit` does.
    Counting relation symbols inside displayed math tracks the real number of
    things asserted.  `\\coloneqq` is a definition, not an assertion, and is not
    counted; nor is anything outside a display."""
    body = []
    for m in re.finditer(r"\\begin\{(?:equation|align|gather)\*?\}(.*?)\\end\{(?:equation|align|gather)\*?\}",
                         segment, re.S):
        body.append(m.group(1))
    for m in re.finditer(r"(?<!\\)\\\[(.*?)(?<!\\)\\\]", segment, re.S):
        body.append(m.group(1))
    n = 0
    for b in body:
        b = re.sub(r"\\text\{[^}]*\}", " ", b)
        b = b.replace("\\coloneqq", " ").replace("\\colon", " ")
        b = re.sub(r"\\begin\{cases\}.*?\\end\{cases\}", " ", b, flags=re.S)
        n += len(RELATION.findall(b))
    n += len(re.findall(r"\\item\b", segment))
    return max(n, 1) if body or "\\item" in segment else 0


def lean_conjuncts(block: str) -> int:
    """Top-level `∧` of the conclusion.

    The conclusion begins after the last `:` that sits at bracket depth zero:
    every binder is inside `(`, `{` or `[`, so its own `:` is at depth one or
    more.  Conjuncts are then the depth-zero `∧` after that point."""
    depth, last_colon = 0, None
    for i, ch in enumerate(block):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and not block.startswith(":=", i):
            last_colon = i
    concl = block[last_colon + 1:] if last_colon is not None else block
    depth, n = 0, 1
    for ch in concl:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == "∧" and depth == 0:
            n += 1
    return n


def main() -> int:
    strict = "--strict" in sys.argv[1:]
    lines = paper_path().read_text(encoding="utf-8").splitlines()
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))

    rows, flagged, unreviewed = [], [], []
    for node in manifest.get("nodes") or []:
        src = node["source"]
        rng = re.search(rf"{re.escape(paper_path().name)}:(\d+)-(\d+)", src)
        lab = re.search(r"label ([A-Za-z][A-Za-z0-9:_-]*)", src)
        if not (rng and lab):
            continue
        a, b = int(rng.group(1)), int(rng.group(2))
        segment = "\n".join(lines[a - 1:b])
        text = (ROOT / node["file"]).read_text(encoding="utf-8")
        blk = text[text.index("-- FROZEN-STATEMENT-BEGIN"):text.index("-- FROZEN-STATEMENT-END")]
        p, l = paper_units(segment), lean_conjuncts(blk)
        rows.append((node["id"], lab.group(1), p, l))
        if p > l or node["id"] in FLAGGED:
            flagged.append(node["id"])
        if node["id"] not in REVIEWED:
            unreviewed.append(node["id"])

    print(f"{'node':26s} {'label':22s} paper  lean")
    for nid, lab, p, l in rows:
        mark = "  <-- paper asserts more" if nid in flagged else ""
        print(f"  {nid:24s} {lab:22s} {p:5d} {l:5d}{mark}")

    print("\nRecorded correspondence, one line per statement:")
    for nid, _, _, _ in rows:
        print(f"  {nid}: {REVIEWED.get(nid, 'NOT REVIEWED')}")

    if unreviewed:
        print(f"\ncheck_clauses: {len(unreviewed)} statement(s) have no recorded "
              f"correspondence: {', '.join(unreviewed)}", file=sys.stderr)
        return 1
    print(f"\ncheck_clauses: OK ({len(rows)} statements, each read against the paper "
          f"and its correspondence recorded; {len(flagged)} where the paper is "
          f"recorded as asserting more, all explained above)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
