"""Compare how much each paper statement asserts with how much its Lean node does.

Every other checker here compares a statement with *itself*: the hash pins the
bytes, the axiom check pins the proof.  None of them notices when a frozen
statement quietly asserts less than the paper statement it claims to transcribe.
That is how a frozen statement can end up without one of the three displays its
paper statement
asserts, while every other check passed.

This counts assertion units on each side and reports the pairs where the paper
asserts more:

  paper   displayed equations and enumerated items inside the statement
  Lean    top-level conjuncts of the frozen statement's conclusion

The counts are a heuristic, not a proof of correspondence: one Lean conjunct can
faithfully carry two paper displays, and one paper display can need three Lean
conjuncts.  So a mismatch is a prompt to look, not a verdict, and every node is
listed with its counts so the reader can judge. The statements compared are
those of the manifest's source file (the corrected edition); definitions stated
separately and results cited without a statement range or label are listed as
excluded. Each reading records the SHA-256 of the frozen statement it was written
for (`READ_AT`); when a statement changes, its reading must be checked again and
its hash updated, or the check fails. A run that compares nothing fails.

    python3 tools/check_clauses.py            # report
    python3 tools/check_clauses.py --strict   # exit 1 if any node is unreviewed
"""

from __future__ import annotations

import hashlib
import os
import re
import sys
from pathlib import Path

from sync_docs import audit_nodes, frozen_block, load_manifest, source_pins, source_range

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
        "The paper asserts one display: on an event of probability 1 the set {v̄_t > 0} "
        "converges in measure to a convex domain B(p), where v̄_t(x) = v_t([tx]). Lean puts "
        "the existence of B before the almost-sure event; the Tendsto of the "
        "symmetric-difference measure to 0 is the display, and Convex, IsOpen and Nonempty "
        "for B read 'convex domain' as a nonempty open convex set.",
    "thm-time-constant":
        "The paper asserts one prose claim: on an event of probability 1 the rescaled arrival "
        "times n⁻¹T_η([nx]), with T_η(x) the least t ≥ 1 with v_t(x) > 0, converge locally "
        "uniformly to N_p, a continuous, convex, one-homogeneous function. Lean states N with "
        "Continuous, ConvexOn, homogeneity for c ≥ 0 and the ε–N convergence on compacts, and "
        "adds Explosive η and finiteness of arrival on the almost-sure event, which the "
        "paper's definition of T_η presupposes.",
    "thm-explosive":
        "The paper asserts one claim: for d ≥ 2, if ν on Z gives mass 1 to {m ≥ d} and "
        "positive mass to 2d−1, then the product law of β is explosive with probability 1. "
        "Lean's hlow and hhit state these two conditions, the conclusion is ∀ᵐ β, Explosive "
        "β, and the SchonmannBootstrap external, which the paper's proof uses, is carried as "
        "an explicit hypothesis.",
    "prop-renormalization":
        "The paper asserts three items for fixed large k, with constants c, C on an event of "
        "probability 1: a unique infinite cluster C∞ of good cubes; components of C∞ᶜ meeting "
        "[−n,n]^d have volume below (log n)^{5/2}; and for x, y ∈ C∞ with |x| ≤ n and |x−y| ≥ "
        "(log n)², c|x−y| ≤ d(x,y) ≤ C|x−y|. Lean carries item 1 as an infinite connected "
        "good set Cinf with a witness cube and uniqueness among infinite components, item 2 "
        "as finiteness with ncard below (log n)^{5/2} (volume read as cardinality), and item "
        "3 as a chemical distance m with c·mnorm ≤ m ≤ C·mnorm (|·| read as the ℓ¹ norm), the "
        "two relations of the display being its two conjuncts.",
    "lem-square-lower-bound":
        "The paper asserts one claim: for d ≥ 2 there is a deterministic C_d > 0 such that "
        "for every η with 2d−2 ≤ η ≤ 2d−1, every n ≥ 1 and every m ≥ 1 with m ≥ ⌈C₂ n² "
        "log(n+1)⌉ when d = 2 or m ≥ ⌈C_d nᵈ⌉ when d ≥ 3, the wave u_t^{(m,0)} is positive on "
        "Λ_n for all large t. Lean takes C > 0 before η, states the threshold as ⌈C "
        "nᵈ·(log(n+1) if d = 2, else 1)⌉ ≤ m, and gives ∃ T with 0 < wave η m 0 t x for all t "
        "≥ T and x in cent d n (Λ_n read as the cube [−n,n]^d).",
    "rem-sharp-planar-obstruction":
        "The paper asserts one display for the homogeneous height-2 background in d = 2: the "
        "least order M₂(n) whose wave covers Λ_n satisfies c n² log(n+1) ≤ M₂(n) ≤ C n² "
        "log(n+1) for every n ≥ 1. Lean takes M as the least m ≥ 1 whose wave covers cent 2 "
        "n, and carries the two bounds as its last two conjuncts; the proof's displays are "
        "not asserted by the statement, which is why the count of 6 exceeds the two "
        "relations, and the Fey–den Boer–Redig and Fey–Levine–Peres inputs appear as "
        "hypotheses.",
    "lem-penultimate-cluster":
        "The paper asserts one display: there is γ > 0 such that for large n and |x| ≤ n, the "
        "penultimate cluster P(x) lies in x + [−(log n)^γ, (log n)^γ]^d, with |x| read as "
        "mnorm. Lean takes γ > 0 and an almost-sure event (the paper leaves it implicit, "
        "since P(x) is random) and states that every y in penultimateCluster η x has |y_i − "
        "x_i| ≤ (log n)^γ for every coordinate i, which is the box inclusion read "
        "coordinatewise.",
    "lem-penultimate-upper-bound":
        "The paper asserts one display: on an event of probability 1 there are γ, C with "
        "T̂(x) ≤ C|x| + (log n)^γ for large n and |x| ≤ n, with |x| read as mnorm. Lean takes "
        "γ > 0 and C > 0 (the positivity is added) and states that lastArrival(0, x) equals a "
        "natural number m, which is the finiteness of T̂, with m ≤ C·mnorm x + (log n)^γ.",
    "lem-penultimate-close":
        "The paper asserts one two-sided display: on an event of probability 1, for large n "
        "and |x| ≤ n, T̂(x) ≤ T̃(x) ≤ T̂(x) + (log n)^γ with γ > 0. Lean states lastArrival ≤ "
        "clusterArrival as the left inequality, and natural-number witnesses a, b for the two "
        "values with b ≤ a + (log n)^γ as the right one.",
    "prop-last-wave-convergence":
        "The paper asserts one prose claim: on an event of probability 1, n⁻¹T̂_η([nx]) "
        "converges locally uniformly to N_p, a continuous, convex, one-homogeneous function "
        "on R^d. Lean states N with Continuous, ConvexOn, homogeneity for c ≥ 0 and the ε–N "
        "convergence on compacts, and adds finiteness of lastArrival on the almost-sure "
        "event, which the paper presupposes.",
    "prop-approximate-subadditive":
        "The paper asserts two displays: on an event of probability 1, with constants C₁(η), "
        "C₂(η), T(x) ≤ T̂(x) + C₁ and T̂(x) ≤ T(x) + C₂ for all x ∈ Z^d. Lean's two conjuncts "
        "are these inequalities with C1, C2 : ℕ, which is faithful since the paper's "
        "constants are finite; arrival takes times n ≥ 1, the same as the paper's minimum "
        "over t ≥ 0 because the odometer is 0 at time 0.",
    "prop-generalized-last-wave":
        "The paper asserts one prose claim under Hypotheses 1, 3 and 4 (finite range of "
        "dependence, path filling, strongly box-crossing): on an event of probability 1, η is "
        "explosive and n⁻¹T̂_η([nx]) converges locally uniformly to a deterministic, "
        "continuous, convex, one-homogeneous N_η depending only on the law. Lean takes these "
        "three as h1, h3, h4, adds the stationarity, ergodicity and support assumptions on "
        "the law, puts ∃ N before the almost-sure event, and asserts Explosive, finiteness "
        "and the ε–N convergence.",
    "thm-generalized-convergence":
        "The paper asserts one prose claim under the assumptions of the last-wave proposition "
        "and Hypothesis 5 (wave approximation): on an event of probability 1, η is explosive "
        "and n⁻¹T_η([nx]) converges locally uniformly to N_η. Lean takes the same hypotheses "
        "with h5 and states Explosive, finiteness of arrival and the ε–N convergence of "
        "arrival for one ∃ N; the statement does not restate that this N is the last-wave "
        "limit, so that identification is the paper's.",
    "thm-counterexample":
        "The paper asserts, for each d ≥ 2, explosive backgrounds with η ≱ 2d−2 that have no "
        "limit shape and whose arrival times T(n) = min{t > 0 : v_t(n e₁) > 0} satisfy limsup "
        "n⁻¹T(n) ≥ 3/2 and liminf n⁻¹T(n) = 1. Lean gives η with an explosiveness witness, "
        "¬∀x, 2d−2 ≤ η x, finiteness of the arrival times, 3/2 ≤ limsup, liminf = 1, and ¬∃ "
        "measurable B with the rescaled support converging to B in measure; the last negation "
        "ranges over all measurable sets, so it implies the paper's negation over convex "
        "domains.",
    "prop-explosion-criteria":
        "The paper asserts one implication for d ≥ 2: if the law has finite range of "
        "dependence (Hypothesis 1), satisfies box-crossing (Hypothesis 2) and is recurrent, "
        "then it is explosive. Lean states this as FiniteRangeOfDependence, BoxCrossingHyp "
        "and RecurrentLaw implying ExplosiveLaw, where explosive for a law is read as ∀ᵐ η, "
        "Explosive η, and the stationarity, ergodicity and support assumptions are added.",
    "prop-box-crossing":
        "The paper asserts two clauses: for d ≥ 2 the original product law is box-crossing, "
        "and in dimension one every law supported on η ≥ 1 is box-crossing. Lean quantifies "
        "the first over product measures of any ν with ν{m ≥ d} = 1 and ν{2d−1} > 0, with the "
        "Schönmann input, which contains the toy law (1−p)δ_{2d−2} + pδ_{2d−1} as a case, and "
        "the second over laws P on Site 1 with P{η ≥ 1} = 1, reading 'supported on' as almost "
        "sure.",
    "ext-fey-levine-peres":
        "The paper asserts one statement: for the toy background with p > 0, η is explosive "
        "with probability 1. Lean's definition FeyLevinePeresExplosive quantifies over every "
        "d ≥ 2 and every p with 0 < p ≤ 1, the range where the toy law is a probability law, "
        "and asserts ∀ᵐ η ∂(toyLaw d p), Explosive η.",
    "ext-schonmann-bootstrap":
        "The paper asserts one inequality: with η′ equal to 2d with probability p and to d "
        "otherwise, there are c, C depending only on d and p such that P(Q_n^{(d)} is "
        "η′-internally spanned) ≥ 1 − c e^{−Cn}; the case definition of η′ is a definition, "
        "not an assertion, and is carried by the arguments 2d, d, p of productLaw. Lean "
        "states ∃ c, C > 0 with ofReal(1 − c e^{−Cn}) ≤ productLaw d (2d) d p "
        "{InternallySpanned η n} for all n, where ofReal takes a negative bound to 0, which "
        "the paper's inequality permits.",
    "ext-fey-levine-peres-proved":
        "This is the same statement as ext-fey-levine-peres: the Lean value xsr_flp is "
        "FeyLevinePeresExplosive, so the reading there applies.",
    "ext-schonmann-bootstrap-proved":
        "This is the same statement as ext-schonmann-bootstrap: the Lean value xsr_schonmann "
        "is SchonmannBootstrap, so the reading there applies.",
    "lem-last-wave-bound":
        "The paper asserts two claims for t ≥ 1 and all x, z: the last wave started at z is "
        "at most 1 outside the interior of the penultimate cluster of z, and u_t^{(z)}(x) ≤ 1 "
        "+ ũ^{(z)}(x). Lean states the displayed bound as its first conjunct for every t ∈ ℕ "
        "(so it also covers t = 0, which the paper excludes), with penultimateWave as ũ, and "
        "the at-most-1 claim as the second conjunct, reading the interior as the cluster "
        "minus its inner boundary; the range 2d−2 ≤ η ≤ 2d−1 and a nonstabilizing witness at "
        "z are added as hypotheses.",
    "prop-dimensional-reduction":
        "The paper asserts two displays, for all t ≥ 0 and (1, x_{d−1}) in the low face "
        "F₁(Q_n^{(d)}): the odometers agree, u_t^{(d)}(1, x) = u_t^{(d−1)}(x), and the "
        "sandpiles differ by 2 wherever u_t^{(d)}(1, x) = 0. Lean's first conjunct is bUpOdo "
        "= bLowOdo and its second is bUpConf = bLowConf + 2 under bUpOdo = 0, with F₁ read as "
        "faceLow; Lean writes the upper dimension as d + 1 (with 1 ≤ d), so the paper's "
        "dimension d is Lean's d + 1.",
    "lem-approx-subadditivity":
        "The paper asserts one display: for all a, b, z ∈ Z^d, T̃(a,z) ≤ T̃(a,b) + T̃(b,z). "
        "Lean states the same inequality for clusterArrival, with the range 2d−2 ≤ η ≤ 2d−1 "
        "and a nonstabilizing witness at every site added as hypotheses so that T̃ is "
        "defined.",
    "prop-recurrence":
        "The paper asserts one statement: for every d ≥ 1 the constant background η ≡ d on "
        "Z^d is recurrent. Lean states Recurrent (fun _ => d) for every d ≥ 1.",
    "lem-local-convexity":
        "The paper asserts one display for a finite path A = {z^{(i)}} with z^{(i)} ∼ "
        "z^{(i+1)}: the parallel toppling w_t with A held fixed, started from w_0 = 1_A with "
        "s_0′ = η + Δw_0, equals 1 on the bounding rectangle br(A) for all t ≥ |br(A)|. Lean "
        "states fodo A η (indicator A 1) t x = 1 for x ∈ br A and |br A| ≤ t, where fodo's "
        "toppling test already uses η + Δw_t, so s_0′ is built in; the range 2d−2 ≤ η ≤ 2d−1 "
        "(the text before the lemma uses η ≥ 2d−2) and the finiteness of br(A) are added as "
        "hypotheses.",
    "lem-finite-exploding":
        "The paper asserts one statement: the last wave at 0 is well defined, M̂_η(0) < ∞. "
        "Lean states that almost surely some n ≥ 1 has a wave at 0 that does not stabilize, "
        "which is the finiteness of M̂_η(0), since waveThreshold is the least such n.",
    "prop-crossing-time":
        "The paper asserts one display: for every δ > 0 there is k with the maximum over i "
        "and z of the crossing time 𝔠_k^{(i,z)} at most k^d, with probability at least 1 − δ. "
        "Lean takes 1 ≤ k and states ofReal(1 − δ) ≤ toyLaw d p of the event that, for every "
        "i and every z in closureN(cube k), every site of the cube is eventually 1 under "
        "crossOdo (the case w_∞ = 1 on Q_k) and some n with 1 ≤ n ≤ k^d has crossOdo = 1 on "
        "the cube (the time bound); the range of z is read as closureN(cube k), which the "
        "paper leaves implicit.",
}

# Nodes known from hand reading to assert strictly less than their paper
# statement, which the count heuristic misses when the missing assertion is not
# a displayed relation.  Like the heuristic flags, these are printed and
# explained but do not fail the check; only `unreviewed` does.
FLAGGED: set[str] = set()


# The SHA-256 of the frozen statement each reading above was checked against.
READ_AT: dict[str, str] = {
    "thm-limit-shape": "3f3707ff2dfa461558934c748b614a3b4472f338425ddf883b0ff4485e72f6d9",
    "thm-time-constant": "83239bc6236e7faecd7ba0ab147fc0af98c324fc90f32cb537a6f368fa478a07",
    "thm-explosive": "8132c02216ac6b502b1b4e6bb898ead2d8aaeea4a7b9da2795b1f83af4b403ed",
    "prop-renormalization": "5e3c8b09f9ce732c2cad76168fa1d455e515ea8a08ae74716d43967e8e623b21",
    "lem-square-lower-bound": "19f817d7ff3eb7c2f9a112ea3fe3c0070bb13f4e9e9ca3a6c31ad2f0265dcf1b",
    "rem-sharp-planar-obstruction": "a086ab6a2d98e5e193a5bf73c82335824ffa3b2628bf1f418859acbf9777a03d",
    "lem-penultimate-cluster": "58d7a4ac6a71a4a8145a5c64cb08d305febcbd628497ada2cb10bf250293f4d1",
    "lem-penultimate-upper-bound": "5b2ee13157a8d82856757ff4dd81617c9a2c782f2d59e704ccf71b5e14cd6a18",
    "lem-penultimate-close": "f2ac930203bda0ebdc77f88a7eefb80485e0492766f23f701b3f532d34c3ac18",
    "prop-last-wave-convergence": "9a80cc4dcaac38eaab62fc1fbfeb46f6b0868d54c397c6b4687823ef3940ff59",
    "prop-approximate-subadditive": "9b0824a6fef38f45bc7f3c1cc813ab4268d210f0eeb61ea6bf217cd93132cd44",
    "prop-generalized-last-wave": "aa81aa6cdc69939e486fb145c1d7b7b7643e47511b4dbe84d71ad588ea823eaf",
    "thm-generalized-convergence": "d32daec0ed262bf93997fd6bf958d784c860b5024f292c5a782cf8b0f332c546",
    "thm-counterexample": "1af0799acd9eccce67b979a6a59e756398fd513054e9019f1118421bf7ecf178",
    "prop-explosion-criteria": "72c7f767456a36130729aa032ed6da22a650bd11c0d87266b9a785b73dab827f",
    "prop-box-crossing": "967eea86ece9bb02ada55289f36b6bb98ab9f02b4099f9067c43565191c91144",
    "ext-fey-levine-peres": "bb15c9367cd9630ab65ea5d4d6829aca3ced6da045c2f2e078edb1306a3f890c",
    "ext-schonmann-bootstrap": "26fb069d31c8b054743da77918174384ef4a3981145d075fda165b96748b51ce",
    "ext-fey-levine-peres-proved": "a25c10e2f66ff0a1141aea2274ab888744e3a0a24b8e65077a671b3ea60ecb7a",
    "ext-schonmann-bootstrap-proved": "b2f9d167d3cbd4c150d94c771f06b6055ed809a62378fb549e2c0b7422c1ce89",
    "lem-last-wave-bound": "3760843f3135cb089b2282167e54ccfa110776cff8af977a314b73c7f3179774",
    "prop-dimensional-reduction": "678347f088aa6399bee44eabb178981923e8fa91f3fa119fb1550a2f5b25d7a1",
    "lem-approx-subadditivity": "cc8f12ca936e4c7004662f4796489012419c44eb5071f5549ea1fa3cf5fc67f5",
    "prop-recurrence": "fb09b457811848161a746759e6fd31ee024a56bee43df4e23cca58af7ae87fa1",
    "lem-local-convexity": "c265b27336538e776144ad00d8ad3e44a93816312863f9b3cb9dc3d5997e91f4",
    "lem-finite-exploding": "70e35f646e03b599a40942113c9c6f1ad34cb35dc8757901a8ca990199169701",
    "prop-crossing-time": "0abd7c5aad74dc25d871825907205f3af57bbc7755498247c348ad66592bceae",
}


def paper_path(manifest: dict) -> Path:
    """The manifest's source file, or `$EXPLODING_PAPER` (which must have the same hash)."""
    env = os.environ.get("EXPLODING_PAPER")
    return Path(env) if env else ROOT / manifest["source_pin"]["file"]


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
    try:
        manifest = load_manifest(MANIFEST)
        default = manifest["source_pin"]
        path = paper_path(manifest)
        if hashlib.sha256(path.read_bytes()).hexdigest() != default["sha256"]:
            raise LookupError(f"{path} does not have the SHA-256 recorded in the manifest")
        lines = path.read_text(encoding="utf-8").splitlines()
        pins = source_pins(manifest["nodes"], manifest)
        eligible, excluded = audit_nodes(manifest["nodes"], pins, default)
    except (LookupError, KeyError, OSError, ValueError) as exc:
        print(f"check_clauses: {exc}", file=sys.stderr)
        return 2

    rows, flagged, unreviewed = [], [], []
    for node in eligible:
        src = node["source"]
        lab = re.search(r"label ([A-Za-z][A-Za-z0-9:_-]*)", src)
        if not lab:
            excluded.append((node["id"], "no labelled statement"))
            continue
        a, b = source_range(node, pins[node["id"]])
        segment = "\n".join(lines[a - 1:b])
        blk = frozen_block(node)
        p, l = paper_units(segment), lean_conjuncts(blk)
        rows.append((node["id"], lab.group(1), p, l))
        if p > l or node["id"] in FLAGGED:
            flagged.append(node["id"])
        current = node["frozen_sha256"]  # checked against the file by check_manifest
        if node["id"] not in REVIEWED or READ_AT.get(node["id"]) != current:
            unreviewed.append(node["id"])

    print(f"{'node':26s} {'label':22s} paper  lean")
    for nid, lab, p, l in rows:
        mark = "  <-- paper asserts more" if nid in flagged else ""
        print(f"  {nid:24s} {lab:22s} {p:5d} {l:5d}{mark}")

    print("\nRecorded correspondence, one line per statement:")
    for nid, _, _, _ in rows:
        print(f"  {nid}: {REVIEWED.get(nid, 'NOT REVIEWED')}")

    print("\nExcluded:")
    for nid, reason in excluded:
        print(f"  {nid}: {reason}")
    if not rows:
        print("\ncheck_clauses: FAIL (no statement compared)", file=sys.stderr)
        return 1

    if unreviewed:
        print(f"\ncheck_clauses: {len(unreviewed)} statement(s) have no reading for their "
              f"current frozen text: {', '.join(unreviewed)}", file=sys.stderr)
        return 1
    print(f"\ncheck_clauses: OK ({len(rows)} statements; "
          f"{len(excluded)} excluded; each compared statement read against the paper "
          f"and its correspondence recorded; {len(flagged)} where the paper is "
          f"recorded as asserting more, all explained above)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
