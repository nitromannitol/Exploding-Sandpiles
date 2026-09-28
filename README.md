# Exploding-Sandpiles

A **Lean 4** formalization, in progress, of the paper
[*A shape theorem for exploding sandpiles*](https://arxiv.org/abs/2102.04422)
(Ahmed Bou-Rabee, Annals of Applied Probability 34(1A) (2024), 714-742; arXiv:2102.04422),
built on [`mathlib`](https://github.com/leanprover-community/mathlib4) and the shared library
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability) (`LatticeProb`).

[![CI](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/build.yml)

## What this is

A *background* is a function `η : ℤ^d → ℤ` counting chips at each site.  Add `n` chips at
the origin and topple in parallel: every site holding at least `2d` chips fires, sending one
chip to each neighbour.  The background is *robust* if this halts for every `n`, and
*explosive* otherwise.  For the Bernoulli background of `(1.2)`, which holds `2d - 2` chips
with probability `1 - p` and `2d - 1` with probability `p > 0`, Fey, Levine and Peres showed
that it is explosive almost surely (quoted as Theorem 1.1).  The main theorems of the paper
say that the explosion has a limit shape: the toppled region, rescaled by time, converges to
a convex domain (Theorem 1.2), and the rescaled arrival times converge locally uniformly to
a continuous, convex, one-homogeneous function (Theorem 1.3).  Theorem 1.4 extends the
explosion theorem to product backgrounds with at least `d` chips everywhere and a positive
density of sites with `2d - 1` chips.  Behind them are crossing speeds and a static
renormalization (Section 2), the last wave (Section 3), the proof of Theorem 1.3
(Section 4), general hypotheses under which the convergence holds (Section 5, Theorem 5.1),
explosive backgrounds with no limit shape (Section 6, Theorem 6.1), and a criterion for
explosion through dimensional reduction and bootstrap percolation (Section 7).

**This is a work in progress.**  Every theorem, lemma and proposition of the paper is
registered as a frozen Lean statement (`tools/check_coverage.py`), and five further results
that the paper cites are registered as assumptions, 29 registered statements in all.
**None of the paper's main results is proved yet.**

- **5 are proved:** Lemma 3.1 (a wave of order `(2d)^{dn}` covers the box of radius `n`),
  Lemma 3.3 (the last wave exceeds the penultimate wave by at most one), Lemma 3.4
  (subadditivity of the penultimate-cluster arrival times), Proposition 7.2 (dimensional
  reduction on a face of the box) and Proposition 7.3 (recurrence of the constant
  background `d`).
- **2 have written proofs that rest on open statements:** Theorem 1.3, proved from
  Propositions 3.1 and 4.1, and Theorem 5.1, proved from Proposition 5.1.  Their axiom
  closures contain `sorryAx` until those propositions are proved.
- **15 are open**, each a frozen statement whose proof is a single registered `sorry`:
  Theorems 1.2, 1.4 and 6.1, Propositions 2.1, 2.2, 3.1, 4.1, 5.1, 7.1 and 7.5, and Lemmas
  2.1, 3.2, 3.5, 3.6 and 3.7.
- **7 are cited results** that the paper quotes and does not prove: the explosion theorem of
  Fey, Levine and Peres (Theorem 1.1), Schonmann's bound for bootstrap percolation
  (Proposition 7.4), and five results cited in proofs: Theorem 0.0 and Corollary 1.4 of
  Liggett, Schonmann and Stacey (domination by product measures), Theorem 1.1 of Antal and
  Pisztora (the chemical distance in supercritical bond percolation), Lemma 5.2 of Mathieu
  (the holes of the infinite cluster) and Theorem 2.8 of Fey, Meester and Redig (the least
  action principle).

Not formalized: the proof outline of Section 1, the examples of Section 5.2 and the figures.

**What is assumed.**  The seven cited results are stated in Lean as propositions in
`Exploding/External/` and are **not proved here**; a theorem whose proof uses one takes it as
an explicit hypothesis, so its statement shows what it rests on.  For example, Theorem 1.3
takes the theorem of Fey, Levine and Peres and the three percolation results behind
Proposition 2.2.  [`ASSUMPTIONS.md`](ASSUMPTIONS.md) lists all seven with their verbatim Lean
statements.

- **`sorry`:** 15 registered statements are still open, each a single registered `sorry`;
  everything else is proved with only the three standard axioms, except that the two
  written proofs above rest on open statements.  `tools/check_warnings.py` fails on any
  other `sorry` or warning.
- **No custom `axiom`.**  The proved results reduce to `mathlib`'s three standard
  foundational axioms `propext`, `Classical.choice` and `Quot.sound`, verified by
  [`Exploding/Meta/AxiomsAudit.lean`](Exploding/Meta/AxiomsAudit.lean) for the results
  restated in [`Exploding/MainTheorems.lean`](Exploding/MainTheorems.lean) and by
  `tools/check_axioms.py` for every registered statement.  The cited results are
  hypotheses, not axioms.
- Pinned to Lean `v4.32.0`, `mathlib` at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997` and `Lattice-Probability` at commit
  `bbe0b90`.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **29 registered statements: 7 `SEALED`, proved here; 2 `CONDITIONAL`, proofs written that rest on open statements; 7 `FROZEN`, cited results that are assumed; and 13 `DRAFT_SORRY`, open.**  The 7 sealed nodes are machine-checked, and each one's axiom
closure is exactly Lean's three standard axioms `propext`,
`Classical.choice` and `Quot.sound`.  The 2 `CONDITIONAL` nodes, `thm-time-constant` and `thm-generalized-convergence`, have
complete proofs that use statements still open, so their axiom closures
contain `sorryAx` until those are proved.  The 7 `FROZEN` nodes, `ext-fey-levine-peres`, `ext-schonmann-bootstrap`, `ext-liggett-schonmann-stacey`, `ext-lss-bounded-degree`, `ext-antal-pisztora`, `ext-mathieu-holes` and `ext-fey-meester-redig`, are cited results,
stated in `Exploding/External/` and carried as explicit hypotheses by the
theorems that use them; they are assumed here, not proved.  Still open: `thm-limit-shape`, `thm-explosive`, `prop-crossing-time`, `prop-renormalization`, `lem-penultimate-cluster`, `lem-penultimate-upper-bound`, `lem-penultimate-close`, `prop-last-wave-convergence`, `prop-approximate-subadditive`, `prop-generalized-last-wave`, `thm-counterexample`, `prop-explosion-criteria` and `prop-box-crossing`.  Each has a frozen statement and a
proof that is a single registered `sorry`.  Run `python3 tools/check_axioms.py` to see the axiom closure of every node;
it fails while any closure contains `sorryAx`.  These counts are generated
from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`.

<!-- STATUS-END -->

## Main results

None of the paper's main results is proved yet.  [`Exploding/MainTheorems.lean`](Exploding/MainTheorems.lean)
names their frozen statements in its docstring (`Exploding.Frozen.limit_shape` for Theorem
1.2, `Exploding.Frozen.convergence_of_time_constant` for Theorem 1.3,
`Exploding.Frozen.explosive` for Theorem 1.4, `Exploding.Frozen.generalized_convergence`
for Theorem 5.1 and `Exploding.Frozen.counterexample` for Theorem 6.1), and states in full
only the results that are proved, each by `exact` of its certified counterpart in
`Exploding/Frozen/`, so the statements displayed there are the certified ones.  None of
them takes a cited result as a hypothesis.

* **`Exploding.square_lower_bound`** (Lemma 3.1): on a nonnegative background, for `n ≥ 1`
  and `m ≥ (2d)^{dn}`, the `m`-wave from the origin reaches every site of `[-n, n]^d`.
* **`Exploding.last_wave_bound`** (Lemma 3.3): for `2d - 2 ≤ η ≤ 2d - 1` with a well-defined
  last wave, the last wave exceeds the penultimate wave by at most one.
* **`Exploding.approx_subadditivity`** (Lemma 3.4): under the same hypotheses, the
  penultimate-cluster arrival times are subadditive.
* **`Exploding.dimensional_reduction`** (Proposition 7.2): on a face of the box, the
  constrained process in `ℤ^{d+1}` runs the one in `ℤ^d`.
* **`Exploding.recurrence`** (Proposition 7.3): the constant background `d` is recurrent.

## Scope and faithfulness

Every theorem, lemma and proposition of the paper is registered as a Lean declaration, one
node for each of its 24 numbered statements.  The paper formalized is the corrected copy
`paper/exploding.tex`, and [`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) lists
each place where it differs from the arXiv version.  The following words have fixed
meanings.

| term | meaning |
|---|---|
| **registered statement**, also called a **node** | one Lean declaration transcribing one statement of the paper. Each has an entry in `ledger/manifest.yaml`. |
| **frozen statement** | the declaration's text between the lines `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`, pinned by the SHA-256 of those bytes. It cannot change without the change being recorded in the manifest. The proof after the end marker may be rewritten freely. |
| **`SEALED`** | the node is **proved** here: a complete proof, whose axiom closure contains only `propext`, `Classical.choice` and `Quot.sound`. |
| **`CONDITIONAL`** | the node's proof is written and contains no `sorry` of its own, but it uses nodes that are still open, so its axiom closure contains `sorryAx`. It is not proved. |
| **`DRAFT_SORRY`** | the node is **open**: its statement is frozen and its proof is a single registered `sorry`. |
| **`FROZEN`** | a result the paper cites, **assumed rather than proved**, stated as a proposition in `Exploding/External/` and carried as an explicit hypothesis. |
| **axiom closure** | the axioms a proof ultimately rests on, as reported by Lean's `#print axioms`. |
| **`sorryAx`** | the axiom Lean inserts for an unproved `sorry`; its presence in an axiom closure means the result is not proved. |

The word *frozen* carries two senses, so it is worth separating them: every registered
statement is frozen in the sense of being **pinned by hash**, whether or not it is proved
yet, while the state `FROZEN` marks a statement that is **assumed rather than proved**.

The paper-to-Lean map, node by node, is [`CORRESPONDENCE.md`](CORRESPONDENCE.md), which
records the cited inputs and the conventions by which a statement of the paper is read in
Lean.  In summary: arrival and crossing times are valued in `ℕ∞`, so that the paper's `∞` is not
read as a junk value; locally uniform convergence is written in its `ε`-form; finiteness is
carried explicitly where a cardinality or a supremum would otherwise absorb it; the standing
hypotheses of Sections 2 to 4 are explicit hypotheses of the deterministic lemmas; and
Proposition 7.2 writes the paper's `d` as `d + 1`.

Checkers compare the Lean statements with the paper's rather than with their hashes.
`tools/check_coverage.py` confirms that every theorem, lemma and proposition of
`paper/exploding.tex` is claimed by a node.  In each frozen statement whose conclusion has an
existential constant, `tools/check_constants.py` checks that it is bound before the paper's
parameters.  `tools/check_clauses.py` and `tools/check_exponents.py` compare assertion
counts and exponents; neither has a recorded reading of any node yet, so both currently
check nothing.  These are review aids; none proves equivalence between LaTeX and Lean.

### Which Lean statement formalizes which result

The table links the paper's statements to the frozen Lean declarations and gives each one's
state.  It is generated from the manifest and the paper; it does not prove mathematical
correspondence between the two sources.

<!-- PAPER-MAP-BEGIN (generated by tools/sync_docs.py) -->

| Paper result | Description | Lean statement | State |
|---|---|---|---|
| [Theorem 1.1](paper/exploding.tex#L238)<br>`prop:fey_levine_peres_explode` | Explosion of the Bernoulli background (Fey, Levine and Peres), cited | [Exploding.External.FeyLevinePeresExplosive](Exploding/External/FeyLevinePeres.lean#L18) | cited result, assumed |
| [Theorem 1.2](paper/exploding.tex#L246)<br>`theorem:limit_shape` | The rescaled toppled region converges to a convex domain | [Exploding.Frozen.limit_shape](Exploding/Frozen/LimitShape.lean#L29) | open |
| [Theorem 1.3](paper/exploding.tex#L259)<br>`theorem:convergence_of_time_constant` | The rescaled arrival times converge | [Exploding.Frozen.convergence_of_time_constant](Exploding/Frozen/TimeConstant.lean#L33) | proof written; rests on open statements |
| [Theorem 1.4](paper/exploding.tex#L265)<br>`theorem:explosive` | A criterion for a product background to explode | [Exploding.Frozen.explosive](Exploding/Frozen/Explosive.lean#L22) | open |
| [Proposition 2.1](paper/exploding.tex#L416)<br>`prop:crossing_time` | Large boxes are crossed quickly | [Exploding.Frozen.crossing_time](Exploding/Frozen/CrossingTime.lean#L19) | open |
| [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | Domination by a product measure on a dependence graph of bounded degree (Liggett, Schonmann and Stacey), cited | [Exploding.External.LiggettSchonmannStaceyBoundedDegree](Exploding/External/LiggettSchonmannStaceyBoundedDegree.lean#L31) | cited result, assumed |
| [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | The chemical distance in supercritical bond percolation (Antal and Pisztora), cited | [Exploding.External.AntalPisztoraChemicalDistance](Exploding/External/AntalPisztora.lean#L29) | cited result, assumed |
| [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | The holes of the infinite cluster of site percolation (Mathieu), cited | [Exploding.External.MathieuHoleVolume](Exploding/External/MathieuHoles.lean#L28) | cited result, assumed |
| [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | The infinite cluster of good cubes | [Exploding.Frozen.renormalization_properties](Exploding/Frozen/Renormalization.lean#L35) | open |
| [Lemma 2.1](paper/exploding.tex#L531)<br>`lemma:local_convexity` | A path of topplings fills its bounding rectangle | [Exploding.Frozen.local_convexity](Exploding/Frozen/LocalConvexity.lean#L20) | proved |
| [Lemma 3.1](paper/exploding.tex#L705)<br>`lemma:square_lower_bound` | A wave of order (2d)^(dn) covers the box of radius n | [Exploding.Frozen.square_lower_bound](Exploding/Frozen/SquareLowerBound.lean#L22) | proved |
| [Lemma 3.2](paper/exploding.tex#L720)<br>`lemma:finite_exploding` | The last wave is well defined | [Exploding.Frozen.finite_exploding](Exploding/Frozen/FiniteExploding.lean#L27) | proved |
| [Lemma 3.3](paper/exploding.tex#L730)<br>`lemma:last_wave_bound` | The last wave exceeds the penultimate wave by at most one | [Exploding.Frozen.last_wave_bound](Exploding/Frozen/LastWaveBound.lean#L24) | proved |
| [Lemma 3.4](paper/exploding.tex#L760)<br>`lemma:approx_subadditivity` | Penultimate-cluster arrival times are subadditive | [Exploding.Frozen.approx_subadditivity](Exploding/Frozen/ApproxSubadditivity.lean#L105) | proved |
| [Lemma 3.5](paper/exploding.tex#L792)<br>`lemma:last_penultimate_cluster` | Penultimate clusters are polylogarithmically small | [Exploding.Frozen.last_penultimate_cluster](Exploding/Frozen/PenultimateCluster.lean#L29) | open |
| [Lemma 3.6](paper/exploding.tex#L807)<br>`lemma:penultimate_upper_bound` | A linear upper bound on last-wave arrival times | [Exploding.Frozen.penultimate_upper_bound](Exploding/Frozen/PenultimateUpperBound.lean#L27) | open |
| [Lemma 3.7](paper/exploding.tex#L832)<br>`lemma:last_penultimate_close` | Last-wave and penultimate-cluster arrival times are close | [Exploding.Frozen.last_penultimate_close](Exploding/Frozen/PenultimateClose.lean#L27) | open |
| [Proposition 3.1](paper/exploding.tex#L846)<br>`prop:convergence_of_the_last_wave` | Convergence of the last wave | [Exploding.Frozen.convergence_of_the_last_wave](Exploding/Frozen/LastWaveConvergence.lean#L27) | open |
| [Proposition 4.1](paper/exploding.tex#L886)<br>`prop:approximate_subadditive` | The last wave approximates the exploding sandpile | [Exploding.Frozen.approximate_subadditive](Exploding/Frozen/ApproximateSubadditive.lean#L29) | open |
| [Proposition 5.1](paper/exploding.tex#L1203)<br>`prop:convergence_of_the_generalized_last_wave` | Convergence of the last wave under the general hypotheses | [Exploding.Frozen.convergence_of_the_generalized_last_wave](Exploding/Frozen/GeneralizedLastWave.lean#L32) | open |
| [Proposition 5.1](paper/exploding.tex#L1203)<br>`prop:convergence_of_the_generalized_last_wave` | Domination of a finitely dependent field by a product measure (Liggett, Schonmann and Stacey), cited | [Exploding.External.LiggettSchonmannStacey](Exploding/External/LiggettSchonmannStacey.lean#L26) | cited result, assumed |
| [Theorem 5.1](paper/exploding.tex#L1249) | Convergence of the exploding sandpile under the general hypotheses | [Exploding.Frozen.generalized_convergence](Exploding/Frozen/GeneralizedConvergence.lean#L33) | proof written; rests on open statements |
| [Theorem 6.1](paper/exploding.tex#L1351)<br>`theorem:counterexample` | Explosive backgrounds without a limit shape | [Exploding.Frozen.counterexample](Exploding/Frozen/Counterexample.lean#L25) | open |
| [Theorem 6.1](paper/exploding.tex#L1351)<br>`theorem:counterexample` | The least action principle (Fey, Meester and Redig), cited | [Exploding.External.FeyMeesterRedigLeastAction](Exploding/External/FeyMeesterRedig.lean#L40) | cited result, assumed |
| [Proposition 7.1](paper/exploding.tex#L1821)<br>`prop:explosion_criteria` | A criterion for a background law to explode | [Exploding.Frozen.explosion_criteria](Exploding/Frozen/ExplosionCriteria.lean#L18) | open |
| [Proposition 7.2](paper/exploding.tex#L1890)<br>`prop:dimensional_reduction` | Dynamics on a face reduce to one dimension lower | [Exploding.Frozen.dimensional_reduction](Exploding/Frozen/DimensionalReduction.lean#L24) | proved |
| [Proposition 7.3](paper/exploding.tex#L1927)<br>`prop:recurrence` | The constant background d is recurrent | [Exploding.Frozen.recurrence](Exploding/Frozen/Recurrence.lean#L17) | proved |
| [Proposition 7.4](paper/exploding.tex#L1969)<br>`prop:schonnmann_bootstrap` | Schonmann's bound for bootstrap percolation, cited | [Exploding.External.SchonmannBootstrap](Exploding/External/Schonmann.lean#L23) | cited result, assumed |
| [Proposition 7.5](paper/exploding.tex#L1986) | The background of Theorem 1.4 is box-crossing | [Exploding.Frozen.box_crossing](Exploding/Frozen/BoxCrossing.lean#L21) | open |

<!-- PAPER-MAP-END -->

## Verified against a Mathlib-only statement

Not yet.  The repositories this one follows restate each main theorem using only Mathlib and
check it with [`leanprover/comparator`](https://github.com/leanprover/comparator).  Such a
check certifies nothing while the main theorems rest on `sorry`, so the challenges will be
added when they are sealed; [`Audit/README.md`](Audit/README.md) describes the plan.

## Building

The project uses [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager)
and Lake.  The toolchain is pinned in [`lean-toolchain`](lean-toolchain)
(`leanprover/lean4:v4.32.0`), so `elan` installs the right Lean version automatically, and
the dependencies are pinned to commits in `lakefile.lean` and
[`lake-manifest.json`](lake-manifest.json); `lake` fetches them, and there is nothing to
clone by hand.

```bash
lake exe cache get   # prebuilt Mathlib
lake build           # compile the project
```

The build emits exactly one `declaration uses 'sorry'` warning for each open registered
statement, 16 in all, and no other warning.

```bash
lake build Exploding.Meta.AxiomsAudit   # print the axioms of the proved results
```

To use the library, `import Exploding` pulls in the whole development; the proved results
are in `import Exploding.MainTheorems`.

The checkers in `tools/` need Python 3.10 or newer and PyYAML
(`python3 -m pip install -r tools/requirements.txt`).  `python3 tools/verify.py` runs every
check below and fails on the first failure; continuous integration runs it on request.
`check_axioms.py` and `check_warnings.py` run Lean; the others read the manifest, the paper
and the Lean sources.

| command | what it guarantees |
|---|---|
| `python3 tools/check_manifest.py` | every node's file holds exactly one frozen block whose SHA-256 equals `frozen_sha256` and which declares exactly the node's `export`; every file in `Exploding/Frozen/` belongs to one node; `Exploding/` contains no `axiom`, `admit` or `sorryAx`, and `sorry` only once in the proof of each open node |
| `python3 tools/check_axioms.py` | runs `#print axioms` on every manifest export and lists which closures contain `sorryAx`; it fails while any node is open, and `tools/verify.py` checks instead that exactly the open and `CONDITIONAL` nodes are the ones that do |
| `python3 tools/check_warnings.py` | `lake build Exploding` emits one `sorry` warning per open node and no other warning |
| `python3 tools/check_constants.py` | in a frozen statement whose conclusion has an existential constant, the constant is bound before the paper's parameters |
| `python3 tools/check_coverage.py` | every theorem, lemma and proposition of `paper/exploding.tex` is named in the `source` of some manifest node |
| `python3 tools/check_clauses.py` | compares the assertion count of each paper statement with the conjunct count of its Lean statement, for the nodes with a recorded reading (none yet) |
| `python3 tools/check_exponents.py` | compares the exponents written in a paper statement with those in its Lean statement, for the nodes with a recorded reading (none yet) |

Also in `tools/`: `paper_anchors.py` and `paper_citations.py` check the
`exploding.tex:<lines>` ranges in the manifest and in the Lean docstrings against the paper's
labels; `sync_docs.py` checks (`--write` regenerates) the status block and the paper map of
this file and the frozen-surface table of `CORRESPONDENCE.md`; `assumptions.py` regenerates
`ASSUMPTIONS.md` (`--check` verifies it is current); `freeze.py` registers a frozen statement
in the manifest.

The paper snapshot `paper/exploding.tex` is the source of the Annals of Applied Probability
submission of arXiv:2102.04422v2, corrected where the arXiv text was wrong; it needs the
`imsart` class to compile, and its figures are not included.  The unmodified arXiv source is
`paper/exploding-arxiv.tex`, and [`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md)
lists every difference between the two.

## Repository layout

```
Exploding/
  MainTheorems.lean   the proved results, stated in full; the main theorems named
  Frozen/             the frozen statement surface, one frozen statement per file
  External/           the two cited results, stated as propositions and assumed
  Support/            the model and the lemmas the frozen statements are proved from
    Toppling.lean     parallel toppling, the n-wave, stabilizable, robust and explosive
    Vocab.lean        boxes, crossing times, good cubes, the last wave, the background law
    Hypotheses.lean   the five hypotheses of Section 5
    Reduction.lean    the constrained processes of Section 7.1
  Meta/               AxiomsAudit.lean
Exploding.lean        the root module (imports the whole library)
Audit/                README.md: the comparator challenges, to be added
ASSUMPTIONS.md        the cited results assumed (generated)
CORRESPONDENCE.md     paper ↔ Lean: conventions, cited inputs, differences, node table
ledger/manifest.yaml  one row per registered statement: hash, paper source, state
paper/exploding.tex   the paper, pinned by the SHA-256 in ledger/manifest.yaml
paper/exploding-arxiv.tex, paper/arxiv/
                      the unmodified arXiv source
paper/CHANGES_FROM_ARXIV.md
                      every difference between the two
tools/                the checkers and generators listed under Building
```

## How this was built

The Lean code in this repository was written by AI models under the supervision of the
author, in a private working repository whose history is this one.  A supervising Claude
Code session launched the agents below, wrote briefs, recorded the author's decisions and
merged their branches; for this repository it ran on Claude Fable 5.1 from 2026-09-10 to
2026-09-16, on Claude Opus 5 on 2026-09-20, and on Claude Opus 5.5 on 2026-09-23 and
2026-09-24.  On 2026-09-10 a Claude Opus 5 general, a Claude Code subagent,
froze all twenty-four statements, including the two cited results, wrote the model and
sealed Lemmas 3.3 and 3.4 and Proposition 7.2; GLM-5.3-flash drafted compile-filtered proof
candidates for it, some of which became support lemmas, and GLM-5.3 and GLM-5.3-flash
audited every frozen statement against the paper.  On 2026-09-13 and 2026-09-14
DeepSeek-v4.1-flash generals, through a custom driver, sealed Proposition 7.3 and wrote the
proofs of Theorems 1.3 and 5.1 from the propositions they use.  On 2026-09-23 the supervising
session repaired two of the paper checkers, whose patterns named a different paper.  Claude
Sonnet 5 generals (2026-09-16 and 2026-09-17), a Kimi k3 general (2026-09-16), Mistral's
Leanstral (2026-09-20 and 2026-09-23), DeepSeek-v4.1-flash agents (2026-09-23 and
2026-09-24) and Claude Sonnet 5 subagents (2026-09-23 and 2026-09-24) also worked on the open
nodes; none of that work is in this repository.  One Sonnet branch registered the statements
of two open nodes as cited results, which would have sealed them by assumption; the
supervising session rejected it.  Claude Opus 5.5 wrote `Exploding/MainTheorems.lean`, the
axiom audit and this documentation on 2026-09-24; on the same day it stated the results the
paper cites as explicit hypotheses, corrected the paper copy as listed in
`paper/CHANGES_FROM_ARXIV.md`, restated the affected statements to match, and proved
Lemma 3.1.  The models, tooling, cost, and review
status are disclosed in full in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**, who is also the author of the paper it
formalizes.  If you use this formalization, please cite it using the metadata in
[`CITATION.cff`](CITATION.cff).

## Acknowledgements

This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4) and the shared library
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability).  The two
results it assumes are due to Fey, Levine and Peres and to Schonmann.

## License

The Lean code in this repository is licensed under the **Apache License 2.0** (see
[`LICENSE`](LICENSE)).  The paper source in `paper/` is included for reference and is not
covered by the Apache license.
