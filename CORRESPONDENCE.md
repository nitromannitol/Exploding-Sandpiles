# Correspondence: paper ↔ Lean

Maps every frozen declaration to *A shape theorem for exploding sandpiles*
(Bou-Rabee).

## Conventions

- The paper is pinned at `paper/exploding.tex`, the Annals of Applied
  Probability submission of arXiv:2102.04422v2 with the corrections listed in
  [`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md); its SHA-256 is in
  `ledger/manifest.yaml`.  Source locations are `exploding.tex:<line range>` plus
  the LaTeX `\label` name.
- The bytes between `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`
  are the contract.  `python3 tools/check_manifest.py` is the authority on the
  hash recipe.

## External inputs

Every cited result the paper uses without proof is a `Prop` in
`Exploding/External/`, frozen and pinned like a statement, and enters only as an
explicit hypothesis of the nodes whose proofs use it.

| node | cited result | used by |
|---|---|---|
| `ext-fey-levine-peres` | Fey, Levine and Peres, *Growth rates and explosions in sandpiles*, Proposition 1.4 | quoted as Theorem 1.1; strengthened by `thm-explosive` |
| `ext-schonmann-bootstrap` | Schonmann, *On the behavior of some cellular automata related to bootstrap percolation*, the large-deviation bound | `prop-box-crossing`, `thm-explosive`, `thm-limit-shape` |
| `ext-liggett-schonmann-stacey` | Liggett, Schonmann and Stacey, *Domination by product measures*, Theorem 0.0 | Section 5: `prop-generalized-last-wave`, `thm-generalized-convergence` |
| `ext-lss-bounded-degree` | Liggett, Schonmann and Stacey, *Domination by product measures*, Corollary 1.4 | Proposition 2.2 and every statement that uses it |
| `ext-antal-pisztora` | Antal and Pisztora, *On the chemical distance for supercritical Bernoulli percolation*, Theorem 1.1, for bond percolation | Proposition 2.2 and every statement that uses it |
| `ext-mathieu-holes` | Mathieu, *Quenched invariance principles for random walks with random conductances*, Lemma 5.2 | Proposition 2.2 and every statement that uses it |
| `ext-fey-meester-redig` | Fey, Meester and Redig, *Stabilizability and percolation in the infinite volume sandpile model*, Theorem 2.8 | `thm-counterexample` |

## How a statement of the paper is read in Lean

| paper | Lean reading | why |
|---|---|---|
| every arrival time and the crossing time | valued in `ℕ∞` | `sInf ∅ = ⊤` there is the paper's `∞`; in `ℕ` it is the junk value `0` |
| the bounds on arrival times against real quantities | conjoined with `∃ m : ℕ, T = m` | carries the finiteness the paper asserts and avoids `ENat.toNat ⊤ = 0` |
| locally uniform convergence | written in its `ε`-form, not as a supremum | `sSup ∅ = 0` and an unbounded `sSup` is `0` in `ℝ` |
| `prop:renormalization_properties`, clause (2) | the finiteness of the component is conjoined with the cardinality bound | `Set.ncard` of an infinite set is `0` |
| `lemma:local_convexity` | the finiteness of `br(A)` is carried, and `\|br(A)\|` read off it | same reason |
| `lemma:local_convexity`, `lemma:last_wave_bound`, `lemma:approx_subadditivity` | the standing hypotheses of Sections 2 and 3 (`2d - 2 ≤ η ≤ 2d - 1`, the last wave well defined) are explicit hypotheses | those lemmas assert nothing probabilistic; the section fixes `η` before stating them |
| `prop:dimensional_reduction` | the paper's `d` is written `d + 1` | so that the lower-dimensional lattice is `ℤ^d` rather than `ℤ^{d-1}` |
| `theorem:limit_shape` | "convex domain" is `Convex ℝ B ∧ IsOpen B ∧ B.Nonempty` | a nonempty open convex set is connected, hence a domain |
| the floor `⌊·⌋` of `(2.1)`, `(2.4)` and `(3.1)` | integer division `/` on `ℤ` | `/` on `ℤ` is `Int.ediv`, which rounds towards `-∞` |
| `lemma:square_lower_bound` | "the support of the `m`-wave" is `∃ t, 0 < u_t x` | the wave odometer is nondecreasing in time on a nonnegative background, so this is the support of the terminal odometer when the wave stabilizes, and is the right reading when it does not |
| every statement of Sections 1 to 4 | carries `2 ≤ d` | the standing hypothesis of "Main results", `Suppose d ≥ 2 and η is drawn from a product measure ...` |

## Main results

None of the paper's main results is proved yet.  Their frozen statements are registered, and
[`Exploding/MainTheorems.lean`](Exploding/MainTheorems.lean) names them in its docstring
without restating them; it states in full only the five results that are proved.

| Source | Frozen statement | State |
|---|---|---|
| Theorem 1.2, `theorem:limit_shape` | `Exploding.Frozen.limit_shape` | open |
| Theorem 1.3, `theorem:convergence_of_time_constant` | `Exploding.Frozen.convergence_of_time_constant` | `CONDITIONAL`: proved from Propositions 3.1 and 4.1, which are open, and the cited Theorem 1.1 |
| Theorem 1.4, `theorem:explosive` | `Exploding.Frozen.explosive` | open |
| Theorem 5.1, "Convergence of the exploding sandpile" | `Exploding.Frozen.generalized_convergence` | `CONDITIONAL`: proved from Proposition 5.1, which is open |
| Theorem 6.1, `theorem:counterexample` | `Exploding.Frozen.counterexample` | open |

No comparator challenge exists yet; see [`Audit/README.md`](Audit/README.md).

## Frozen surface

<!-- FROZEN-SURFACE-BEGIN (generated by tools/sync_docs.py) -->

| id | Lean | paper | state |
|---|---|---|---|
| `thm-limit-shape` | [Exploding.Frozen.limit_shape](Exploding/Frozen/LimitShape.lean#L29) | exploding.tex:246-254 (label theorem:limit_shape) | DRAFT_SORRY |
| `thm-time-constant` | [Exploding.Frozen.convergence_of_time_constant](Exploding/Frozen/TimeConstant.lean#L33) | exploding.tex:259-262 (label theorem:convergence_of_time_constant) | CONDITIONAL |
| `thm-explosive` | [Exploding.Frozen.explosive](Exploding/Frozen/Explosive.lean#L22) | exploding.tex:265-268 (label theorem:explosive) | DRAFT_SORRY |
| `prop-renormalization` | [Exploding.Frozen.renormalization_properties](Exploding/Frozen/Renormalization.lean#L35) | exploding.tex:482-497 (label prop:renormalization_properties) | DRAFT_SORRY |
| `lem-square-lower-bound` | [Exploding.Frozen.square_lower_bound](Exploding/Frozen/SquareLowerBound.lean#L22) | exploding.tex:705-707 (label lemma:square_lower_bound) | SEALED |
| `lem-penultimate-cluster` | [Exploding.Frozen.last_penultimate_cluster](Exploding/Frozen/PenultimateCluster.lean#L29) | exploding.tex:792-798 (label lemma:last_penultimate_cluster) | DRAFT_SORRY |
| `lem-penultimate-upper-bound` | [Exploding.Frozen.penultimate_upper_bound](Exploding/Frozen/PenultimateUpperBound.lean#L27) | exploding.tex:807-812 (label lemma:penultimate_upper_bound) | DRAFT_SORRY |
| `lem-penultimate-close` | [Exploding.Frozen.last_penultimate_close](Exploding/Frozen/PenultimateClose.lean#L30) | exploding.tex:832-837 (label lemma:last_penultimate_close) | DRAFT_SORRY |
| `prop-last-wave-convergence` | [Exploding.Frozen.convergence_of_the_last_wave](Exploding/Frozen/LastWaveConvergence.lean#L27) | exploding.tex:846-852 (label prop:convergence_of_the_last_wave) | DRAFT_SORRY |
| `prop-approximate-subadditive` | [Exploding.Frozen.approximate_subadditive](Exploding/Frozen/ApproximateSubadditive.lean#L29) | exploding.tex:886-898 (label prop:approximate_subadditive) | DRAFT_SORRY |
| `prop-generalized-last-wave` | [Exploding.Frozen.convergence_of_the_generalized_last_wave](Exploding/Frozen/GeneralizedLastWave.lean#L32) | exploding.tex:1203-1207 (label prop:convergence_of_the_generalized_last_wave) | DRAFT_SORRY |
| `thm-generalized-convergence` | [Exploding.Frozen.generalized_convergence](Exploding/Frozen/GeneralizedConvergence.lean#L33) | exploding.tex:1249-1253 (Convergence of the exploding sandpile) | CONDITIONAL |
| `thm-counterexample` | [Exploding.Frozen.counterexample](Exploding/Frozen/Counterexample.lean#L25) | exploding.tex:1351-1361 (label theorem:counterexample) | DRAFT_SORRY |
| `prop-explosion-criteria` | [Exploding.Frozen.explosion_criteria](Exploding/Frozen/ExplosionCriteria.lean#L18) | exploding.tex:1821-1825 (label prop:explosion_criteria) | DRAFT_SORRY |
| `prop-box-crossing` | [Exploding.Frozen.box_crossing](Exploding/Frozen/BoxCrossing.lean#L21) | exploding.tex:1986-1988 (P is box-crossing) | DRAFT_SORRY |
| `ext-fey-levine-peres` | [Exploding.External.FeyLevinePeresExplosive](Exploding/External/FeyLevinePeres.lean#L18) | exploding.tex:238-240 (label prop:fey_levine_peres_explode) | FROZEN |
| `ext-schonmann-bootstrap` | [Exploding.External.SchonmannBootstrap](Exploding/External/Schonmann.lean#L23) | exploding.tex:1969-1981 (label prop:schonnmann_bootstrap) | FROZEN |
| `ext-liggett-schonmann-stacey` | [Exploding.External.LiggettSchonmannStacey](Exploding/External/LiggettSchonmannStacey.lean#L26) | liggett1997domination Theorem 0.0, cited at exploding.tex:1215-1217 in the proof of prop:convergence_of_the_generalized_last_wave | FROZEN |
| `ext-lss-bounded-degree` | [Exploding.External.LiggettSchonmannStaceyBoundedDegree](Exploding/External/LiggettSchonmannStaceyBoundedDegree.lean#L31) | liggett1997domination Corollary 1.4, cited at exploding.tex:478 for prop:renormalization_properties | FROZEN |
| `ext-antal-pisztora` | [Exploding.External.AntalPisztoraChemicalDistance](Exploding/External/AntalPisztora.lean#L29) | antal1996chemical Theorem 1.1, cited at exploding.tex:478 for prop:renormalization_properties | FROZEN |
| `ext-mathieu-holes` | [Exploding.External.MathieuHoleVolume](Exploding/External/MathieuHoles.lean#L28) | mathieu2008quenched Lemma 5.2, cited at exploding.tex:478 for prop:renormalization_properties | FROZEN |
| `ext-fey-meester-redig` | [Exploding.External.FeyMeesterRedigLeastAction](Exploding/External/FeyMeesterRedig.lean#L40) | fey2009stabilizability Theorem 2.8, cited at exploding.tex:1415-1424 in the proof of theorem:counterexample | FROZEN |
| `lem-last-wave-bound` | [Exploding.Frozen.last_wave_bound](Exploding/Frozen/LastWaveBound.lean#L24) | exploding.tex:730-735 (label lemma:last_wave_bound) | SEALED |
| `prop-dimensional-reduction` | [Exploding.Frozen.dimensional_reduction](Exploding/Frozen/DimensionalReduction.lean#L24) | exploding.tex:1890-1899 (label prop:dimensional_reduction) | SEALED |
| `lem-approx-subadditivity` | [Exploding.Frozen.approx_subadditivity](Exploding/Frozen/ApproxSubadditivity.lean#L105) | exploding.tex:760-765 (label lemma:approx_subadditivity) | SEALED |
| `prop-recurrence` | [Exploding.Frozen.recurrence](Exploding/Frozen/Recurrence.lean#L17) | exploding.tex:1927-1929 (label prop:recurrence) | SEALED |
| `lem-local-convexity` | [Exploding.Frozen.local_convexity](Exploding/Frozen/LocalConvexity.lean#L20) | exploding.tex:531-535 (label lemma:local_convexity) | SEALED |
| `lem-finite-exploding` | [Exploding.Frozen.finite_exploding](Exploding/Frozen/FiniteExploding.lean#L27) | exploding.tex:720-722 (label lemma:finite_exploding) | CONDITIONAL |
| `prop-crossing-time` | [Exploding.Frozen.crossing_time](Exploding/Frozen/CrossingTime.lean#L20) | exploding.tex:416-422 (label prop:crossing_time) | SEALED |

<!-- FROZEN-SURFACE-END -->
