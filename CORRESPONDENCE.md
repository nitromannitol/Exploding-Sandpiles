# Correspondence: paper ↔ Lean

Maps the source-partitioned manifest to A shape theorem for exploding sandpiles
(Bou-Rabee). The default is the corrected journal source; the v4 counterexample and crossing successors
and four literal definitions override it with corrected arXiv-format v10. The official
arXiv v2 extraction is preserved separately and is outside this promotion's certification
scope.

## Conventions

- The global default is paper/exploding.tex, SHA-256
  1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44; row-level
  overrides pin six declarations to corrected arXiv-format v10 and
  its defs.tex input. A source address is tied to its effective pin, range and label
  when present; v10 line 103 has no invented equation label.
- The bytes between `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`
  are the contract.  `python3 tools/check_manifest.py` is the authority on the
  hash recipe.

## External inputs

The seven cited results remain registered in Exploding/External/ under the old source.
A theorem carries one only when its exact frozen type has that binder. The proved v4
counterexample type has no hFMR binder; the historic FMR citation remains in the old
journal-source record.

| node | cited result | used by |
|---|---|---|
| `ext-fey-levine-peres` | Fey, Levine and Peres, *Growth rates and explosions in sandpiles*, Proposition 1.4 | quoted as Theorem 1.1; strengthened by `thm-explosive` |
| `ext-schonmann-bootstrap` | Schonmann, *On the behavior of some cellular automata related to bootstrap percolation*, the large-deviation bound | `prop-box-crossing`, `thm-explosive`, `thm-limit-shape` |
| `ext-liggett-schonmann-stacey` | Liggett, Schonmann and Stacey, *Domination by product measures*, Theorem 0.0 | Section 5: `prop-generalized-last-wave`, `thm-generalized-convergence` |
| `ext-lss-bounded-degree` | Liggett, Schonmann and Stacey, *Domination by product measures*, Corollary 1.4 | Proposition 2.2 and every statement that uses it |
| `ext-antal-pisztora` | Antal and Pisztora, *On the chemical distance for supercritical Bernoulli percolation*, Theorem 1.1, for bond percolation | Proposition 2.2 and every statement that uses it |
| `ext-mathieu-holes` | Mathieu, *Quenched invariance principles for random walks with random conductances*, Lemma 5.2 | Proposition 2.2 and every statement that uses it |
| `ext-fey-meester-redig` | Fey, Meester and Redig, *Stabilizability and percolation in the infinite volume sandpile model*, Theorem 2.8 | preserved historical journal-source record; not a premise of proved v4 |

Six of the seven are proved in this repository, so the hypothesis can be discharged:
`ext-fey-meester-redig` by `Exploding.xfmr_proved`, `ext-lss-bounded-degree` by
`Exploding.xlse_lss_bounded_degree`, `ext-liggett-schonmann-stacey` by
`Exploding.xlse_lss_general`, `ext-mathieu-holes` by `Exploding.xmf_proved`,
`ext-schonmann-bootstrap` by `Exploding.xsr_schonmann`, and `ext-fey-levine-peres` by
`Exploding.xsr_flp`, which applies `Exploding.LSProof.ls_flp_from_explosive` to
`Exploding.xsr_schonmann`.  Only `ext-antal-pisztora` is assumed outright;
[`ASSUMPTIONS.md`](ASSUMPTIONS.md) gives the statements.

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
| old-source statements of Sections 1 to 4 | carry `2 ≤ d` | the standing hypothesis of the historical "Main results" section; the proved v4 statement has its own explicit `2 ≤ d` binder |
| `s_0' = η` in the frozen-toppling convention (2.3), in Lemma 2.1, the crossing time, Hypotheses 5.2–5.4 and recurrence | the `S`-frozen toppling `fodo S η w₀` evolves `s_t' = η + Δ w_t`, i.e. `s_0 = η` | (2.3) writes `s_0' = s_0 + Δ w_0`, but the paper's later uses and its proofs need the initial firing's chips delivered (`exploding.tex:447`: a `(2d-1)`-site next to a toppled line topples at the next step); the paper's own (2.4) is inconsistent with (2.3) here |
| the Bernoulli probability `p` of `(1.2)` in paper rows | `0 < p ≤ 1` in `lem-finite-exploding@7`, `lem-penultimate-cluster@5`, `lem-penultimate-upper-bound@5`, `lem-penultimate-close@5` and `prop-approximate-subadditive@5`; four remaining strict Bernoulli paper rows retain `0 < p < 1` | Version 7 includes the deterministic `p = 1` endpoint for Lemma 3.2 under the historical source pin. Versions 5 include the endpoints for Lemmas 3.5, 3.6, 3.7 and Proposition 4.1 under the official arXiv pin. The corrected-v10 counterexample is deterministic and has no Bernoulli `p`. The corrected crossing version 4 includes p = 1 under its separate pin. Other corrected-v10 statements remain uncertified. |

## Main results

The remaining old-source theorem rows below retain their narrower journal-source contracts. The
Theorem 1.2 0 < p < 1 row and comparator are historical old-source scope; they do not
certify corrected-v10 endpoints. The proved v4 Theorem 6.1 row has no cited-result binder
and passed exact compiled type, axiom and independent source/body/consumer checks. The four
literal definitions passed source/body audit but add no theorem coverage. The dated
promotion receipt is [ledger/audits/2026-10-15-counterexample-v4-promotion.md](ledger/audits/2026-10-15-counterexample-v4-promotion.md). The corrected Proposition 2.1 terminal-and-deadline successor has its own [validation receipt](ledger/audits/2026-10-15-crossing-v4-promotion.md). Main theorem rows are:

| Source | Frozen statement | State and cited hypotheses carried |
|---|---|---|
| Theorem 1.2, `theorem:limit_shape` | `Exploding.Frozen.limit_shape` | proved; carries the three percolation results behind Proposition 2.2 (`hLSSB`, `hHole`, `hChem`) and Schonmann's bound (`hSch`), which `Exploding.xsr_schonmann` proves |
| Theorem 1.3, `theorem:convergence_of_time_constant` | `Exploding.Frozen.convergence_of_time_constant` | proved; carries the cited Theorem 1.1 (`hFLP`), which `Exploding.xsr_flp` proves, and the three percolation results |
| Theorem 1.4, `theorem:explosive` | `Exploding.Frozen.explosive` | proved; carries Schonmann's bound (`hSch`), which `Exploding.xsr_schonmann` proves |
| Theorem 5.1, "Convergence of the exploding sandpile" | `Exploding.Frozen.generalized_convergence` | proved; carries the general domination theorem (`hLSS`) and the three percolation results |
| Theorem 6.1, `theorem:counterexample` | `Exploding.Frozen.counterexample` | proved exact-source successor: one and the same explosive background supplies the lower-bound, finite-arrival, both axial-limit and measurable-volume clauses; no cited-result binder; independent source/body/consumer audit and integration checks passed |

The historical limit-shape statement (Theorem 1.2) is restated over Mathlib alone and
checked with leanprover/comparator; this covers only its four explicit old-source hypotheses,
not v4 or corrected v10 as a whole. See ExplodingAudit/README.md.

## Frozen surface

<!-- FROZEN-SURFACE-BEGIN (generated by tools/sync_docs.py) -->

| id | Lean | paper | source pin | state |
|---|---|---|---|---|
| `thm-limit-shape` | [Exploding.Frozen.limit_shape](Exploding/Frozen/LimitShape.lean#L30) | exploding.tex:246-254 (label theorem:limit_shape) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `thm-time-constant` | [Exploding.Frozen.convergence_of_time_constant](Exploding/Frozen/TimeConstant.lean#L33) | exploding.tex:259-262 (label theorem:convergence_of_time_constant) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `thm-explosive` | [Exploding.Frozen.explosive](Exploding/Frozen/Explosive.lean#L28) | exploding.tex:265-268 (label theorem:explosive) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `prop-renormalization` | [Exploding.Frozen.renormalization_properties](Exploding/Frozen/Renormalization.lean#L37) | exploding.tex:482-497 (label prop:renormalization_properties) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `lem-square-lower-bound` | [Exploding.Frozen.square_lower_bound](Exploding/Frozen/SquareLowerBound.lean#L22) | exploding.tex:705-707 (label lemma:square_lower_bound) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `lem-penultimate-cluster` | [Exploding.Frozen.last_penultimate_cluster](Exploding/Frozen/PenultimateCluster.lean#L31) | exploding-arxiv.tex:652-658 (label lemma:last_penultimate_cluster) | `paper/exploding-arxiv.tex` (`f12deba6e481a3d8`) | proved, independently audited |
| `lem-penultimate-upper-bound` | [Exploding.Frozen.penultimate_upper_bound](Exploding/Frozen/PenultimateUpperBound.lean#L29) | exploding-arxiv.tex:667-672 (label lemma:penultimate_upper_bound) | `paper/exploding-arxiv.tex` (`f12deba6e481a3d8`) | proved, independently audited |
| `lem-penultimate-close` | [Exploding.Frozen.last_penultimate_close](Exploding/Frozen/PenultimateClose.lean#L32) | exploding-arxiv.tex:692-697 (label lemma:last_penultimate_close) | `paper/exploding-arxiv.tex` (`f12deba6e481a3d8`) | proved, independently audited |
| `prop-last-wave-convergence` | [Exploding.Frozen.convergence_of_the_last_wave](Exploding/Frozen/LastWaveConvergence.lean#L34) | exploding.tex:846-852 (label prop:convergence_of_the_last_wave) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `prop-approximate-subadditive` | [Exploding.Frozen.approximate_subadditive](Exploding/Frozen/ApproximateSubadditive.lean#L34) | exploding-arxiv.tex:740-752 (label prop:approximate_subadditive) | `paper/exploding-arxiv.tex` (`f12deba6e481a3d8`) | proved, independently audited |
| `prop-generalized-last-wave` | [Exploding.Frozen.convergence_of_the_generalized_last_wave](Exploding/Frozen/GeneralizedLastWave.lean#L40) | exploding.tex:1203-1207 (label prop:convergence_of_the_generalized_last_wave) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `thm-generalized-convergence` | [Exploding.Frozen.generalized_convergence](Exploding/Frozen/GeneralizedConvergence.lean#L33) | exploding.tex:1249-1253 (Convergence of the exploding sandpile) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `thm-counterexample` | [Exploding.Frozen.counterexample](Exploding/Frozen/Counterexample.lean#L13) | exploding-corrected-arxiv.tex:1875-1885 (label theorem:counterexample) | `paper/corrected-arxiv/exploding-corrected-arxiv.tex` (`59b5ac1a5cdf80c5`) | proved, independently audited |
| `prop-explosion-criteria` | [Exploding.Frozen.explosion_criteria](Exploding/Frozen/ExplosionCriteria.lean#L19) | exploding.tex:1821-1825 (label prop:explosion_criteria) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `prop-box-crossing` | [Exploding.Frozen.box_crossing](Exploding/Frozen/BoxCrossing.lean#L22) | exploding.tex:1986-1988 (P is box-crossing) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `ext-fey-levine-peres` | [Exploding.External.FeyLevinePeresExplosive](Exploding/External/FeyLevinePeres.lean#L18) | exploding.tex:238-240 (label prop:fey_levine_peres_explode) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | cited result, hypothesis |
| `ext-schonmann-bootstrap` | [Exploding.External.SchonmannBootstrap](Exploding/External/Schonmann.lean#L23) | exploding.tex:1969-1981 (label prop:schonnmann_bootstrap) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | cited result, hypothesis |
| `ext-liggett-schonmann-stacey` | [Exploding.External.LiggettSchonmannStacey](Exploding/External/LiggettSchonmannStacey.lean#L26) | liggett1997domination Theorem 0.0, cited at exploding.tex:1215-1217 in the proof of prop:convergence_of_the_generalized_last_wave | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | cited result, hypothesis |
| `ext-lss-bounded-degree` | [Exploding.External.LiggettSchonmannStaceyBoundedDegree](Exploding/External/LiggettSchonmannStaceyBoundedDegree.lean#L31) | liggett1997domination Corollary 1.4, cited at exploding.tex:478 for prop:renormalization_properties | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | cited result, hypothesis |
| `ext-antal-pisztora` | [Exploding.External.AntalPisztoraChemicalDistance](Exploding/External/AntalPisztora.lean#L29) | antal1996chemical Theorem 1.1, cited at exploding.tex:478 for prop:renormalization_properties | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | cited result, hypothesis |
| `ext-mathieu-holes` | [Exploding.External.MathieuHoleVolume](Exploding/External/MathieuHoles.lean#L28) | mathieu2008quenched Lemma 5.2, cited at exploding.tex:478 for prop:renormalization_properties | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | cited result, hypothesis |
| `ext-fey-meester-redig` | [Exploding.External.FeyMeesterRedigLeastAction](Exploding/External/FeyMeesterRedig.lean#L40) | fey2009stabilizability Theorem 2.8, cited at exploding.tex:1415-1424 in the proof of theorem:counterexample | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | cited result, hypothesis |
| `lem-last-wave-bound` | [Exploding.Frozen.last_wave_bound](Exploding/Frozen/LastWaveBound.lean#L24) | exploding.tex:730-735 (label lemma:last_wave_bound) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `prop-dimensional-reduction` | [Exploding.Frozen.dimensional_reduction](Exploding/Frozen/DimensionalReduction.lean#L24) | exploding.tex:1890-1899 (label prop:dimensional_reduction) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `lem-approx-subadditivity` | [Exploding.Frozen.approx_subadditivity](Exploding/Frozen/ApproxSubadditivity.lean#L105) | exploding.tex:760-765 (label lemma:approx_subadditivity) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `prop-recurrence` | [Exploding.Frozen.recurrence](Exploding/Frozen/Recurrence.lean#L17) | exploding.tex:1927-1929 (label prop:recurrence) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `lem-local-convexity` | [Exploding.Frozen.local_convexity](Exploding/Frozen/LocalConvexity.lean#L20) | exploding.tex:531-535 (label lemma:local_convexity) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `lem-finite-exploding` | [Exploding.Frozen.finite_exploding](Exploding/Frozen/FiniteExploding.lean#L28) | exploding.tex:720-722 (label lemma:finite_exploding) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `prop-crossing-time` | [Exploding.Frozen.crossing_time](Exploding/Frozen/CrossingTime.lean#L14) | exploding-corrected-arxiv.tex:286-292 (label prop:crossing_time) | `paper/corrected-arxiv/exploding-corrected-arxiv.tex` (`59b5ac1a5cdf80c5`) | proved, independently audited |
| `ext-fey-levine-peres-proved` | [Exploding.xsr_flp](Exploding/Support/ExtSchFLP.lean#L8) | exploding.tex:238-240 (label prop:fey_levine_peres_explode) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `ext-schonmann-bootstrap-proved` | [Exploding.xsr_schonmann](Exploding/Support/ExtSchFinal.lean#L72) | exploding.tex:1969-1981 (label prop:schonnmann_bootstrap) | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `ext-liggett-schonmann-stacey-proved` | [Exploding.xlse_lss_general](Exploding/Support/ExtLSSCountable.lean#L120) | in-repo discharge of ext-liggett-schonmann-stacey; liggett1997domination Theorem 0.0, cited at exploding.tex:1215-1217 in the proof of prop:convergence_of_the_generalized_last_wave | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `ext-lss-bounded-degree-proved` | [Exploding.lssBoundedDegree](Exploding/External/LSSBoundedDegreeProved.lean#L8) | in-repo discharge of ext-lss-bounded-degree; liggett1997domination Corollary 1.4, cited at exploding.tex:478 for prop:renormalization_properties | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `ext-mathieu-holes-proved` | [Exploding.xmf_proved](Exploding/Support/ExtMHHoleVolume.lean#L14) | in-repo discharge of ext-mathieu-holes; mathieu2008quenched Lemma 5.2, cited at exploding.tex:478 for prop:renormalization_properties | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `ext-fey-meester-redig-proved` | [Exploding.xfmr_proved](Exploding/Support/ExtFMR.lean#L58) | in-repo discharge of ext-fey-meester-redig; fey2009stabilizability Theorem 2.8, cited at exploding.tex:1415-1424 in the proof of theorem:counterexample | `paper/exploding.tex` (`1d7c2010d8bd29e7`) | proved, independently audited |
| `def-counterexample-threshold` | [Exploding.counterexampleThreshold](Exploding/Frozen/CounterexampleThreshold.lean#L14) | exploding-corrected-arxiv.tex:100-102 (label eq:first_explosion); carrier at 28-39 and context at 99 | `paper/corrected-arxiv/exploding-corrected-arxiv.tex` (`59b5ac1a5cdf80c5`) | FROZEN definition; source/body audit required |
| `def-counterexample-pile` | [Exploding.counterexamplePile](Exploding/Frozen/CounterexamplePile.lean#L13) | exploding-corrected-arxiv.tex:103-103 (literal definition); threshold context at 99-102 | `paper/corrected-arxiv/exploding-corrected-arxiv.tex` (`59b5ac1a5cdf80c5`) | FROZEN definition; source/body audit required |
| `def-counterexample-arrival` | [Exploding.counterexampleArrival](Exploding/Frozen/CounterexampleArrival.lean#L13) | exploding-corrected-arxiv.tex:118 (context label theorem:convergence_of_time_constant); specialization at 1877 | `paper/corrected-arxiv/exploding-corrected-arxiv.tex` (`59b5ac1a5cdf80c5`) | FROZEN definition; source/body audit required |
| `def-counterexample-support` | [Exploding.counterexampleSupport](Exploding/Frozen/CounterexampleSupport.lean#L13) | exploding-corrected-arxiv.tex:109-111 (context label theorem:limit_shape); tie rule at 173-174 and A_t at 2340-2341 | `paper/corrected-arxiv/exploding-corrected-arxiv.tex` (`59b5ac1a5cdf80c5`) | FROZEN definition; source/body audit required |

<!-- FROZEN-SURFACE-END -->

The table retains the historical thm-counterexample@3 identity: old marker SHA-256 c9c8b8778d204a8280a899f7dda2fefda47e85854c1169bb477828b81f191dd3, semantic-closure SHA-256 ff157998636d1fa5296aa50733454d0a0538d591c0824fd6e6fcab3f9e9b4b9e, and whole-file SHA-256 d9e7f60ec00c1dbdc63a690bba7524dd1fd0f31b30b0ccaa03de3c15bd0dc195. Those v3 values do not certify v4. The registry is 29 journal-source rows, four official-ArXiv rows and six corrected-v10 rows; exact allowed gaps are source-partitioned. Coverage is respectively 18/24, 4/24 and 2/24, and definitions add zero theorem coverage. The aggregate is 28 PROVED rows (22 paper-owned across the three pins and six cited-input discharges), 11 FROZEN definitions and zero SEALED rows. All seven historical cited inputs, including FMR, remain registered. The ordinary bond-hole geometry, near-root defective-animal bounds and finite-hole tail add no numbered-theorem coverage; corrected Proposition 2.2, the selected infinite-cluster transfer and its exact alpha constant remain outside this promotion.

The historical crossing @3 statement retains marker SHA-256 `86d88877abf5e6e1dc37f9bf5e1a1552bb04588de3fa050596b1faf4fb3d5e38` in its dated identity record. The corrected @4 type has a different source pin and explicitly displays terminal one, positive time and `k^d`; the historical GoodCube-only correspondence is not reused for it. Its PROVED registration is bound to the corrected source and its separate exact-declaration receipt.
