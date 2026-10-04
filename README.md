# Exploding-Sandpiles

A **Lean 4** formalization of the paper

> Ahmed Bou-Rabee,
> [*A shape theorem for exploding sandpiles*](https://arxiv.org/abs/2102.04422),
> Annals of Applied Probability 34(1A) (2024), 714-742; arXiv:2102.04422.

Every result that the paper proves is proved in Lean, with the results that the paper cites
from the literature as explicit hypotheses. Of the seven cited results, six are also proved
in this repository and one is assumed: the chemical-distance bound of Antal and Pisztora.
The development is built on
[`mathlib`](https://github.com/leanprover-community/mathlib4) and the shared library
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability) (`LatticeProb`).

[![CI](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/comparator.yml)

## What is proved

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

Every theorem, lemma and proposition of the paper is registered as a frozen Lean statement
(`tools/check_coverage.py`), and the seven further results that the paper cites are
registered as assumptions, 29 registered statements in all.  The 22 results that the paper
proves are proved, each reducing to only the three standard axioms `propext`,
`Classical.choice` and `Quot.sound`: Theorems 1.2, 1.3, 1.4, 5.1 and 6.1, Propositions 2.1,
2.2, 3.1, 4.1, 5.1, 7.1, 7.2, 7.3 and 7.5, and Lemmas 2.1 and 3.1 to 3.7.  Theorem 1.1 and
Proposition 7.4 are results the paper quotes without proof, and are among the seven cited
results below.

[`Exploding/MainTheorems.lean`](Exploding/MainTheorems.lean) restates every proved result of
the paper, each by `exact` of its certified counterpart in `Exploding/Frozen/`, so the
statements displayed there are the certified ones.  The main theorems, with their paper
labels and certified statements, are:

- **Theorem 1.2, the limit shape** (`theorem:limit_shape`, `Exploding.Frozen.limit_shape`):
  for `d ≥ 2` and `0 < p < 1` there is a nonempty open convex set `B ⊂ ℝ^d` such that, for
  almost every background `η` of `(1.2)`, the Lebesgue measure of the symmetric difference of
  `B` and `{y | v_t([t y]) > 0}` tends to `0`.
- **Theorem 1.3, the time constant** (`theorem:convergence_of_time_constant`,
  `Exploding.Frozen.convergence_of_time_constant`): there is a continuous, convex,
  one-homogeneous `N : ℝ^d → ℝ` such that almost surely the background is explosive, every
  arrival time is finite, and `n⁻¹ T_η([n y])` converges to `N y` uniformly on every compact
  set.
- **Theorem 1.4** (`theorem:explosive`, `Exploding.Frozen.explosive`): a product background
  with at least `d` chips at every site and a positive probability of `2d - 1` chips at a
  site is explosive almost surely.
- **Theorem 5.1, convergence under the general hypotheses** (`Exploding.Frozen.generalized_convergence`):
  under the hypotheses of Section 5, almost surely the background is explosive and the
  rescaled arrival times converge locally uniformly to a deterministic, continuous, convex,
  one-homogeneous function.
- **Theorem 6.1, no limit shape** (`theorem:counterexample`, `Exploding.Frozen.counterexample`):
  for `d ≥ 2` there is an explosive background `η ≱ 2d - 2` with finite arrival times `T(n)`
  at `n e_1`, `limsup n⁻¹ T(n) ≥ 3/2` and `liminf n⁻¹ T(n) = 1`.

Highlights among the proved results:

* **`Exploding.square_lower_bound`** (Lemma 3.1): on a nonnegative background, for `n ≥ 1`
  and `m ≥ (2d)^{dn}`, the `m`-wave from the origin reaches every site of `[-n, n]^d`.
* **`Exploding.last_wave_bound`** (Lemma 3.3): for `2d - 2 ≤ η ≤ 2d - 1` with a well-defined
  last wave, the last wave exceeds the penultimate wave by at most one.
* **`Exploding.approx_subadditivity`** (Lemma 3.4): under the same hypotheses, the
  penultimate-cluster arrival times are subadditive.
* **`Exploding.dimensional_reduction`** (Proposition 7.2): on a face of the box, the
  constrained process in `ℤ^{d+1}` runs the one in `ℤ^d`.
* **`Exploding.recurrence`** (Proposition 7.3): the constant background `d` is recurrent.

**What is assumed.**  The seven cited results are stated in Lean as propositions in
`Exploding/External/` and carried as explicit hypotheses by the frozen statements, so a
theorem whose proof uses one shows exactly what it rests on; no `axiom` is declared.
[`ASSUMPTIONS.md`](ASSUMPTIONS.md) lists all seven with their verbatim Lean statements.  The
certified statements carry them as follows, where `perc` stands for the three percolation
results `hLSSB` (Corollary 1.4 of Liggett, Schonmann and Stacey), `hHole` (Lemma 5.2 of
Mathieu) and `hChem` (Theorem 1.1 of Antal and Pisztora):

| statement | cited hypotheses carried |
|---|---|
| Theorem 1.2 | `perc`, `hSch` (Schonmann's bound, Proposition 7.4) |
| Theorem 1.3 | `perc`, `hFLP` (Theorem 1.1, Fey, Levine and Peres) |
| Theorem 1.4, Proposition 7.5 | `hSch` |
| Proposition 2.2, Lemmas 3.2, 3.5, 3.6 and 3.7, Propositions 3.1 and 4.1 | `perc` |
| Proposition 5.1, Theorem 5.1 | `perc`, `hLSS` (Theorem 0.0 of Liggett, Schonmann and Stacey) |
| Theorem 6.1 | `hFMR` (Theorem 2.8 of Fey, Meester and Redig) |
| Propositions 2.1, 7.1, 7.2 and 7.3, Lemmas 2.1, 3.1, 3.3 and 3.4 | none |

Propositions 5.1 and 7.1 and Theorem 5.1 also carry the model hypotheses of Sections 5 and 7
(finite range of dependence, path-filling, box-crossing, recurrence, wave approximation);
these are assumptions on the law of the background, not cited results.

Six of the seven cited results are proved in this repository, so the hypothesis can be
discharged by the proof named:

- `hFMR` by `Exploding.xfmr_proved` (`Exploding/Support/ExtFMR.lean`);
- `hLSSB` by `Exploding.xlse_lss_bounded_degree` and `hLSS` by `Exploding.xlse_lss_general`
  (`Exploding/Support/ExtLSSCountable.lean`);
- `hHole` by `Exploding.xmf_proved` (`Exploding/Support/ExtMHHoleVolume.lean`);
- `hSch` by `Exploding.xsr_schonmann` (`Exploding/Support/ExtSchFinal.lean`);
- `hFLP` by `Exploding.xsr_flp` (`Exploding/Support/ExtSchFLP.lean`), which applies
  `Exploding.LSProof.ls_flp_from_explosive` (`Exploding/Support/LSProofAux.lean`) to
  `Exploding.xsr_schonmann`; that derivation is available because Theorem 1.4 strengthens
  Theorem 1.1, and the proof of Theorem 1.2 already uses it.

Only `hChem` (`Exploding.External.AntalPisztoraChemicalDistance`) is assumed outright.  The
frozen statements still take all of the cited results as hypotheses, as in the table;
discharging them with the proofs above, Theorem 6.1 (`hFMR := Exploding.xfmr_proved`),
Theorem 1.4 and Proposition 7.5 (`hSch := Exploding.xsr_schonmann`) hold with no cited
hypothesis; Theorems 1.2 and 1.3 rest on `hChem` alone; and Proposition 2.2, Lemmas 3.2, 3.5,
3.6 and 3.7, Propositions 3.1, 4.1 and 5.1 and Theorem 5.1 rest on `hChem` alone, the last
two together with the model hypotheses above.  The paper-to-Lean map of the cited results is
in [`CORRESPONDENCE.md`](CORRESPONDENCE.md).

Not formalized: the proof outline of Section 1, the examples of Section 5.2 and the figures.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **29 registered statements: 1 `SEALED`, proved here; 21 `PROVED`, proved here and independently audited; and 7 `FROZEN`, cited results carried as hypotheses.**  The 22 proved nodes are machine-checked, and each one's axiom
closure is exactly Lean's three standard axioms `propext`,
`Classical.choice` and `Quot.sound`.  The 7 `FROZEN` nodes, `ext-fey-levine-peres`, `ext-schonmann-bootstrap`, `ext-liggett-schonmann-stacey`, `ext-lss-bounded-degree`, `ext-antal-pisztora`, `ext-mathieu-holes` and `ext-fey-meester-redig`, are cited results,
stated in `Exploding/External/` and carried as explicit hypotheses by the
theorems that use them; those theorems do not prove them, and ASSUMPTIONS.md
marks which are also proved elsewhere in this repository.  No node is open.  Run `python3 tools/check_axioms.py` to see the axiom closure of every node;
it fails while any closure contains `sorryAx`.  These counts are generated
from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`.

<!-- STATUS-END -->

### Scope and faithfulness

Every theorem, lemma and proposition of the paper is registered as a Lean declaration, one
node for each of its 24 numbered statements.  The paper formalized is the corrected copy
`paper/exploding.tex`, and [`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) lists
each place where it differs from the arXiv version.  It is the source of the Annals of
Applied Probability submission of arXiv:2102.04422v2, corrected where the arXiv text was
wrong; it needs the `imsart` class to compile, and its figures are not included.  The
unmodified arXiv source is `paper/exploding-arxiv.tex`.  The following words have fixed
meanings.

| term | meaning |
|---|---|
| **registered statement**, also called a **node** | one Lean declaration transcribing one statement of the paper. Each has an entry in `ledger/manifest.yaml`. |
| **frozen statement** | the declaration's text between the lines `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`, pinned by the SHA-256 of those bytes. It cannot change without the change being recorded in the manifest. The proof after the end marker may be rewritten freely. |
| **`SEALED`** | the node is **proved** here: a complete proof, whose axiom closure contains only `propext`, `Classical.choice` and `Quot.sound`. |
| **`FROZEN`** | a result the paper cites and does not prove, stated as a proposition in `Exploding/External/` and carried as an explicit hypothesis by the statements that use it. [`ASSUMPTIONS.md`](ASSUMPTIONS.md) marks the six of the seven that this repository also proves. |
| **axiom closure** | the axioms a proof ultimately rests on, as reported by Lean's `#print axioms`. |
| **`sorryAx`** | the axiom Lean inserts for an unproved `sorry`; its presence in an axiom closure means the result is not proved. |

The word *frozen* carries two senses, so it is worth separating them: every registered
statement is frozen in the sense of being **pinned by hash**, while the state `FROZEN` marks
a cited result that the statements using it **take as a hypothesis**.

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
counts and exponents for the nodes that have a recorded reading; no node has one, so both
check nothing.  These are review aids; none proves equivalence between LaTeX and Lean.

### Which Lean statement formalizes which result

The table links the paper's statements to the frozen Lean declarations and gives each one's
state.  It is generated from the manifest and the paper; it does not prove mathematical
correspondence between the two sources.

<!-- PAPER-MAP-BEGIN (generated by tools/sync_docs.py) -->

| Paper result | Description | Lean statement | State |
|---|---|---|---|
| [Theorem 1.1](paper/exploding.tex#L238)<br>`prop:fey_levine_peres_explode` | Explosion of the Bernoulli background (Fey, Levine and Peres), cited | [Exploding.External.FeyLevinePeresExplosive](Exploding/External/FeyLevinePeres.lean#L18) | cited result, hypothesis |
| [Theorem 1.2](paper/exploding.tex#L246)<br>`theorem:limit_shape` | The rescaled toppled region converges to a convex domain | [Exploding.Frozen.limit_shape](Exploding/Frozen/LimitShape.lean#L30) | proved, independently audited |
| [Theorem 1.3](paper/exploding.tex#L259)<br>`theorem:convergence_of_time_constant` | The rescaled arrival times converge | [Exploding.Frozen.convergence_of_time_constant](Exploding/Frozen/TimeConstant.lean#L33) | proved, independently audited |
| [Theorem 1.4](paper/exploding.tex#L265)<br>`theorem:explosive` | A criterion for a product background to explode | [Exploding.Frozen.explosive](Exploding/Frozen/Explosive.lean#L28) | proved, independently audited |
| [Proposition 2.1](paper/exploding.tex#L416)<br>`prop:crossing_time` | Large boxes are crossed quickly | [Exploding.Frozen.crossing_time](Exploding/Frozen/CrossingTime.lean#L20) | proved, independently audited |
| [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | Domination by a product measure on a dependence graph of bounded degree (Liggett, Schonmann and Stacey), cited | [Exploding.External.LiggettSchonmannStaceyBoundedDegree](Exploding/External/LiggettSchonmannStaceyBoundedDegree.lean#L31) | cited result, hypothesis |
| [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | The chemical distance in supercritical bond percolation (Antal and Pisztora), cited | [Exploding.External.AntalPisztoraChemicalDistance](Exploding/External/AntalPisztora.lean#L29) | cited result, hypothesis |
| [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | The holes of the infinite cluster of site percolation (Mathieu), cited | [Exploding.External.MathieuHoleVolume](Exploding/External/MathieuHoles.lean#L28) | cited result, hypothesis |
| [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | The infinite cluster of good cubes | [Exploding.Frozen.renormalization_properties](Exploding/Frozen/Renormalization.lean#L37) | proved, independently audited |
| [Lemma 2.1](paper/exploding.tex#L531)<br>`lemma:local_convexity` | A path of topplings fills its bounding rectangle | [Exploding.Frozen.local_convexity](Exploding/Frozen/LocalConvexity.lean#L20) | proved, independently audited |
| [Lemma 3.1](paper/exploding.tex#L705)<br>`lemma:square_lower_bound` | A wave of order (2d)^(dn) covers the box of radius n | [Exploding.Frozen.square_lower_bound](Exploding/Frozen/SquareLowerBound.lean#L22) | proved, independently audited |
| [Lemma 3.2](paper/exploding.tex#L720)<br>`lemma:finite_exploding` | The last wave is well defined | [Exploding.Frozen.finite_exploding](Exploding/Frozen/FiniteExploding.lean#L27) | proved |
| [Lemma 3.3](paper/exploding.tex#L730)<br>`lemma:last_wave_bound` | The last wave exceeds the penultimate wave by at most one | [Exploding.Frozen.last_wave_bound](Exploding/Frozen/LastWaveBound.lean#L24) | proved, independently audited |
| [Lemma 3.4](paper/exploding.tex#L760)<br>`lemma:approx_subadditivity` | Penultimate-cluster arrival times are subadditive | [Exploding.Frozen.approx_subadditivity](Exploding/Frozen/ApproxSubadditivity.lean#L105) | proved, independently audited |
| [Lemma 3.5](paper/exploding.tex#L792)<br>`lemma:last_penultimate_cluster` | Penultimate clusters are polylogarithmically small | [Exploding.Frozen.last_penultimate_cluster](Exploding/Frozen/PenultimateCluster.lean#L30) | proved, independently audited |
| [Lemma 3.6](paper/exploding.tex#L807)<br>`lemma:penultimate_upper_bound` | A linear upper bound on last-wave arrival times | [Exploding.Frozen.penultimate_upper_bound](Exploding/Frozen/PenultimateUpperBound.lean#L28) | proved, independently audited |
| [Lemma 3.7](paper/exploding.tex#L832)<br>`lemma:last_penultimate_close` | Last-wave and penultimate-cluster arrival times are close | [Exploding.Frozen.last_penultimate_close](Exploding/Frozen/PenultimateClose.lean#L31) | proved, independently audited |
| [Proposition 3.1](paper/exploding.tex#L846)<br>`prop:convergence_of_the_last_wave` | Convergence of the last wave | [Exploding.Frozen.convergence_of_the_last_wave](Exploding/Frozen/LastWaveConvergence.lean#L34) | proved, independently audited |
| [Proposition 4.1](paper/exploding.tex#L886)<br>`prop:approximate_subadditive` | The last wave approximates the exploding sandpile | [Exploding.Frozen.approximate_subadditive](Exploding/Frozen/ApproximateSubadditive.lean#L35) | proved, independently audited |
| [Proposition 5.1](paper/exploding.tex#L1203)<br>`prop:convergence_of_the_generalized_last_wave` | Convergence of the last wave under the general hypotheses | [Exploding.Frozen.convergence_of_the_generalized_last_wave](Exploding/Frozen/GeneralizedLastWave.lean#L40) | proved, independently audited |
| [Proposition 5.1](paper/exploding.tex#L1203)<br>`prop:convergence_of_the_generalized_last_wave` | Domination of a finitely dependent field by a product measure (Liggett, Schonmann and Stacey), cited | [Exploding.External.LiggettSchonmannStacey](Exploding/External/LiggettSchonmannStacey.lean#L26) | cited result, hypothesis |
| [Theorem 5.1](paper/exploding.tex#L1249) | Convergence of the exploding sandpile under the general hypotheses | [Exploding.Frozen.generalized_convergence](Exploding/Frozen/GeneralizedConvergence.lean#L33) | proved, independently audited |
| [Theorem 6.1](paper/exploding.tex#L1351)<br>`theorem:counterexample` | Explosive backgrounds without a limit shape | [Exploding.Frozen.counterexample](Exploding/Frozen/Counterexample.lean#L29) | proved, independently audited |
| [Theorem 6.1](paper/exploding.tex#L1351)<br>`theorem:counterexample` | The least action principle (Fey, Meester and Redig), cited | [Exploding.External.FeyMeesterRedigLeastAction](Exploding/External/FeyMeesterRedig.lean#L40) | cited result, hypothesis |
| [Proposition 7.1](paper/exploding.tex#L1821)<br>`prop:explosion_criteria` | A criterion for a background law to explode | [Exploding.Frozen.explosion_criteria](Exploding/Frozen/ExplosionCriteria.lean#L19) | proved, independently audited |
| [Proposition 7.2](paper/exploding.tex#L1890)<br>`prop:dimensional_reduction` | Dynamics on a face reduce to one dimension lower | [Exploding.Frozen.dimensional_reduction](Exploding/Frozen/DimensionalReduction.lean#L24) | proved, independently audited |
| [Proposition 7.3](paper/exploding.tex#L1927)<br>`prop:recurrence` | The constant background d is recurrent | [Exploding.Frozen.recurrence](Exploding/Frozen/Recurrence.lean#L17) | proved, independently audited |
| [Proposition 7.4](paper/exploding.tex#L1969)<br>`prop:schonnmann_bootstrap` | Schonmann's bound for bootstrap percolation, cited | [Exploding.External.SchonmannBootstrap](Exploding/External/Schonmann.lean#L23) | cited result, hypothesis |
| [Proposition 7.5](paper/exploding.tex#L1986) | The background of Theorem 1.4 is box-crossing | [Exploding.Frozen.box_crossing](Exploding/Frozen/BoxCrossing.lean#L22) | proved, independently audited |

<!-- PAPER-MAP-END -->

## Guarantees

- **No `sorry`** in the library: `tools/check_manifest.py` finds none under `Exploding/` and
  `tools/check_warnings.py` fails on any `sorry` or other warning in the build.  The cited
  results are propositions carried as hypotheses, not `sorry`.  The comparator challenge
  [`ExplodingAudit/LimitShape/Challenge.lean`](ExplodingAudit/LimitShape/Challenge.lean)
  contains one intentional statement-level `sorry`, which the corresponding solution file
  proves.
- **No custom axiom.** The proved results depend only on mathlib's standard axioms `propext`,
  `Classical.choice` and `Quot.sound`.
  [`Exploding/Meta/AxiomsAudit.lean`](Exploding/Meta/AxiomsAudit.lean) prints the axiom
  dependencies of the results restated in
  [`Exploding/MainTheorems.lean`](Exploding/MainTheorems.lean) and of the proofs of the six
  cited results that are proved here, `tools/check_axioms.py` does so for every registered
  statement, and the axiom-audit step of the CI workflow fails on any axiom other than these
  three.  The cited results are hypotheses, not axioms.
- **Independent check of the statement.** The limit shape theorem (Theorem 1.2) is restated,
  with the model rebuilt from mathlib primitives alone, in
  [`ExplodingAudit/LimitShape/Challenge.lean`](ExplodingAudit/LimitShape/Challenge.lean),
  together with the four cited results the theorem takes as hypotheses: `hLSSB`, `hHole`,
  `hChem` and `hSch`, of which only `hChem` is assumed outright in this repository (`hLSSB`,
  `hHole` and `hSch` are proved here, by `Exploding.xlse_lss_bounded_degree`,
  `Exploding.xmf_proved` and `Exploding.xsr_schonmann`).  The comparator workflow
  ([`.github/workflows/comparator.yml`](.github/workflows/comparator.yml)) submits the
  challenge and its solution to [leanprover/comparator](https://github.com/leanprover/comparator),
  which checks that the restatement is proved from the library through an independent
  implementation of the Lean kernel; the check covers the theorem with those four
  hypotheses.  See [`ExplodingAudit/README.md`](ExplodingAudit/README.md).
- **Pinned toolchain.** Lean `v4.32.0`; mathlib at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997`; `Lattice-Probability` at revision
  `bbe0b90a7cf0517db0578139aaab7f152edbc45e`; and the dependencies of mathlib (`plausible`,
  `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, `Cli`) at
  the revisions recorded in [`lake-manifest.json`](lake-manifest.json).

## Size

About 59,700 lines of Lean in 304 modules (`Exploding.lean` and `Exploding/`; the audit
directory is not counted), of which about 47,600 lines are code once comments and blank
lines are removed, on top of mathlib and the `Lattice-Probability` library.

## Building

The project uses [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager)
and Lake.  The toolchain is pinned in [`lean-toolchain`](lean-toolchain)
(`leanprover/lean4:v4.32.0`), so `elan` installs the right Lean version automatically, and
the dependencies are pinned to commits in `lakefile.lean` and
[`lake-manifest.json`](lake-manifest.json); `lake` fetches them, and there is nothing to
clone by hand.

```bash
lake exe cache get                      # prebuilt mathlib
lake build                              # the library
lake build ExplodingAudit               # the Mathlib-only comparator surface
lake build Exploding.Meta.AxiomsAudit   # print the axioms of the proved results
```

The build emits no warning.  `import Exploding` loads the whole development and
`import Exploding.MainTheorems` the proved results.

The comparator check of Theorem 1.2 is run from the repository root with
`leanprover/comparator` at commit `575674928e239f5bc452aab72d1dd7b0f1326494`, `lean4export`
at the tag of `lean-toolchain` (`v4.32.0`), nanoda at
`6ae1f0cd962f081f6c423454c5da729d841236a7` and landrun at
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`:

```bash
bash ExplodingAudit/check_standalone.sh ExplodingAudit/LimitShape/Challenge.lean  # one expected `sorry` warning
bash ExplodingAudit/check_standalone.sh --vocabulary                              # Challenge vs SolutionBasic
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ExplodingAudit/LimitShape/comparator.json
```

It prints `Your solution is okay!`; see [`ExplodingAudit/README.md`](ExplodingAudit/README.md).

The checkers in `tools/` need Python 3.10 or newer and PyYAML
(`python3 -m pip install -r tools/requirements.txt`).  `python3 tools/verify.py` runs every
check below and fails on the first failure; the CI workflow runs it on request.
`check_axioms.py` and `check_warnings.py` run Lean; the others read the manifest, the paper
and the Lean sources.

| command | what it guarantees |
|---|---|
| `python3 tools/check_manifest.py` | every node's file holds exactly one frozen block whose SHA-256 equals `frozen_sha256` and which declares exactly the node's `export`; every file in `Exploding/Frozen/` belongs to one node; `Exploding/` contains no `axiom`, `admit`, `sorryAx` or `sorry` |
| `python3 tools/check_axioms.py` | runs `#print axioms` on every manifest export and lists which closures contain `sorryAx`; it fails if any does, and `tools/verify.py` checks that the closures agree with the recorded states |
| `python3 tools/check_warnings.py` | `lake build Exploding` emits no warning |
| `python3 tools/check_constants.py` | in a frozen statement whose conclusion has an existential constant, the constant is bound before the paper's parameters |
| `python3 tools/check_coverage.py` | every theorem, lemma and proposition of `paper/exploding.tex` is named in the `source` of some manifest node |
| `python3 tools/check_clauses.py` | compares the assertion count of each paper statement with the conjunct count of its Lean statement, for the nodes with a recorded reading (none) |
| `python3 tools/check_exponents.py` | compares the exponents written in a paper statement with those in its Lean statement, for the nodes with a recorded reading (none) |

Also in `tools/`: `paper_anchors.py` and `paper_citations.py` check the
`exploding.tex:<lines>` ranges in the manifest and in the Lean docstrings against the paper's
labels; `sync_docs.py` checks (`--write` regenerates) the status block and the paper map of
this file and the frozen-surface table of `CORRESPONDENCE.md`; `assumptions.py` regenerates
`ASSUMPTIONS.md` (`--check` verifies it is current); `freeze.py` registers a frozen statement
in the manifest.

## Repository layout

```
Exploding/
  MainTheorems.lean   the proved results, stated in full; the main theorems named
  Frozen/             the frozen statement surface, one frozen statement per file
  External/           the seven cited results, stated as propositions
  Support/            the model and the lemmas the frozen statements are proved from
    Toppling.lean     parallel toppling, the n-wave, stabilizable, robust and explosive
    Vocab.lean        boxes, crossing times, good cubes, the last wave, the background law
    Hypotheses.lean   the five hypotheses of Section 5
    Reduction.lean    the constrained processes of Section 7.1
    Percolation.lean  Bernoulli site and bond percolation and the dependence graph
    LSProofAux.lean   the assembly of Theorem 1.2, and Theorem 1.1 from Schonmann's bound
    Ext*.lean         the proofs of the cited results that are proved here (ExtFMR, ExtLSS*,
                      ExtMH*, ExtSch*) and lemmas toward the Antal-Pisztora result (ExtAP*),
                      which is assumed
  Meta/               AxiomsAudit.lean
Exploding.lean        the root module (imports the whole library)
ExplodingAudit/       the Mathlib-only restatement of Theorem 1.2 and its solution:
                      README.md, DESIGN.md, LimitShape/ (Challenge, Solution, comparator.json),
                      Support/, check_standalone.sh
ASSUMPTIONS.md        the seven cited results and which are also proved here (generated)
CORRESPONDENCE.md     paper ↔ Lean: conventions, cited inputs, differences, node table
CONTRIBUTING.md       building notes and the elaboration policy for new files
CITATION.cff          citation metadata
formalization.yaml    the disclosure record (models, tooling, review status)
ledger/manifest.yaml  one row per registered statement: hash, paper source, state
paper/exploding.tex   the paper, pinned by the SHA-256 in ledger/manifest.yaml
paper/exploding-arxiv.tex, paper/arxiv/
                      the unmodified arXiv source
paper/CHANGES_FROM_ARXIV.md
                      every difference between the two
tools/                the checkers and generators listed under Building
.github/workflows/    build.yml and comparator.yml
lakefile.lean, lake-manifest.json, lean-toolchain
                      the pinned build
```

## How this was built

The Lean code was written by AI coding agents under the close supervision of the author; the models, tooling and cost are disclosed in [`formalization.yaml`](formalization.yaml).

## Authors, citation, acknowledgements

The Lean development is by **Ahmed Bou-Rabee**, who is also the author of the paper it
formalizes.  If you use this formalization, please cite it using the metadata in
[`CITATION.cff`](CITATION.cff).  This formalization is built on
[Lean 4](https://lean-lang.org), [Mathlib](https://github.com/leanprover-community/mathlib4)
and the shared library
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability).  The seven
cited results it records as hypotheses are due to Fey, Levine and Peres; Schonmann;
Liggett, Schonmann and Stacey; Antal and Pisztora; Mathieu; and Fey, Meester and Redig.

## License

The Lean code in this repository is licensed under the **Apache License 2.0** (see
[`LICENSE`](LICENSE)).  The paper source in `paper/` is included for reference and is not
covered by the Apache license.
