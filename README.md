# A shape theorem for exploding sandpiles

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee,
> [*A shape theorem for exploding sandpiles*](https://arxiv.org/abs/2102.04422),
> Annals of Applied Probability 34(1A) (2024), 714–742; arXiv:2102.04422.

The formalized text is a corrected edition of the arXiv source (v2), in
[`paper/corrected-arxiv/`](paper/corrected-arxiv/). Its section "Corrections to the published
version" lists every change from arXiv v2, and [the table below](#corrections-to-the-published-version)
repeats that list. The unmodified arXiv v2 source is kept in
[`paper/exploding-arxiv.tex`](paper/exploding-arxiv.tex).

All 22 numbered results of the corrected edition and its Remark 1 have Lean proofs without cited literature hypotheses, with no `sorry` and only the standard axioms. The original registered statements retain their explicit cited hypotheses where indicated below; corresponding unconditional forms discharge them. Theorem 6.1 is stated as published, Theorems 1.2 and 1.3 as published with the law (2) read as one common law at every site, and Theorems 1.4 and 5.1 with the corrections listed in the corrected edition. Theorem 5.1 also assumes Hypothesis 1 in a stronger form than printed, and whether it holds under the printed form is open.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on the public library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability).

[![CI](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/comparator.yml)

## What is proved

A *background* is a function `η : ℤᵈ → ℤ`. Add `n` chips at the origin and topple in parallel;
the background is *explosive* if for some `n` this never stabilizes. Let `M_η` be the least such
`n` and `v_t` the parallel-toppling odometer of `η + M_η δ₀`. In Theorems 1.2 and 1.3, `η` has
independent values, `2d − 1` with probability `p` and `2d − 2` otherwise, with `d ≥ 2` and
`0 < p ≤ 1`.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.2 | `Exploding.limit_shape`; `Exploding.limit_shape_unconditional` | The rescaled toppled region converges in volume to a convex domain. |
| Theorem 1.3 | `Exploding.convergence_of_time_constant`; `Exploding.convergence_of_time_constant_unconditional` | The rescaled arrival times converge locally uniformly. |
| Theorem 1.4 | `Exploding.explosive` | A product background with one-site law `ν` explodes. |
| Theorem 5.1 | `Exploding.generalized_convergence`; `Exploding.generalized_convergence_unconditional` | Convergence under the hypotheses of Section 5. |
| Theorem 6.1 | `Exploding.counterexample` | An explosive background with no limit shape. |

**Theorem 1.2.** There is a
nonempty open convex set `B ⊂ ℝᵈ` such that almost surely `|{y : v_t([t y]) > 0} △ B| → 0` as
`t → ∞`.

**Theorem 1.3.** There is a
continuous, convex, positively one-homogeneous `N` such that almost surely `η` is explosive, every
arrival time `T(x) = min{t ≥ 1 : v_t(x) > 0}` is finite, and `n⁻¹ T([n y]) → N(y)` uniformly on
compact sets.

**Theorem 1.4.** Let `d ≥ 2` and let `ν` be a probability law on `ℤ` with `ν{m ≥ d} = 1` and
`ν{2d − 1} > 0`. A background whose values are independent, each of law `ν`, is explosive almost
surely.

**Theorem 5.1.** Let `d ≥ 2` and
let `P` be a law on backgrounds `η_min ≤ η ≤ 2d − 1` that is stationary and ergodic for a sublattice
of finite index and satisfies Hypotheses 1 and 3 to 5 of Section 5. Then almost surely `η` is
explosive, and `n⁻¹ T([n y])` converges locally uniformly to a deterministic, continuous, convex,
one-homogeneous function.

**Theorem 6.1.** For every `d ≥ 2` there is an explosive background `η`, not bounded below by
`2d − 2`, whose arrival times along `e₁` are finite, satisfy `limsup T(n e₁)/n ≥ 3/2` and
`liminf T(n e₁)/n = 1`, and for which no measurable set is a limit in volume of the rescaled
toppled regions.

The other numbered results are proved in [`Exploding/MainTheorems.lean`](Exploding/MainTheorems.lean), as are Remark 1 and the two results the
paper quotes, Theorem 1.1 (Fey, Levine and Peres) and Proposition 7.4 (Schonmann), which are proved
here for `0 < p ≤ 1`. The map from LaTeX labels to Lean names is in
[`CORRESPONDENCE.md`](CORRESPONDENCE.md).

| Paper | Lean declaration |
| --- | --- |
| Theorem 1.1 (quoted) | `Exploding.fey_levine_peres_explosive` |
| Proposition 2.1 | `Exploding.crossing_time` |
| Proposition 2.2 | `Exploding.renormalization_properties` |
| Lemma 2.1 | `Exploding.local_convexity` |
| Lemma 3.1 | `Exploding.square_lower_bound` |
| Remark 1 | `Exploding.sharp_planar_obstruction` |
| Lemma 3.2 | `Exploding.finite_exploding` |
| Lemma 3.3 | `Exploding.last_wave_bound` |
| Lemma 3.4 | `Exploding.approx_subadditivity` |
| Lemma 3.5 | `Exploding.last_penultimate_cluster` |
| Lemma 3.6 | `Exploding.penultimate_upper_bound` |
| Lemma 3.7 | `Exploding.last_penultimate_close` |
| Proposition 3.1 | `Exploding.convergence_of_the_last_wave` |
| Proposition 4.1 | `Exploding.approximate_subadditive` |
| Proposition 5.1 | `Exploding.convergence_of_the_generalized_last_wave` |
| Proposition 7.1 | `Exploding.explosion_criteria` (`d ≥ 2`); `Exploding.explosion_criteria_dim_one` (`d = 1`) |
| Proposition 7.2 | `Exploding.dimensional_reduction` |
| Proposition 7.3 | `Exploding.recurrence` |
| Proposition 7.4 (quoted) | `Exploding.schonmann_bootstrap` |
| Proposition 7.5 | `Exploding.box_crossing` |

## Corrections to the published version

The corrected edition ends with the section "Corrections to the published version", which lists every change
from arXiv v2 with the published text, the corrected text and the reason. The table summarizes it, in the
same order and with the same numbers.

| Change | Where | Summary |
| --- | --- | --- |
| C01 | Main results, law (2); Notation (Bernoulli) | Law (2) and the $\mathrm{Bernoulli}(a,b,p)$ notation become one marginal per site |
| C02 | Theorems 1.1–1.3, reading of (2); convex domain of Theorem 1.2 | (2) is read as in C01; the convex domain of Theorem 1.2 is a nonempty open convex set, which its proof provides |
| C03 | Theorem 1.4, statement | Product law needs one common marginal; counterexample to the published statement |
| C04 | Section 2, frozen recursion | Odometer takes the maximum with its previous value; $s'_{t+1}=s_0+\Delta w_{t+1}$ |
| C05 | Proposition 2.1 and Lemma 2.1 (Section 2), Hypotheses 2–4 (Section 5), recurrence (Section 7), proof of Proposition 4.1 | Initial seed $s_0'=\eta+\Delta w_0$, not $\eta$ |
| C06 | Section 2, paragraph before Proposition 2.2 (proof) | Percolation bounds: Mathieu applied to the independent site process, Antal–Pisztora to the bond process |
| C07 | Lemma 2.1, initial odometer and caption | $w_0$ defined on the whole lattice; caption $s_0'=2+\Delta\mathbf 1_A$ |
| C08 | Section 3, Lemma 3.1, two paragraphs after proof, Remark 1 | Lemma for every $d\geq2$ with $C_d$; remark gives planar lower bound; $Cn^2$ false in $d=2$ |
| C09 | Section 3, proof of Proposition 3.1 | Comparison of $\tilde T$ at nearby points replaces continuity; integrability via Kac |
| C10 | Section 4, Theorem 1.2 proof | Proof added: $\mathcal B(p)=\{\mathcal N_p<1\}$, level set Lebesgue-null |
| C11 | Section 5 standing assumption; Proposition 5.1; Theorem 5.1 | Assume $d\geq2$; $\eta\equiv0$ counterexample in $d=1$; Hyp 5 vacuous |
| C12 | Hypothesis 1 | Pairwise independence becomes joint independence of finite families; a strengthened hypothesis, not a correction: whether the published form suffices is open |
| C13 | Hypothesis 4, deadline | Deadline $|\mathcal B_k|$ instead of $|k|$; weaker hypothesis |
| C14 | Proof of Proposition 5.1 | Six-step proof; published use of Theorem 4.1 of Levine–Peres [LP09] for $\eta\geq\eta_{\min}$ does not transfer |
| C15 | Section 5.2 examples | Hypotheses 1 and 4 verified for the cloud and checkerboard; Theorem 4.2 sentence replaced; $\mathcal S$ nonempty |
| C16 | Proof of Theorem 6.1 | Failure of convergence in the volume sense of Theorem 1.2, for $d\geq2$ |
| C17 | Proposition 7.1, statement | "Let $d\geq2$"; $d=1$ argued after the proof |
| C18 | Proposition 7.1: sentence before it, setting of Section 7, proof | Proof for $d\geq2$; criterion sentence replaced; criterion applied to $\alpha_d$; $d=1$ paragraph |
| C19 | Proof of Theorem 1.4 | Reduced law $\mathbf P_d$ via $\alpha_d$; recurrence and box-crossing for $\mathbf P_d$; explosion transfers; subsection retitled "$\mathbf P_d$ is recurrent" |
| C20 | Proposition 7.2, setup | Tangential field $\beta$; $\eta^{(d-1)}=\eta^{(d)}(1,\cdot)-1$; $\Delta u_0$ term; interior and other external initial odometers zero |
| C21 | Proposition 7.2, inductive step | Both constrained odometers make the same update |
| C22 | Proposition 7.3: sentence before it, proof | Reduction for $\mathbf P_d$ by monotonicity; decomposition $Q_n=(\mathbf 1+Q_{n-2})\cup\dots$; base cases $n=1,2$ |
| C23 | Proposition 7.5, statement | Box-crossing for $d\geq2$; $d=1$ for every law with $\eta\geq1$ |
| C24 | Proposition 7.5, proof | Proof for $\alpha_d$ with one-marginal layer variables; $d=1$ immediate |
| C25 | Introduction | New subsection Use of artificial intelligence (who wrote the paper and the Lean formalization, what the agents did) and paragraph on the formalization's coverage |
| C26 | Wording | Lemma 2.1 "for every"; Section 5 opening sentence; "ad hoc"; $n\geq1$ and a thin space in the counterexample; "The constraints are" and $\mathbf x_{d-1}$ in Prop 7.2; labels; ties and macros |

## Standing assumptions and scope

1. **Axioms and incomplete proofs.** The library contains no `sorry`, `admit`, `native_decide` or
   new `axiom`. Each main theorem depends on exactly `propext`, `Classical.choice` and
   `Quot.sound`. The registered statements retain the full Antal–Pisztora chemical-distance
   bound as an explicit hypothesis. Its high-density restriction is proved as
   `Exploding.xap12_high_density_bound` and gives unconditional forms of all 11 statements
   that use it. The full statement is proved as
   `Exploding.External.antalPisztoraChemicalDistance_holds`, in every dimension `d ≥ 2` and at
   every density above `p_c`.
2. **Cited results proved here.** All nine cited results are proved in this repository or in
   Lattice-Probability: the theorem of Antal and Pisztora (in dimensions `d ≥ 3` through the slab
   form of the theorem of Grimmett and Marstrand proved in Percolation-Rigidity, whose proof is
   copied here; see [Copied code](#copied-code));
   Liggett, Schonmann and Stacey, Theorem 0.0 and Corollary 1.4; Mathieu, Lemma 5.2; Schonmann's
   bound (Proposition 7.4); Fey, Levine and Peres, Proposition 1.4; and Fey, Meester and Redig,
   Theorem 2.8, which no result uses; the Fey–den Boer–Redig cubical cluster result and the
   Fey–Levine–Peres radius bound. The registered Lemma 3.1 and Remark 1 retain the latter two as
   hypotheses, while `Exploding.square_lower_bound_unconditional` and
   `Exploding.sharp_planar_obstruction_unconditional` discharge both. The cited results and their precise sources are listed in
   [`ASSUMPTIONS.md`](ASSUMPTIONS.md).
3. **Departures.** Hypothesis 1 is used in the form "the values on two finite sets at distance more
   than `K` are independent", meaning that the two families generate independent σ-fields. The
   paper prints pairwise independence. Whether Propositions 5.1 and 7.1 and Theorem 5.1 hold under
   the printed form is open. Proposition 7.1 is stated for `d ≥ 2`; the case `d = 1`, argued in the
   paragraph after its proof, is `Exploding.explosion_criteria_dim_one`, and
   `Exploding.explosion_criteria_of_one_le` covers every `d ≥ 1`. The unconditional route uses only the proved
   high-density case of Antal–Pisztora, whereas the paper cites the full supercritical result;
   the restriction suffices because the paper applies it at density close to one (Section 2,
   line 350). The full supercritical statement is proved by a renormalization that departs from
   the cited proof (see [`CORRESPONDENCE.md`](CORRESPONDENCE.md)).
4. **Conventions.** Arrival times are valued in `ℕ∞`; `[x]` is the nearest lattice point, with ties
   broken by the coordinatewise minimum; locally uniform convergence is stated in its `ε`-form; the
   floor in the toppling rules is integer division on `ℤ`.
5. **Not formalized.** The proof outline of Section 1, the examples of Section 5.2, the qualitative
   claims of Remarks 3, 4 and 5, and the figures.

## Assumed literature inputs

The registered statements retain the following explicit hypothesis, which is proved here as
`Exploding.External.antalPisztoraChemicalDistance_holds`
([`Exploding/External/AntalPisztoraProved.lean`](Exploding/External/AntalPisztoraProved.lean)),
so it can be discharged instead of assumed. Its high-density restriction is proved as
`Exploding.xap12_high_density_bound`; this suffices for the unconditional forms listed below. The
full statement is proved in dimension two as `Exploding.antalPisztora_dim_two`, and
`Exploding.antalPisztoraChemicalDistance_of_boxEstimate` derives it in every dimension from
`Exploding.PisztoraBoxEstimate` for `d ≥ 3`: at every density above `p_c` and at some scale `N`,
outside events of arbitrarily small probability, the cube `[0, N)^d` contains an open path between
two sites at sup-distance at least `N - 1`, and all such paths inside `[-N, 2N)^d` are joined
inside it. This is a consequence of the coarse-graining theorem of Pisztora (1996, Theorem 3.1).
`Exploding.pisztoraBoxEstimate_of_slabConnectivity` proves it from uniform two-point connectivity
in the slabs of cubes, `Exploding.LatticeBond.UniformCubeSlabConnectivity`, above the critical
probability, through the slab crossing estimates of Percolation-Rigidity. That slab connectivity,
the slab form of the theorem of Grimmett and Marstrand, is proved in Percolation-Rigidity
(`Rigidity.Percolation.uniformCubeSlabConnectivity_of_criticalProbability_lt`, transferred here by
`Exploding.latticeBond_uniformCubeSlabConnectivity_of_criticalProbability_lt`). Both parts of
Percolation-Rigidity are copied in `Exploding/Rigidity/` (see [Copied code](#copied-code)).

| Hypothesis | Content | Source | Used by registered statements |
| --- | --- | --- | --- |
| `Exploding.External.AntalPisztoraChemicalDistance` (`hChem`) | For Bernoulli bond percolation on `ℤᵈ`, `d ≥ 2`, with density `q > p_c`, there are `ρ ≥ 1` and `c > 0` such that, for `\|y\|` large, the probability that the chemical distance from `0` to `y` is finite and exceeds `ρ\|y\|` is at most `exp(−c\|y\|)`. | P. Antal and A. Pisztora, *On the chemical distance for supercritical Bernoulli percolation*, Ann. Probab. 24 (1996), Theorem 1.1 | Theorems 1.2, 1.3 and 5.1, Propositions 2.2, 3.1, 4.1 and 5.1, and Lemmas 3.2 and 3.5 to 3.7 |

The corresponding forms without `hChem` are:

- `Exploding.limit_shape_unconditional` and `Exploding.convergence_of_time_constant_unconditional`;
- `Exploding.renormalization_properties_unconditional` and `Exploding.finite_exploding_unconditional`;
- `Exploding.last_penultimate_cluster_unconditional`, `Exploding.penultimate_upper_bound_unconditional`, and `Exploding.last_penultimate_close_unconditional`;
- `Exploding.convergence_of_the_last_wave_unconditional` and `Exploding.approximate_subadditive_unconditional`;
- `Exploding.convergence_of_the_generalized_last_wave_unconditional` and `Exploding.generalized_convergence_unconditional`.

[`ASSUMPTIONS.md`](ASSUMPTIONS.md) gives the Lean text of every cited result and identifies their proofs.

## Guarantees

All 22 numbered results of the corrected edition and its Remark 1 have Lean proofs without cited literature hypotheses, with no `sorry` and only the standard axioms. The original registered statements retain their explicit cited hypotheses where indicated below; corresponding unconditional forms discharge them. Theorem 6.1 is stated as published, Theorems 1.2 and 1.3 as published with the law (2) read as one common law at every site, and Theorems 1.4 and 5.1 with the corrections listed in the corrected edition. Theorem 5.1 also assumes Hypothesis 1 in a stronger form than printed, and whether it holds under the printed form is open.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **42 statements: 29 proved; 9 cited results; 4 definitions.**

Each statement is taken from one source file. For each source the table gives its theorem statements, how many of them are proved, the cited results stated as hypotheses, and the definitions stated separately.

| Source | SHA-256 | Theorem statements | Proved | Cited results | Definitions |
|---|---|---|---|---|---|
| [paper/corrected-arxiv/exploding-corrected-arxiv.tex](paper/corrected-arxiv/exploding-corrected-arxiv.tex) | `ee4b05b340bff74811db1c3ed88ac7b0ad3fd324f0dad5a52393bc4971c0c8b0` | 29 | 29 | 9 | 4 |

Cited results appear as explicit hypotheses in registered statements; some can be discharged by proofs in the library (see ASSUMPTIONS.md). Definitions are not counted as theorems. These counts are generated from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`; `python3 tools/check_axioms.py` checks the axiom closures.

<!-- STATUS-END -->

- **No `sorry`.** The build emits no warning and contains no `sorry` in `Exploding/`. The
  comparator challenge [`ExplodingAudit/LimitShape/Challenge.lean`](ExplodingAudit/LimitShape/Challenge.lean)
  has one intentional statement-level `sorry`.
- **Standard axioms only.** [`Exploding/Meta/AxiomsAudit.lean`](Exploding/Meta/AxiomsAudit.lean)
  prints the axioms of 126 theorems, and [`scripts/check_axioms.py`](scripts/check_axioms.py)
  requires exactly `propext`, `Classical.choice` and `Quot.sound` for each theorem of its explicit
  list.
- **Independent check of the statements.** The Mathlib-only pair [`ExplodingAudit/LimitShape/`](ExplodingAudit/LimitShape/)
  restates Theorem 1.2 for `0 < p ≤ 1` over Mathlib alone, with the four cited results its
  statement takes as hypotheses. It is the only pair.
- **Pinned toolchain and dependencies.** Lean `v4.35.0-rc2`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` and
  Lattice-Probability `7f773dd0aa66dbe1ed1080ae0248906b9cfe5215`, as recorded in
  [`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json) (see
  [Building](#building)).
- **The paper is part of the repository.** The statement map refers to the corrected edition in
  [`paper/corrected-arxiv/`](paper/corrected-arxiv/), whose source
  `exploding-corrected-arxiv.tex` has SHA-256
  `ee4b05b340bff74811db1c3ed88ac7b0ad3fd324f0dad5a52393bc4971c0c8b0`. The unmodified arXiv v2
  source [`paper/exploding-arxiv.tex`](paper/exploding-arxiv.tex) has SHA-256
  `f12deba6e481a3d81c6967bc48ecbbdae1df4fa1c5f6248a38990030b308072d`.
- **Statement hashes.** The SHA-256 of each statement is recorded in
  [`ledger/manifest.yaml`](ledger/manifest.yaml). `python3 tools/verify.py` checks the hashes, the
  correspondence with the paper and the axiom closures.

## Size

The library consists of `Exploding.lean` and the modules under `Exploding/`, on top of Mathlib and
Lattice-Probability. The comparator sources are under `ExplodingAudit/`.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get                                 # prebuilt Mathlib
lake build                                         # the library
lake build Exploding.Meta.AxiomsAudit 2>&1 | tee axioms-audit.log
python3 scripts/check_axioms.py axioms-audit.log   # the axioms of the main results
lake build ExplodingAudit                          # the comparator surface
python3 tools/verify.py                            # every check; needs PyYAML
```

PyYAML is installed by `python3 -m pip install -r tools/requirements.txt`.
[`CONTRIBUTING.md`](CONTRIBUTING.md) describes each check.

Lattice-Probability has no prebuilt cache, so the first build compiles it as well as the library.
It is a public repository, pinned in [`lake-manifest.json`](lake-manifest.json):

- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `7f773dd0aa66dbe1ed1080ae0248906b9cfe5215`.

`import Exploding` loads the numbered results and what they use.

## Running the comparators

The comparator pair is [`ExplodingAudit/LimitShape/`](ExplodingAudit/LimitShape/). Its
[`comparator.json`](ExplodingAudit/LimitShape/comparator.json) permits exactly `propext`,
`Classical.choice` and `Quot.sound`, and enables the nanoda kernel. Build `leanprover/comparator`,
`lean4export`, `nanoda` and `landrun` at the revisions listed in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), then run from the
repository root

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ExplodingAudit/LimitShape/comparator.json
```

which prints `Your solution is okay!`. The [comparator workflow](.github/workflows/comparator.yml)
runs the pair on manual dispatch, and [`ExplodingAudit/README.md`](ExplodingAudit/README.md)
describes it.

There are two continuous-integration workflows: **CI** builds the library with the zero-warning
check, runs the axiom audit and `tools/verify.py` and builds the comparator surface; **Comparator
audit** checks the pair. CI runs on pushes to `main` that change more than documentation (`*.md`),
the compiled paper PDFs, `formalization.yaml` or `CITATION.cff`; the comparator audit runs when it
is started manually. Both workflows can be started manually from the
[Actions page](https://github.com/nitromannitol/Exploding-Sandpiles/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
Exploding/
  MainTheorems.lean   the numbered results, stated in full
  Frozen/             one statement per file, each followed by its proof
  External/           the cited results, stated as propositions
  Support/            the model and the lemmas the statements are proved from
  Rigidity/           slab connectivity and slab crossing estimates copied from
                      Percolation-Rigidity, with headers (see Copied code)
  Meta/               AxiomsAudit.lean
Exploding.lean        the root module
ExplodingAudit/       the Mathlib-only comparator pair, its solution and checks
paper/corrected-arxiv/      the corrected edition: source, bibliography, figures, source note
paper/exploding-arxiv.tex   the unmodified arXiv v2 source
paper/README.md             the texts in paper/
ledger/manifest.yaml        the statements, with their SHA-256 and sources
ASSUMPTIONS.md              the cited results and where each is proved
CORRESPONDENCE.md           paper ↔ Lean: conventions, cited inputs, statement table
CONTRIBUTING.md             building notes and checks
LICENSE                     the Apache License 2.0
CITATION.cff                citation metadata
formalization.yaml          source, statement, automation and review metadata
scripts/                    check_axioms.py, the explicit-list axiom check
tools/                      verify.py and the checkers it runs
.github/workflows/          build.yml and comparator.yml
lakefile.lean, lake-manifest.json, lean-toolchain   the build
```

## Copied code

Some modules are copied from other public repositories, with attribution, and not through a Lake
dependency. Each copied file starts with a header naming its source repository, commit and file,
and the changes made.

| Source | Commit | Modules |
| --- | --- | --- |
| [Percolation-Rigidity](https://github.com/nitromannitol/Percolation-Rigidity) (Apache License 2.0) | [`d5b6dd0b0019636ea3c88ad0f7da087a6ac194c3`](https://github.com/nitromannitol/Percolation-Rigidity/tree/d5b6dd0b0019636ea3c88ad0f7da087a6ac194c3); 59 modules cite the earlier [`63c0ac991f33e61e9645694319070d9405333e5d`](https://github.com/nitromannitol/Percolation-Rigidity/tree/63c0ac991f33e61e9645694319070d9405333e5d), at which they are the same | the 183 modules under [`Exploding/Rigidity/`](Exploding/Rigidity/) outside `Vendor/`, from the files of the same paths under `Rigidity/`: the proof of uniform slab connectivity above the critical probability (`Rigidity.Percolation.uniformCubeSlabConnectivity_of_criticalProbability_lt`) and the slab crossing estimates |
| [anthropics/formal-math](https://github.com/anthropics/formal-math/tree/795efb86f191735c5481675763537cfb4ff37e55/percolation), the `percolation/` project (Apache License 2.0; its `LICENSE` and `NOTICE` are kept verbatim in [`Exploding/Rigidity/Vendor/FormalMathPercolation/`](Exploding/Rigidity/Vendor/FormalMathPercolation/)) | `795efb86f191735c5481675763537cfb4ff37e55` | the 12 modules under `Exploding/Rigidity/Vendor/FormalMathPercolation/Literature/`, from the files of the same names under `percolation/Percolation/Literature/`, as copied in Percolation-Rigidity at `d5b6dd0b0019636ea3c88ad0f7da087a6ac194c3` |
| [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability/tree/7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069) (Apache License 2.0) | `7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069` | the bond model in which Percolation-Rigidity is stated: the nine modules under [`Exploding/Support/LatticeBond/`](Exploding/Support/LatticeBond/), from `LatticeProb/Prob/Percolation/LatticeBond*.lean` and `LatticeProb/Prob/Percolation/LatticeUniqueCluster*.lean`, and `Exploding/Support/StochasticO.lean`, from `LatticeProb/Prob/StochasticO.lean` |

The other formal-math modules that the copied code uses, and the planar site percolation modules
from Leonardo Bonanno's [lean-formalizations](https://github.com/leobon12/lean-formalizations), are
not copied here: they are imported from their copies in the pinned Lattice-Probability
(`LatticeProb.Vendor.FormalMathPercolation` and `LatticeProb.Bonanno.LQGMetric.Perc`), which carry
their own headers.

## How this was built

The Lean code was written by AI coding agents under the close supervision of the author. Anthropic
Claude models (Opus 5, Sonnet 5, Opus 5.5 and Haiku 5.5) worked through Claude Code and the Pi agent
harness. OpenAI GPT-6 Sol, GPT-6 Luna and GPT-6.1-Sol worked through the Codex CLI on the Lean
work, and GPT-6-Astra reviewed the mathematics of the pairwise form of Hypothesis 1. DeepSeek V4.1
Flash and Mistral Leanstral searched for auxiliary proofs. Every proof is checked by the Lean
kernel. The models and tools are listed in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**, who is also the author of the paper it
formalizes. If you use this formalization, please cite it using the metadata in
[`CITATION.cff`](CITATION.cff). This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4) and the library
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability).

## License

The Lean code in this repository is licensed under the **Apache License 2.0** (see
[`LICENSE`](LICENSE)); the copied modules listed in [Copied code](#copied-code) keep the terms of
their sources.  The paper source in `paper/` is included for reference and is not
covered by the Apache license.
