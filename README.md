# A shape theorem for exploding sandpiles

[![CI](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/comparator.yml)

A Lean 4 formalization of the paper

> Ahmed Bou-Rabee,
> [*A shape theorem for exploding sandpiles*](https://arxiv.org/abs/2102.04422),
> Annals of Applied Probability 34(1A) (2024), 714–742,
> [doi:10.1214/23-AAP1976](https://doi.org/10.1214/23-AAP1976).

The paper studies a sandpile in which almost every site starts with just too few chips to topple.
Adding enough chips at one site makes the toppling spread forever. The paper shows that the region
reached by this explosion has a limit shape.

Every numbered result of the paper, and its Remark 1, is proved in Lean. No gaps remain, and no result
of another work is assumed. The statements follow a corrected edition of the paper. They use one
hypothesis, finite range of dependence, in a stronger form than printed (see
[What is assumed](#what-is-assumed)).

## The paper

A *background* `η : ℤᵈ → ℤ` puts a number of chips on each site of the lattice. Add `n` chips at
the origin and topple in parallel: at each step, every site with at least `2d` chips sends one chip
to each of its `2d` neighbours. The *odometer* `v_t(x)` counts the topplings at `x` up to time `t`.
The background is *explosive* if, for some `n`, this process never stops. Let `M_η` be the least
such `n`, and call `η + M_η δ₀` the *exploding sandpile*. Its *arrival time* at `x` is
`T(x) = min{t ≥ 1 : v_t(x) > 0}`.

The main example is a random background with independent values: `2d − 1` with probability `p` and
`2d − 2` otherwise, with `d ≥ 2` and `0 < p ≤ 1`. Fey, Levine and Peres showed that it is explosive
almost surely (Theorem 1.1 of the paper). The paper shows that the explosion has a limit shape.
Write `[x]` for the lattice point nearest to `x ∈ ℝᵈ`.

**Theorem 1.2.** There is a nonempty open convex set `B ⊂ ℝᵈ` such that, almost surely, the volume
of `{y : v_t([t y]) > 0} △ B` tends to `0` as `t → ∞`.

**Theorem 1.3.** There is a continuous, convex, positively one-homogeneous function `N` on `ℝᵈ`
such that, almost surely, every arrival time is finite and `n⁻¹ T([n y]) → N(y)` uniformly on
compact sets.

**Theorem 1.4.** Let `d ≥ 2`, and let `ν` be a probability law on `ℤ` with `ν{m ≥ d} = 1` and
`ν{2d − 1} > 0`. A background whose values are independent, each of law `ν`, is explosive almost
surely.

**Theorem 5.1.** Let `d ≥ 2`, and let `P` be a law on backgrounds with `η_min ≤ η ≤ 2d − 1` that
is stationary and ergodic for a sublattice of finite index. Suppose `P` satisfies Hypotheses 1 and
3 to 5 of Section 5. Then almost surely `η` is explosive, and `n⁻¹ T([n y])` converges locally
uniformly to a deterministic, continuous, convex, one-homogeneous function.

The hypotheses say the following.

- Hypothesis 1 (finite range of dependence): the values of `η` on two finite sets that are far
  enough apart are independent.
- Hypothesis 3 (path-filling): toppling along a long path of sites soon fills its bounding
  rectangle.
- Hypothesis 4 (strongly box-crossing): with probability close to one, a large box, wherever it is
  placed, is crossed by topplings in a strong sense defined in Section 5.
- Hypothesis 5 (wave-approximation): the arrival times of the exploding sandpile differ by `o(n)`
  on `[−n, n]ᵈ` from those of the last wave, an auxiliary process of Section 3.

**Theorem 6.1.** For every `d ≥ 2` there is an explosive background, not bounded below by `2d − 2`,
whose arrival times along `e₁` are finite with `limsup T(n e₁)/n ≥ 3/2` and `liminf T(n e₁)/n = 1`.
No measurable set is a limit in volume of its rescaled toppled regions.

## The main theorems in Lean

| Paper | Lean declaration | File |
| --- | --- | --- |
| Theorem 1.2 | `Exploding.limit_shape_unconditional` | [`LimitShapeUnconditional.lean`](Exploding/Support/LimitShapeUnconditional.lean) |
| Theorem 1.3 | `Exploding.convergence_of_time_constant_unconditional` | [`TimeConstantUnconditional.lean`](Exploding/Support/TimeConstantUnconditional.lean) |
| Theorem 1.4 | `Exploding.explosive` | [`MainTheorems.lean`](Exploding/MainTheorems.lean) |
| Theorem 5.1 | `Exploding.generalized_convergence_unconditional` | [`GeneralizedConvergenceUnconditional.lean`](Exploding/Support/GeneralizedConvergenceUnconditional.lean) |
| Theorem 6.1 | `Exploding.counterexample` | [`MainTheorems.lean`](Exploding/MainTheorems.lean) |

Their only hypotheses are the setting of the paper. `import Exploding` loads all of them.

How to read the statements:

- The law of the random background is `Exploding.toyLaw d p`. The exploding sandpile is
  `Exploding.explodingPile η`, its odometer is `Exploding.podo`, and `Exploding.nearestSite` is
  `[x]`, with ties broken by the coordinatewise minimum.
- Arrival times, `Exploding.arrival`, are valued in `ℕ∞`. Locally uniform convergence is stated in
  its `ε`-form.
- In Theorem 5.1, the background takes values in `[η_min, 2d − 1]` (`Exploding.InOmega`). The
  hypotheses are `Exploding.FiniteRangeOfDependence` (Hypothesis 1), `Exploding.PathFillingHyp`
  (Hypothesis 3), `Exploding.StronglyBoxCrossingHyp` (Hypothesis 4) and
  `Exploding.WaveApproximationHyp` (Hypothesis 5).

## All numbered results

The paper has 24 numbered results and Remark 1. Two are quoted from other works: Theorem 1.1, of Fey,
Levine and Peres, and Proposition 7.4, of Schonmann. Both are proved here. Each row gives the
declaration that proves the result.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 | `Exploding.fey_levine_peres_explosive` | The random background is explosive almost surely. |
| Theorem 1.2 | `Exploding.limit_shape_unconditional` | The rescaled toppled region converges in volume to a convex domain. |
| Theorem 1.3 | `Exploding.convergence_of_time_constant_unconditional` | The rescaled arrival times converge locally uniformly. |
| Theorem 1.4 | `Exploding.explosive` | A product background with one-site law `ν` explodes. |
| Proposition 2.1 | `Exploding.crossing_time` | With probability at least `1 − δ`, toppling confined to a cube of side `k` fills it by time `kᵈ`, from every seed. |
| Proposition 2.2 | `Exploding.renormalization_properties_unconditional` | The good cubes have a unique infinite component, with small holes and chemical distances comparable to Manhattan distances. |
| Lemma 2.1 | `Exploding.local_convexity` | On `2d − 2 ≤ η ≤ 2d − 1`, a finite path of topplings fills its bounding rectangle. |
| Lemma 3.1 | `Exploding.square_lower_bound_unconditional` | The `m`-wave covers `[−n, n]ᵈ` once `m ≥ C nᵈ` (`m ≥ C n² log(n + 1)` when `d = 2`). |
| Remark 1 | `Exploding.sharp_planar_obstruction_unconditional` | The logarithm of Lemma 3.1 cannot be removed in dimension two. |
| Lemma 3.2 | `Exploding.finite_exploding_unconditional` | Almost surely the last wave is well defined. |
| Lemma 3.3 | `Exploding.last_wave_bound` | The last wave is at most one more than the penultimate wave, and at most one outside the penultimate cluster. |
| Lemma 3.4 | `Exploding.approx_subadditivity` | The arrival times of the penultimate clusters are subadditive. |
| Lemma 3.5 | `Exploding.last_penultimate_cluster_unconditional` | The penultimate clusters are polylogarithmically small. |
| Lemma 3.6 | `Exploding.penultimate_upper_bound_unconditional` | The last-wave arrival times are at most linear, up to a power of the logarithm. |
| Lemma 3.7 | `Exploding.last_penultimate_close_unconditional` | The last-wave and penultimate-cluster arrival times are polylogarithmically close. |
| Proposition 3.1 | `Exploding.convergence_of_the_last_wave_unconditional` | The rescaled last-wave arrival times converge locally uniformly to a continuous, convex, one-homogeneous function. |
| Proposition 4.1 | `Exploding.approximate_subadditive_unconditional` | The arrival times and the last-wave arrival times differ by at most a constant. |
| Proposition 5.1 | `Exploding.convergence_of_the_generalized_last_wave_unconditional` | Convergence of the last-wave arrival times under Hypotheses 1, 3 and 4. |
| Theorem 5.1 | `Exploding.generalized_convergence_unconditional` | Convergence of the exploding sandpile under the hypotheses of Section 5. |
| Theorem 6.1 | `Exploding.counterexample` | An explosive background with no limit shape. |
| Proposition 7.1 | `Exploding.explosion_criteria_of_one_le` | A recurrent law satisfying Hypotheses 1 and 2 is explosive, in every dimension `d ≥ 1`. The paper argues `d = 1` only in a remark after the proof. |
| Proposition 7.2 | `Exploding.dimensional_reduction` | The constrained odometer on a face of the cube in `ℤ^{d+1}` equals the one in `ℤᵈ`. |
| Proposition 7.3 | `Exploding.recurrence` | The constant background `d` on `ℤᵈ` is recurrent. |
| Proposition 7.4 | `Exploding.schonmann_bootstrap` | Schonmann's bound: the cube `Q_n` is internally spanned with probability at least `1 − c e^{−Cn}`. |
| Proposition 7.5 | `Exploding.box_crossing` | Product backgrounds as in Theorem 1.4 are box-crossing for `d ≥ 2`; in dimension one, every law with `η ≥ 1` is. |

## What is assumed

No result of another work is assumed. The nine results that the paper cites are proved in this
repository or in Lattice-Probability. [`ASSUMPTIONS.md`](ASSUMPTIONS.md) gives each with its source
and its proof.

One hypothesis of the paper is used in a stronger form than printed.

- **Hypothesis 1 (finite range of dependence).** The published paper asks that `η(x)` and `η(y)` be
  independent when `|x − y| > K`. The corrected edition and the Lean statements ask that the
  families of values on two finite sets at distance more than `K` be independent. Theorem 5.1 and
  Propositions 5.1 and 7.1 assume this form, `Exploding.FiniteRangeOfDependence`. Whether they hold
  under the printed form is open (correction C12).

## Corrections

The Lean statements follow a corrected edition of the arXiv v2 source,
[`paper/corrected-arxiv/exploding-corrected-arxiv.tex`](paper/corrected-arxiv/exploding-corrected-arxiv.tex),
with its [PDF](paper/corrected-arxiv/exploding-corrected-arxiv.pdf). It makes 26 changes, C01 to
C26, listed with the published text, the corrected text and the reason in its final section,
"Corrections to the published version". The unmodified arXiv v2 source is
[`paper/exploding-arxiv.tex`](paper/exploding-arxiv.tex).

- **The random law (equation (2) of the paper).** As printed, it fixes only the law at the origin. It is read as one common law at
  every site (C01, C02). The convex domain of Theorem 1.2 is a nonempty open convex set, which its
  proof provides (C02). Theorems 1.2 and 1.3 are otherwise as published.
- **Theorem 1.4.** As printed, it is false for product laws whose marginals differ between sites.
  The corrected statement takes one common law `ν` at every site and `d ≥ 2` (C03).
- **Other statements.** Lemma 3.1 holds with an extra `log(n + 1)` in dimension two, and Remark 1
  shows that it is needed (C08). Section 5 assumes `d ≥ 2`, since Proposition 5.1 and Theorem 5.1
  fail in dimension one (C11). Hypothesis 1 is strengthened (C12) and Hypothesis 4 weakened (C13).
  Propositions 7.1 and 7.5 are stated for `d ≥ 2`, with their one-dimensional cases stated apart
  (C17, C23). Both one-dimensional cases are proved.
- **Definitions and proofs.** Four changes correct definitions of Sections 2 and 7 (C04, C05, C07,
  C20). Ten change proofs only; C10 adds the proof of Theorem 1.2.
- **Other.** C15 verifies the examples of Section 5.2, C25 adds a statement on the use of
  artificial intelligence, and C26 corrects wording.

## Scope

- **Statement forms.** Arrival times are valued in `ℕ∞`. `[x]` is the nearest lattice point, with
  ties broken by the coordinatewise minimum. The floor in the toppling rules is integer division on
  `ℤ`. [`CORRESPONDENCE.md`](CORRESPONDENCE.md) lists every reading of a statement that is not
  literal.
- **The Antal–Pisztora bound.** The paper applies it to bond percolation of density close to one.
  The unconditional forms use the proved high-density case, `Exploding.xap12_high_density_bound`.
  The full supercritical bound is also proved, as
  `Exploding.External.antalPisztoraChemicalDistance_holds`, by a renormalization that departs from
  the cited proof (see [`CORRESPONDENCE.md`](CORRESPONDENCE.md)).
- <a id="assumed-literature-inputs"></a>**First forms of the results.** [`Exploding/MainTheorems.lean`](Exploding/MainTheorems.lean) also
  holds earlier forms of several results that take a result of another work as a hypothesis. Eleven
  take the chemical distance bound of Antal and Pisztora, and Lemma 3.1 and Remark 1 take two radius
  bounds. All three are proved here, and no declaration in the tables above takes them.
  [`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps the paper to the Lean names.
- **Not formalized.** The proof outline of Section 1, the examples of Section 5.2, the qualitative
  claims of Remarks 3, 4 and 5, and the figures.

## Checking the proofs

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **42 statements: 29 proved; 9 results of other works that the paper cites; 4 definitions.**

Each statement is taken from one source file. The table gives, for each source, its theorem statements, how many of them are proved, the cited results of other works, and the definitions that are stated separately. [`ASSUMPTIONS.md`](ASSUMPTIONS.md) gives the source and the proof of each cited result.

| Source | SHA-256 | Theorem statements | Proved | Cited results | Definitions |
|---|---|---|---|---|---|
| [paper/corrected-arxiv/exploding-corrected-arxiv.tex](paper/corrected-arxiv/exploding-corrected-arxiv.tex) | `ee4b05b340bff74811db1c3ed88ac7b0ad3fd324f0dad5a52393bc4971c0c8b0` | 29 | 29 | 9 | 4 |

Definitions are not counted as theorems. The counts are generated from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`; `python3 tools/check_axioms.py` checks the axioms used.

<!-- STATUS-END -->

- **No `sorry`.** This is Lean's marker for an unproved step. The library `Exploding/` has none, and the build emits no warning. Each comparator
  challenge `ExplodingAudit/*/Challenge.lean` has one intentional `sorry`, which the matching
  solution proves.
- **Standard axioms only.** [`Exploding/Meta/AxiomsAudit.lean`](Exploding/Meta/AxiomsAudit.lean)
  prints the axioms of 128 declarations, among them every declaration in the tables above.
  [`scripts/check_axioms.py`](scripts/check_axioms.py) requires exactly `propext`,
  `Classical.choice` and `Quot.sound` for each theorem of its explicit list.
- **Independent check of the statements.** The comparator tool checks that a short restatement over
  mathlib alone is proved by the library, using both the Lean kernel and the independent nanoda
  kernel. Four such pairs in [`ExplodingAudit/`](ExplodingAudit/) restate main results. Three state
  Theorems 1.2, 1.3 and 5.1 with no cited result as a hypothesis. The fourth,
  [`ExplodingAudit/LimitShape/`](ExplodingAudit/LimitShape/), states Theorem 1.2 with four cited
  results as hypotheses; the library proves all four.
- **Fixed statements.** The SHA-256 of each statement and of the corrected edition is recorded in
  [`ledger/manifest.yaml`](ledger/manifest.yaml). `python3 tools/verify.py` checks the hashes, the
  correspondence with the paper and the axioms.
- **Continuous integration.** The **CI** workflow builds the library with no warnings, runs the
  axiom audit and `tools/verify.py`, and builds the comparator pairs. The **Comparator audit**
  workflow runs the four pairs after each successful CI run on `main`, on the commit that CI built.

The library has 686 Lean files with 109,610 lines (`Exploding.lean` and `Exploding/`), built on
mathlib and Lattice-Probability.

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
It is a public repository, used at a fixed commit recorded in [`lake-manifest.json`](lake-manifest.json):

- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `7f773dd0aa66dbe1ed1080ae0248906b9cfe5215`.

The toolchain is Lean `v4.35.0-rc2`, with mathlib at `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

### Running the comparators

The comparator pairs are the four directories of [`ExplodingAudit/`](ExplodingAudit/), listed in
[`ExplodingAudit/README.md`](ExplodingAudit/README.md). Each `comparator.json` permits exactly
`propext`, `Classical.choice` and `Quot.sound`, and enables the nanoda kernel. Build
`leanprover/comparator`, `lean4export`, `nanoda` and `landrun` at the revisions listed in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), then run from the
repository root

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ExplodingAudit/<Pair>/comparator.json
```

which prints `Your solution is okay!` for each pair.

## Repository layout

```text
Exploding.lean              the root module
Exploding/
  MainTheorems.lean         the main results, including the first forms
  Frozen/                   the statements of the corrected edition, one per file, each with its proof
  External/                 the cited results, stated as propositions, and their proofs
  Support/                  the model, the lemmas, and the unconditional forms
  Rigidity/                 slab connectivity and slab crossing estimates copied from
                            Percolation-Rigidity (see Copied code)
  Meta/                     AxiomsAudit.lean
ExplodingAudit/             the comparator pairs
paper/corrected-arxiv/      the corrected edition: source, PDF, bibliography, figures
paper/exploding-arxiv.tex   the unmodified arXiv v2 source
ledger/manifest.yaml        the list of statements, with their SHA-256 and sources
ASSUMPTIONS.md              the cited results and where each is proved
CORRESPONDENCE.md           paper ↔ Lean: conventions, cited results, statement table
scripts/, tools/            the axiom check, verify.py and the checkers it runs
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
not copied here: they are imported from their copies in the Lattice-Probability version used here
(`LatticeProb.Vendor.FormalMathPercolation` and `LatticeProb.Bonanno.LQGMetric.Perc`), which carry
their own headers.

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude), OpenAI (GPT),
DeepSeek and Mistral, under the direction of Ahmed Bou-Rabee. Every proof is checked by the Lean
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
