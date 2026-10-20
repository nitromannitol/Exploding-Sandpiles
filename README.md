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

All 22 numbered results of the corrected edition and its Remark 1 are proved in Lean, with no `sorry` and only the standard axioms, from three cited results that enter as explicit hypotheses; Theorem 6.1 is stated as published, Theorems 1.2 and 1.3 as published with the law (2) read as one common law at every site, and Theorems 1.4 and 5.1 with the corrections listed in the corrected edition; Theorem 5.1 also assumes Hypothesis 1 in a stronger form than printed, and whether it holds under the printed form is open.

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
| Theorem 1.2 | `Exploding.limit_shape` | The rescaled toppled region converges in volume to a convex domain. |
| Theorem 1.3 | `Exploding.convergence_of_time_constant` | The rescaled arrival times converge locally uniformly. |
| Theorem 1.4 | `Exploding.explosive` | A product background with one-site law `ν` explodes. |
| Theorem 5.1 | `Exploding.generalized_convergence` | Convergence under the hypotheses of Section 5. |
| Theorem 6.1 | `Exploding.counterexample` | An explosive background with no limit shape. |

**Theorem 1.2.** There is a nonempty open convex set `B ⊂ ℝᵈ` such that almost surely
`|{y : v_t([t y]) > 0} △ B| → 0` as `t → ∞`.

**Theorem 1.3.** There is a continuous, convex, positively one-homogeneous `N` such that almost
surely `η` is explosive, every arrival time `T(x) = min{t ≥ 1 : v_t(x) > 0}` is finite, and
`n⁻¹ T([n y]) → N(y)` uniformly on compact sets.

**Theorem 1.4.** Let `d ≥ 2` and let `ν` be a probability law on `ℤ` with `ν{m ≥ d} = 1` and
`ν{2d − 1} > 0`. A background whose values are independent, each of law `ν`, is explosive almost
surely.

**Theorem 5.1.** Let `d ≥ 2` and let `P` be a law on backgrounds `η_min ≤ η ≤ 2d − 1` that is
stationary and ergodic for a sublattice of finite index and satisfies Hypotheses 1 and 3 to 5 of
Section 5. Then almost surely `η` is explosive, and `n⁻¹ T([n y])` converges locally uniformly to a
deterministic, continuous, convex, one-homogeneous function.

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
| Proposition 7.1 | `Exploding.explosion_criteria` |
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
| C05 | Section 2 (Prop 2.1, Lemma 2.1, Hypotheses 2–4), Section 7 recurrence, Proposition 4.1 proof | Initial seed $s_0'=\eta+\Delta w_0$, not $\eta$ |
| C06 | Section 2, paragraph before Proposition 2.2 (proof) | Percolation bounds: Mathieu applied to the independent site process, Antal–Pisztora to the bond process |
| C07 | Lemma 2.1, initial odometer and caption | $w_0$ defined on the whole lattice; caption $s_0'=2+\Delta\mathbf 1_A$ |
| C08 | Section 3, Lemma 3.1, two paragraphs after proof, Remark 1 | Lemma for every $d\geq2$ with $C_d$; remark gives planar lower bound; $Cn^2$ false in $d=2$ |
| C09 | Section 4, Proposition 4.1 proof | Comparison of $\tilde T$ at nearby points replaces continuity; integrability via Kac |
| C10 | Section 4, Theorem 1.2 proof | Proof added: $\mathcal B(p)=\{\mathcal N_p<1\}$, level set Lebesgue-null |
| C11 | Section 5 standing assumption; Proposition 5.1; Theorem 5.1 | Assume $d\geq2$; $\eta\equiv0$ counterexample in $d=1$; Hyp 5 vacuous |
| C12 | Hypothesis 1 | Pairwise independence becomes joint independence of finite families; a strengthened hypothesis, not a correction: whether the published form suffices is open |
| C13 | Hypothesis 4, deadline | Deadline $|\mathcal B_k|$ instead of $|k|$; weaker hypothesis |
| C14 | Proof of Proposition 5.1 | Six-step proof; published use of Theorem 4.1 of Levine–Peres [LP09] for $\eta\geq\eta_{\min}$ does not transfer |
| C15 | Section 5.2 examples | Hypotheses 1 and 4 verified for the cloud and checkerboard; Theorem 4.2 sentence replaced; $\mathcal S$ nonempty |
| C16 | Proof of Theorem 6.1 | Failure of convergence in the volume sense of Theorem 1.2, for $d\geq2$ |
| C17 | Proposition 7.1, statement | "Let $d\geq2$"; $d=1$ argued after the proof |
| C18 | Proposition 7.1, proof | Proof for $d\geq2$; criterion sentence replaced; $d=1$ paragraph |
| C19 | Proof of Theorem 1.4 | Reduced law $\mathbf P_d$ via $\alpha_d$; recurrence and box-crossing for $\mathbf P_d$; explosion transfers |
| C20 | Proposition 7.2, setup | Tangential field $\beta$; $\eta^{(d-1)}=\eta^{(d)}(1,\cdot)-1$; $\Delta u_0$ term |
| C21 | Proposition 7.2, inductive step | Both constrained odometers make the same update |
| C22 | Proposition 7.3, proof | Decomposition $Q_n=(\mathbf 1+Q_{n-2})\cup\dots$; base cases $n=1,2$ |
| C23 | Proposition 7.5, statement | Box-crossing for $d\geq2$; $d=1$ for every law with $\eta\geq1$ |
| C24 | Proposition 7.5, proof | Proof for $\alpha_d$ with one-marginal layer variables; $d=1$ immediate |
| C25 | Minor wording | AI-use subsection and Lean paragraph; $n\geq1$ in counterexample; $\mathbf x_{d-1}$ in Prop 7.2; labels; ties |

## Standing assumptions and scope

1. **Cited results assumed.** Three results of the literature enter as explicit hypotheses of the
   statements that use them; none is an `axiom`:
   - Antal and Pisztora, Theorem 1.1 (chemical distance in supercritical bond percolation), `hChem`:
     Theorems 1.2, 1.3 and 5.1, Propositions 2.2, 3.1, 4.1 and 5.1, and Lemmas 3.2 and 3.5 to 3.7;
   - Fey, den Boer and Redig, Theorem 4.1, and Fey, Levine and Peres, Theorem 1.1 (radius of the
     toppled cluster): Lemma 3.1 and Remark 1 only.
2. **Cited results proved here.** Six other cited results are proved in this repository:
   Liggett, Schonmann and Stacey, Theorem 0.0 and Corollary 1.4; Mathieu, Lemma 5.2; Schonmann's
   bound (Proposition 7.4); Fey, Levine and Peres, Proposition 1.4; and Fey, Meester and Redig,
   Theorem 2.8, which no result uses. The statements in `Exploding/MainTheorems.lean` do not take
   them as hypotheses. The cited results and their precise sources are listed in
   [`ASSUMPTIONS.md`](ASSUMPTIONS.md).
3. **Departures.** Hypothesis 1 is used in the form "the values on two finite sets at distance more
   than `K` are independent", meaning that the two families generate independent σ-fields. The
   paper prints pairwise independence. Whether Propositions 5.1 and 7.1 and Theorem 5.1 hold under
   the printed form is open. Proposition 7.1 is proved for `d ≥ 2`; the case `d = 1` is argued in a
   paragraph after its proof and is not formalized.
4. **Axioms.** The library contains no `sorry`, `admit`, `native_decide` or new `axiom`. Each main
   theorem depends on exactly `propext`, `Classical.choice` and `Quot.sound`.
5. **Conventions.** Arrival times are valued in `ℕ∞`; `[x]` is the nearest lattice point, with ties
   broken by the coordinatewise minimum; locally uniform convergence is stated in its `ε`-form; the
   floor in the toppling rules is integer division on `ℤ`.
6. **Not formalized.** The proof outline of Section 1, the examples of Section 5.2, the qualitative
   claims of Remarks 3, 4 and 5, the case `d = 1` of Proposition 7.1, and the figures.

## Guarantees

All 22 numbered results of the corrected edition and its Remark 1 are proved in Lean, with no `sorry` and only the standard axioms, from three cited results that enter as explicit hypotheses; Theorem 6.1 is stated as published, Theorems 1.2 and 1.3 as published with the law (2) read as one common law at every site, and Theorems 1.4 and 5.1 with the corrections listed in the corrected edition; Theorem 5.1 also assumes Hypothesis 1 in a stronger form than printed, and whether it holds under the printed form is open.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **42 statements: 29 proved; 9 cited results; 4 definitions.**

Each statement is taken from one source file. For each source the table gives its theorem statements, how many of them are proved, the cited results stated as hypotheses, and the definitions stated separately.

| Source | SHA-256 | Theorem statements | Proved | Cited results | Definitions |
|---|---|---|---|---|---|
| [paper/corrected-arxiv/exploding-corrected-arxiv.tex](paper/corrected-arxiv/exploding-corrected-arxiv.tex) | `6e5a981a0d8d3b7abdf78e31d2630780b9db467e63aea7772e93043e4e804d0c` | 29 | 29 | 9 | 4 |

A cited result is a hypothesis of the theorems that use it, not an axiom (see ASSUMPTIONS.md). Definitions are not counted as theorems. These counts are generated from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`; `python3 tools/check_axioms.py` checks the axiom closures.

<!-- STATUS-END -->

- **No `sorry`.** The build emits no warning and contains no `sorry` in `Exploding/`. The
  comparator challenge [`ExplodingAudit/LimitShape/Challenge.lean`](ExplodingAudit/LimitShape/Challenge.lean)
  has one intentional statement-level `sorry`.
- **Standard axioms only.** [`Exploding/Meta/AxiomsAudit.lean`](Exploding/Meta/AxiomsAudit.lean)
  prints the axioms of 95 theorems, and [`scripts/check_axioms.py`](scripts/check_axioms.py)
  requires exactly `propext`, `Classical.choice` and `Quot.sound` for each theorem of its explicit
  list.
- **Comparator.** The Mathlib-only pair [`ExplodingAudit/LimitShape/`](ExplodingAudit/LimitShape/)
  restates Theorem 1.2 for `0 < p ≤ 1` over Mathlib alone, with the four cited results its
  statement takes as hypotheses. It is the only pair.
- **Statements.** The SHA-256 of each statement is recorded in
  [`ledger/manifest.yaml`](ledger/manifest.yaml). `python3 tools/verify.py` checks the hashes, the
  correspondence with the paper and the axiom closures.
- **Toolchain and dependencies.** Lean `v4.32.0`, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` and
  Lattice-Probability `78f4b2cec065fa2fb5116b06c41966855f62cf50`, as recorded in
  [`lean-toolchain`](lean-toolchain) and [`lake-manifest.json`](lake-manifest.json).

## Size

`Exploding/` and `Exploding.lean`: 420 Lean files with 75,789 lines. `ExplodingAudit/`: 4 Lean
files with 697 lines.

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

## Running the comparators

The comparator pair is [`ExplodingAudit/LimitShape/`](ExplodingAudit/LimitShape/). Its
[`comparator.json`](ExplodingAudit/LimitShape/comparator.json) permits exactly `propext`,
`Classical.choice` and `Quot.sound`, and enables the nanoda kernel. Build `leanprover/comparator`,
`lean4export` and `landrun` at the revisions listed in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), then run from the
repository root

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ExplodingAudit/LimitShape/comparator.json
```

which prints `Your solution is okay!`. The [comparator workflow](.github/workflows/comparator.yml)
runs the pair on manual dispatch, and [`ExplodingAudit/README.md`](ExplodingAudit/README.md)
describes it.

## Repository layout

```text
Exploding/
  MainTheorems.lean   the numbered results, stated in full
  Frozen/             one statement per file, each followed by its proof
  External/           the cited results, stated as propositions
  Support/            the model and the lemmas the statements are proved from
  Meta/               AxiomsAudit.lean
Exploding.lean        the root module
ExplodingAudit/       the Mathlib-only comparator pair, its solution and checks
paper/corrected-arxiv/      the corrected edition: source, bibliography, figures, source note
paper/exploding-arxiv.tex   the unmodified arXiv v2 source
paper/README.md             the three texts in paper/
ledger/manifest.yaml        the statements, with their SHA-256 and sources
ASSUMPTIONS.md              the cited results and where each is proved
CORRESPONDENCE.md           paper ↔ Lean: conventions, cited inputs, statement table
CONTRIBUTING.md             building notes and checks
CITATION.cff                citation metadata
formalization.yaml          source, statement, automation and review metadata
scripts/                    check_axioms.py, the explicit-list axiom check
tools/                      verify.py and the checkers it runs
.github/workflows/          build.yml and comparator.yml
lakefile.lean, lake-manifest.json, lean-toolchain   the build
```

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
[`LICENSE`](LICENSE)).  The paper source in `paper/` is included for reference and is not
covered by the Apache license.
