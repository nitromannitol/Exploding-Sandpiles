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

All 22 numbered results of the corrected edition and its Remark 1 are proved in Lean, with no `sorry` and only the standard axioms, from three cited results that enter as explicit hypotheses; Theorem 6.1 is stated as published, Theorems 1.2 and 1.3 as published with the law (2) read as one common law at every site, and Theorems 1.4 and 5.1 with the corrections listed in the corrected edition.

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

The other numbered results are proved in the same file, as are Remark 1 and the two results the
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

The table lists the 20 changes from arXiv v2, in the order of the corrected edition. Each gives the
published text, the corrected text and the reason. "Where" names the result concerned; "proof only"
marks a change that leaves the statement unchanged.

| Change | Where | Published | Corrected | Reason |
| --- | --- | --- | --- | --- |
| C01 | Law (2), Section 1 | $\mathbf P(\eta(0)=2d-2)=1-p$, $\mathbf P(\eta(0)=2d-1)=p$ at the origin only | $\mathbf P=\bigotimes_{x}\nu_p$, $\nu_p=(1-p)\delta_{2d-2}+p\delta_{2d-1}$, $0<p\le1$ | The published law does not fix the marginal away from the origin; with $2d-2$ elsewhere the background is robust. |
| C02 | Theorems 1.2 and 1.3 | Law (2) fixes the origin marginal only; "convex domain" unspecified | Law read as C01; a convex domain is a nonempty open convex set | The statements need the common marginal, and the term needs a definition. |
| C03 | Theorem 1.4 | Product measure $\mathbf P$, $\beta\ge d$, $\mathbf P(\beta(0)=2d-1)>0$ | $d\ge2$, $\nu(\{m\ge d\})=1$, $\nu(\{2d-1\})>0$, $\mathbf P=\bigotimes_x\nu$ | The published statement fails for product laws whose marginals differ between sites. |
| C04 | Frozen parallel toppling recursion | $w_{t+1}(x)=\lfloor\cdot\rfloor$ for $x\notin\mathcal S$; $s'_{t+1}=s_0+\Delta(w_{t+1}-w_0)$ | $w_{t+1}(x)=\max\{w_t(x),\lfloor\cdot\rfloor\}$; $s'_{t+1}=s_0+\Delta w_{t+1}$ | The odometer never decreases; the identity for $s'$ holds only when $\Delta w_0=0$. |
| C05 | Proposition 2.1, Lemma 2.1, Hypotheses 2 to 4, recurrence criterion, proof of Proposition 4.1 | Delivered seed $s'_0=\eta$ | $s'_0=\eta+\Delta w_0$; "quickly exceeds 1" becomes "is at least 1" in Hypothesis 3 | The published seed contradicts the frozen process; with $s'_0=\eta$ nothing topples on an L-shaped path on $\eta\equiv2d-2$. |
| C06 | Proof of Proposition 2.2 (paragraph before it, proof only) | Good cubes dominate a site percolation process; large deviations for supercritical percolation | Good edges dominate bond percolation $\zeta$ (Liggett, Schonmann and Stacey, Corollary 1.4); Mathieu's Lemma 5.2 bounds holes; Antal and Pisztora bounds chemical distances | The chemical distance bound concerns bond percolation; good cubes form a site process. |
| C07 | Lemma 2.1, initial odometer and its figure caption | $w_0\vert_A=1$; caption $s'_0=2$ | $w_0=\mathbf 1_A$ on the whole lattice; caption $s'_0=2+\Delta\mathbf 1_A$ | The frozen process takes its initial odometer on the whole lattice. |
| C08 | Lemma 3.1, statement, proof and remarks | Constant $C$ with the $(Cn^d)$-wave containing $[-n,n]^d$; proof from Fey, den Boer and Redig | For $d\ge2$, $m\ge\lceil C_2n^2\log(n+1)\rceil$ when $d=2$, or $m\ge\lceil C_dn^d\rceil$ when $d\ge3$; sharp planar rate in Remark 1 | The bound $Cn^2$ is false in dimension two (Remark 1). |
| C09 | Proof of Proposition 3.1 (proof only) | Convergence in integer directions by the subadditive ergodic theorem; everywhere by continuity | Two bounds on $\tilde T$ on an event of probability one; ergodic theorem on the induced transformation; comparison bound in place of continuity | Integrability of $\tilde T(0,y)$ is not shown, and continuity is not available. |
| C10 | Proof of Theorem 1.2 | No derivation | Proof via $\mathcal B(p)=\{\mathcal N_p<1\}$; the level set $\{\mathcal N_p=1\}$ has Lebesgue measure zero | Theorem 1.2 is asserted without proof. |
| C11 | Standing assumption of Section 5; Proposition 5.1; Theorem 5.1 | No dimension assumed | "In this section assume $d\ge2$." | Both statements are false in dimension one: take $\eta\equiv0$ on $\mathbb Z$. |
| C12 | Hypothesis 1, statement | $\eta(x)$ and $\eta(y)$ independent if $\lvert x-y\rvert>K$ | For finite $F,G$ with $\lvert x-y\rvert>K$ on $F\times G$, the values on $F$ and the values on $G$ are independent | The domination step needs joint independence; pairwise independence does not give it. |
| C13 | Hypothesis 4, deadline | $w_{\lvert k\rvert}\ge\mathbf 1\{x\in\mathcal B_k\}$ | $w_{\lvert\mathcal B_k\rvert}\ge\mathbf 1\{x\in\mathcal B_k\}$ | Since $\eta\le2d-1$, crossing by that time is the same as eventual crossing. |
| C14 | Proof of Proposition 5.1 (proof only) | Domination by independent Bernoulli variables; explosion asserted | Proof written out in full, deriving nonnegativity, recurrence and explosion of $\eta$ | The domination needs the joint independence of C12; the sketch does not derive explosion. |
| C15 | Proof of Theorem 6.1, failure of convergence | Failure shown by comparison with the two-dimensional counterexample | $\lvert(A_t\triangle(A_t-e_2/t))\cap\Omega_d\rvert\ge c_d$ for large $t$, with $A_t=\{y:\bar v_t(y)>0\}$ | The sense of failure must be the one Theorem 1.2 asserts. |
| C16 | Proposition 7.1, dimension | No restriction on $d$ | $d\ge2$ | The case $d=1$ is not covered by the machine-checked statement. |
| C17 | Proof of Proposition 7.1 (proof only) | "The arguments in the generalization section imply the criterion"; no proof | A proof for $d\ge2$, and a separate paragraph for $d=1$ | The criterion needs a proof of its own. |
| C18 | Setup of Proposition 7.2, initial data and tangential values | $s_0^{(d-1)}(\mathbf x_{d-1})=\eta^{(d)}(\mathbf x_{d-1})-1$; tangential values unspecified | $\eta^{(d-1)}(\mathbf x)=\eta^{(d)}(1,\mathbf x)-1$; $s_0^{(d-1)}=\eta^{(d-1)}+\Delta u_0^{(d-1)}$; boundary values in $\{0,1\}$ | The published argument of $\eta^{(d)}$ is a typo; the initial topplings need $\Delta u_0$. |
| C19 | Proof of Proposition 7.3 (proof only) | $Q_n^{(d)}=Q_{n-2}^{(d)}\cup\bigcup_i\mathcal F_i(Q_n^{(d)})$ | $Q_n^{(d)}=(\mathbf 1+Q_{n-2}^{(d)})\cup\bigcup_{i=1}^{2d}\mathcal F_i(Q_n^{(d)})$, with base cases $n=1,2$ | $Q_{n-2}^{(d)}$ is the corner cube, not the inner cube. |
| C20 | Proposition 7.5, box-crossing of $\mathbf P$ | "In all dimensions, $\mathbf P$ is box-crossing" | For $d\ge2$, $\mathbf P$ is box-crossing; in dimension one, every law supported on $\eta\ge1$ is | The statement fails for product laws whose marginals differ, as in C03. |

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
   claims of Remarks 4, 5 and 6, the case `d = 1` of Proposition 7.1, and the figures.

## Guarantees

All 22 numbered results of the corrected edition and its Remark 1 are proved in Lean, with no `sorry` and only the standard axioms, from three cited results that enter as explicit hypotheses; Theorem 6.1 is stated as published, Theorems 1.2 and 1.3 as published with the law (2) read as one common law at every site, and Theorems 1.4 and 5.1 with the corrections listed in the corrected edition.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **42 statements: 29 proved; 9 cited results; 4 definitions.**

Each statement is taken from one source file. For each source the table gives its theorem statements, how many of them are proved, the cited results stated as hypotheses, and the definitions stated separately.

| Source | SHA-256 | Theorem statements | Proved | Cited results | Definitions |
|---|---|---|---|---|---|
| [paper/corrected-arxiv/exploding-corrected-arxiv.tex](paper/corrected-arxiv/exploding-corrected-arxiv.tex) | `0cefbf3bfc7cc08597d59d36a3473cdf94ee816076f688c978510bb7edc6e019` | 23 | 23 | 2 | 4 |
| [paper/exploding.tex](paper/exploding.tex) | `1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44` | 6 | 6 | 7 | 0 |

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

`Exploding/` and `Exploding.lean`: 420 Lean files with 75,785 lines. `ExplodingAudit/`: 4 Lean
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
paper/exploding.tex         an earlier journal-format revision, superseded by the corrected edition
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
