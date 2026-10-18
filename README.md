# Exploding-Sandpiles

A **Lean 4** formalization of the paper

> Ahmed Bou-Rabee,
> [*A shape theorem for exploding sandpiles*](https://arxiv.org/abs/2102.04422),
> Annals of Applied Probability 34(1A) (2024), 714-742; arXiv:2102.04422.

The manifest selects three exact sources: 30 rows against the corrected journal text `paper/exploding.tex`; the Lemma 3.5, 3.6 and 3.7 successors against the official arXiv extraction `paper/exploding-arxiv.tex`; and six rows against the local corrected arXiv-format v10 draft `paper/corrected-arxiv/exploding-corrected-arxiv.tex`. Structural theorem coverage under those separate pins is respectively 19/24, 3/24 and 2/24; these fractions cannot be added into a whole-paper certificate. The corrected crossing declaration requires terminal value one and a positive volume deadline for every permitted seed, over `0 < p ≤ 1`. Lemmas 3.5, 3.6 and 3.7 include `p = 1` under the official arXiv pin. The four literal definitions add no theorem coverage. Cited literature remains explicit in theorem types. The development is built on mathlib and Lattice-Probability (LatticeProb).

A separate corrected arXiv-format draft is available with a source note and compilation instructions at paper/corrected-arxiv/SOURCE_NOTE.md.

[![CI](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/Exploding-Sandpiles/actions/workflows/comparator.yml)

## Results and source coverage

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

The registry has 39 rows: 30 journal-source rows (17 paper theorems, six cited-input companions and seven cited-input definitions), three official-arXiv paper theorems, and six corrected-v10 rows (two paper theorems and four literal definitions). The aggregate remains 28 theorem rows and 11 definition rows. Structural coverage by exact pin is journal 19/24 (17/22 paper-owned), official arXiv 3/24 (3/22), and corrected-v10 2/24 (2/22). Three exact `coverage_allowed_gaps` entries record the uncovered sets. The manifest has 28 PROVED rows, 11 FROZEN definitions and zero SEALED rows; each theorem row is bound to its own exact source and validation record. The dated [counterexample receipt](ledger/audits/2026-10-15-counterexample-v4-promotion.md) and [crossing receipt](ledger/audits/2026-10-15-crossing-v4-promotion.md) distinguish their evidence. Theorem 1.1 and Proposition 7.4 are among the seven preserved cited inputs.

[`Exploding/MainTheorems.lean`](Exploding/MainTheorems.lean) gives the public statements.
The following Theorems 1.2, 1.3, 1.4 and 5.1 summarize existing old-source rows only.
The Bernoulli Theorems 1.2 and 1.3 retain their strict 0 < p < 1 contracts;
Theorems 1.4 and 5.1 retain their own stated model hypotheses. None certifies a
corrected-v10 endpoint. The proved v4 Theorem 6.1 statement is tied to the corrected-v10 override:

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
- **Theorem 6.1, no limit shape** (`theorem:counterexample`,
  `Exploding.Frozen.counterexample`): for `d ≥ 2` there is one explosive background `η` not
  bounded below by `2d - 2`, with finite arrivals along `n e₁`, `limsup n⁻¹ T(n) ≥ 3/2`,
  and `liminf n⁻¹ T(n) = 1`. For that same `η` and `hη`, no measurable set `B` is a limit
  of the rescaled support in symmetric-difference volume. The full conclusion is proved
  without a cited-result hypothesis.

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

**What is assumed.** The seven historical cited results are stated in Lean as propositions in
`Exploding/External/`; an old-source theorem carries one where it appears in that statement, so
the type shows its cited premises. The two corrected-v10 theorem types have no cited-result binder. No
`axiom` is declared. [`ASSUMPTIONS.md`](ASSUMPTIONS.md) lists all seven registered historical
inputs with their verbatim Lean statements. The old-source frozen statements carry them as
follows, where `perc` stands for the three percolation
results `hLSSB` (Corollary 1.4 of Liggett, Schonmann and Stacey), `hHole` (Lemma 5.2 of
Mathieu) and `hChem` (Theorem 1.1 of Antal and Pisztora):

| statement | cited hypotheses carried |
|---|---|
| Theorem 1.2 | `perc`, `hSch` (Schonmann's bound, Proposition 7.4) |
| Theorem 1.3 | `perc`, `hFLP` (Theorem 1.1, Fey, Levine and Peres) |
| Theorem 1.4, Proposition 7.5 | `hSch` |
| Proposition 2.2, Lemmas 3.2, 3.5, 3.6 and 3.7, Propositions 3.1 and 4.1 | `perc` |
| Proposition 5.1, Theorem 5.1 | `perc`, `hLSS` (Theorem 0.0 of Liggett, Schonmann and Stacey) |
| Theorem 6.1 and Proposition 2.1, corrected-v10 | none; both exact types have no cited-result binder |
| Propositions 7.1, 7.2 and 7.3, Lemmas 2.1, 3.1, 3.3 and 3.4 | none |

Propositions 5.1 and 7.1 and Theorem 5.1 also carry the model hypotheses of Sections 5 and 7
(finite range of dependence, path-filling, box-crossing, recurrence, wave approximation);
these are assumptions on the law of the background, not cited results.

Six of the seven cited results are proved in this repository, so the hypothesis can be
discharged by the proof named:

- The historical FMR registration still has the separate proof `Exploding.xfmr_proved`
  (`Exploding/Support/ExtFMR.lean`); FMR is not a premise of proved v4 Theorem 6.1.
- `hLSSB` by `Exploding.xlse_lss_bounded_degree` and `hLSS` by `Exploding.xlse_lss_general`
  (`Exploding/Support/ExtLSSCountable.lean`);
- `hHole` by `Exploding.xmf_proved` (`Exploding/Support/ExtMHHoleVolume.lean`);
- `hSch` by `Exploding.xsr_schonmann` (`Exploding/Support/ExtSchFinal.lean`);
- `hFLP` by `Exploding.xsr_flp` (`Exploding/Support/ExtSchFLP.lean`), which applies
  `Exploding.LSProof.ls_flp_from_explosive` (`Exploding/Support/LSProofAux.lean`) to
  `Exploding.xsr_schonmann`; that derivation is available because Theorem 1.4 strengthens
  Theorem 1.1, and the proof of Theorem 1.2 already uses it.

Only `hChem` (`Exploding.External.AntalPisztoraChemicalDistance`) is assumed outright. The
frozen statements carry cited results only where they appear as hypotheses. The proved
Theorem 6.1 statement has no cited-result binder. Theorem 1.4 and Proposition 7.5 (`hSch := Exploding.xsr_schonmann`)
hold with no cited hypothesis; Theorems 1.2 and 1.3 rest on `hChem` alone; and Proposition
2.2, Lemmas 3.2, 3.5, 3.6 and 3.7, Propositions 3.1, 4.1 and 5.1 and Theorem 5.1 rest on
`hChem` alone, the last two together with the model hypotheses above. The paper-to-Lean map
of the cited results is
in [`CORRESPONDENCE.md`](CORRESPONDENCE.md).

Not formalized: the proof outline of Section 1, the examples of Section 5.2 and the figures.
Other corrected-v10 statements have no corrected-source certification; Lemma 3.2 version 7 is PROVED for 0 < p ≤ 1 under the historical source pin, and Lemmas 3.5, 3.6 and 3.7 version 5 include p = 1 under the official arXiv pin; five remaining strict Bernoulli paper rows still exclude p = 1.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **39 registered declarations: 28 `PROVED`; 7 `FROZEN` cited inputs; 4 `FROZEN` non-External definitions.**

Source coverage is partial. Each row describes only its selected source; historical-source rows provide no revised-source coverage. These counts do not establish that every statement of any paper revision is proved.

| Pinned source | SHA-256 | Theorem rows | Proved theorem rows | Cited inputs | Non-External definitions |
|---|---|---|---|---|---|
| [paper/corrected-arxiv/exploding-corrected-arxiv.tex](paper/corrected-arxiv/exploding-corrected-arxiv.tex) | `59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2` | 2 | 2 | 0 | 4 |
| [paper/exploding-arxiv.tex](paper/exploding-arxiv.tex) | `f12deba6e481a3d81c6967bc48ecbbdae1df4fa1c5f6248a38990030b308072d` | 3 | 3 | 0 | 0 |
| [paper/exploding.tex](paper/exploding.tex) | `1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44` | 23 | 23 | 7 | 0 |

Non-External definitions are not counted as cited inputs or theorem proofs. Their literal-body/source audit is required; directory placement does not establish source fidelity. Theorem states and source pins come from `ledger/manifest.yaml`; independent source and axiom audits remain necessary. Run `python3 tools/check_axioms.py` to check axiom closures.

<!-- STATUS-END -->

### Scope and faithfulness

The global source default remains `paper/exploding.tex`, SHA-256 `1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44`. Lemmas 3.5, 3.6 and 3.7 version 5 select the official arXiv extraction `paper/exploding-arxiv.tex`, SHA-256 `f12deba6e481a3d81c6967bc48ecbbdae1df4fa1c5f6248a38990030b308072d`, with its byte-identical `defs.tex` input. The counterexample and crossing successors and four literal definitions select the separate corrected-v10 draft, SHA-256 `59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2`. The official arXiv and abstract are preserved; these three rows do not certify the rest of that source or its literal initialization.

The partition is 30 journal rows, three official-ArXiv rows and six corrected-v10 rows. The journal group has 23 theorem rows (17 paper-owned and six cited-input companions) and seven cited-input definitions. The official group has three paper theorems; the corrected group has two paper theorems and four literal definitions. Aggregate counts remain 28 theorem rows and 11 definition rows. Journal coverage is 19/24 theorem-like statements and 17/22 paper-owned statements; its gaps are crossing at line 416, Lemmas 3.5–3.7 at lines 792, 807 and 832, and the counterexample at line 1351. Official-arXiv coverage is 3/24 and 3/22 paper-owned, claiming Lemmas 3.5–3.7 at lines 652, 667 and 692; its other 21 statements are explicit allowed gaps. Corrected-v10 coverage is 2/24 and 2/22 paper-owned, claiming crossing at line 286 and the counterexample at line 1875; its other 22 statements remain explicit allowed gaps. Definitions add no theorem coverage. These are structural row claims, not whole-paper fidelity certificates.

The old thm-counterexample@3 handwritten audit remains bound to exploding.tex:1351-1361, marker SHA-256 c9c8b8778d204a8280a899f7dda2fefda47e85854c1169bb477828b81f191dd3, semantic-closure SHA-256 ff157998636d1fa5296aa50733454d0a0538d591c0824fd6e6fcab3f9e9b4b9e, and whole-file SHA-256 d9e7f60ec00c1dbdc63a690bba7524dd1fd0f31b30b0ccaa03de3c15bd0dc195. The proved v4 successor has a different pin and its own source/body/consumer audit; it is excluded from that historical audit. Handwritten notes apply only to their exact source, version and hashes. Finite-exploding version 7 and Lemmas 3.5, 3.6 and 3.7 version 5 include p = 1 under their respective pins. Five remaining strict Bernoulli paper rows remain narrower at p = 1.

| term | meaning |
|---|---|
| registered node | a manifest-owned declaration. Theorem nodes claim numbered source statements; definition nodes record literal or cited-input definitions and add no theorem coverage. |
| frozen statement | the declaration text between FROZEN-STATEMENT-BEGIN and FROZEN-STATEMENT-END, pinned by its exact SHA-256; any proof follows the end marker. |
| PROVED / SEALED | a theorem node with a complete proof and recorded clean axiom closure. PROVED also records passing source/semantic and independent audits; no row is currently SEALED. |
| FROZEN | a pinned definition contract with no theorem-proof claim. It includes cited-input definitions and, after independent audit, may include literal local definitions; it does not mean every definition is a literature assumption. |
| axiom closure | the axioms a proof ultimately rests on, as reported by Lean's #print axioms. |
| sorryAx | the axiom Lean inserts for an unproved sorry; its presence in an axiom closure means the result is not proved. |

The journal rows' summaries above retain their journal-source scope. Historical handwritten statement/citation audits and `paper_anchors.py` / `paper_citations.py` select only rows pinned to the exact default journal source; the official-ArXiv and corrected-v10 rows are excluded from those old-source endpoint claims. A stale v3 identity must fail against the changed live export, not be silently rebound to v4.

`tools/check_coverage.py` partitions claims by effective source pin and checks the three exact allowed-gap sets in the manifest. It reports journal 19/24, official arXiv 3/24 and corrected-v10 2/24. Definitions contribute zero theorem-like claims. This structural check does not establish mathematical equivalence. Five strict Bernoulli endpoint gaps and the other unclaimed arXiv statements remain outside these rows’ certification.

check_clauses.py and check_exponents.py are review aids bound to recorded source-specific readings. An empty annotation set is not evidence of correspondence; no unreviewed source or proof result is inferred from it. Historical audit fixtures remain bound to their exact v3 identities.

### Which Lean statement formalizes which result

The table links the paper's statements to the frozen Lean declarations and gives each one's
state.  It is generated from the manifest and the paper; it does not prove mathematical
correspondence between the two sources.

<!-- PAPER-MAP-BEGIN (generated by tools/sync_docs.py) -->

| Pinned source | Paper statement or definition | Description | Lean declaration | State |
|---|---|---|---|---|
| `paper/corrected-arxiv/exploding-corrected-arxiv.tex` | [Definition registration, lines 100-102](paper/corrected-arxiv/exploding-corrected-arxiv.tex#L100) | Non-External definition; literal-body/source audit required | [Exploding.counterexampleThreshold](Exploding/Frozen/CounterexampleThreshold.lean#L14) | FROZEN definition; source/body audit required |
| `paper/corrected-arxiv/exploding-corrected-arxiv.tex` | [Definition registration, lines 103-103](paper/corrected-arxiv/exploding-corrected-arxiv.tex#L103) | Non-External definition; literal-body/source audit required | [Exploding.counterexamplePile](Exploding/Frozen/CounterexamplePile.lean#L13) | FROZEN definition; source/body audit required |
| `paper/corrected-arxiv/exploding-corrected-arxiv.tex` | [Definition registration, lines 109-111](paper/corrected-arxiv/exploding-corrected-arxiv.tex#L109) | Non-External definition; literal-body/source audit required | [Exploding.counterexampleSupport](Exploding/Frozen/CounterexampleSupport.lean#L13) | FROZEN definition; source/body audit required |
| `paper/corrected-arxiv/exploding-corrected-arxiv.tex` | [Definition registration, lines 118-118](paper/corrected-arxiv/exploding-corrected-arxiv.tex#L118) | Non-External definition; literal-body/source audit required | [Exploding.counterexampleArrival](Exploding/Frozen/CounterexampleArrival.lean#L13) | FROZEN definition; source/body audit required |
| `paper/corrected-arxiv/exploding-corrected-arxiv.tex` | [Proposition 2.1](paper/corrected-arxiv/exploding-corrected-arxiv.tex#L286)<br>`prop:crossing_time` | Large boxes are crossed quickly | [Exploding.Frozen.crossing_time](Exploding/Frozen/CrossingTime.lean#L14) | proved, independently audited |
| `paper/corrected-arxiv/exploding-corrected-arxiv.tex` | [Theorem 6.1](paper/corrected-arxiv/exploding-corrected-arxiv.tex#L1875)<br>`theorem:counterexample` | Explosive backgrounds without a limit shape | [Exploding.Frozen.counterexample](Exploding/Frozen/Counterexample.lean#L13) | proved, independently audited |
| `paper/exploding-arxiv.tex` | [Lemma 3.5](paper/exploding-arxiv.tex#L652)<br>`lemma:last_penultimate_cluster` | Penultimate clusters are polylogarithmically small | [Exploding.Frozen.last_penultimate_cluster](Exploding/Frozen/PenultimateCluster.lean#L31) | proved, independently audited |
| `paper/exploding-arxiv.tex` | [Lemma 3.6](paper/exploding-arxiv.tex#L667)<br>`lemma:penultimate_upper_bound` | A linear upper bound on last-wave arrival times | [Exploding.Frozen.penultimate_upper_bound](Exploding/Frozen/PenultimateUpperBound.lean#L29) | proved, independently audited |
| `paper/exploding-arxiv.tex` | [Lemma 3.7](paper/exploding-arxiv.tex#L692)<br>`lemma:last_penultimate_close` | Last-wave and penultimate-cluster arrival times are close | [Exploding.Frozen.last_penultimate_close](Exploding/Frozen/PenultimateClose.lean#L32) | proved, independently audited |
| `paper/exploding.tex` | [Theorem 1.1](paper/exploding.tex#L238)<br>`prop:fey_levine_peres_explode` | Explosion of the Bernoulli background (Fey, Levine and Peres), cited | [Exploding.External.FeyLevinePeresExplosive](Exploding/External/FeyLevinePeres.lean#L18) | cited result, hypothesis |
| `paper/exploding.tex` | [Theorem 1.1](paper/exploding.tex#L238)<br>`prop:fey_levine_peres_explode` | In-repo discharge of the Fey, Levine and Peres explosion theorem | [Exploding.xsr_flp](Exploding/Support/ExtSchFLP.lean#L8) | proved, independently audited |
| `paper/exploding.tex` | [Theorem 1.2](paper/exploding.tex#L246)<br>`theorem:limit_shape` | The rescaled toppled region converges to a convex domain | [Exploding.Frozen.limit_shape](Exploding/Frozen/LimitShape.lean#L30) | proved, independently audited |
| `paper/exploding.tex` | [Theorem 1.3](paper/exploding.tex#L259)<br>`theorem:convergence_of_time_constant` | The rescaled arrival times converge | [Exploding.Frozen.convergence_of_time_constant](Exploding/Frozen/TimeConstant.lean#L33) | proved, independently audited |
| `paper/exploding.tex` | [Theorem 1.4](paper/exploding.tex#L265)<br>`theorem:explosive` | A criterion for a product background to explode | [Exploding.Frozen.explosive](Exploding/Frozen/Explosive.lean#L28) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | The chemical distance in supercritical bond percolation (Antal and Pisztora), cited | [Exploding.External.AntalPisztoraChemicalDistance](Exploding/External/AntalPisztora.lean#L29) | cited result, hypothesis |
| `paper/exploding.tex` | [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | Domination by a product measure on a dependence graph of bounded degree (Liggett, Schonmann and Stacey), cited | [Exploding.External.LiggettSchonmannStaceyBoundedDegree](Exploding/External/LiggettSchonmannStaceyBoundedDegree.lean#L31) | cited result, hypothesis |
| `paper/exploding.tex` | [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | In-repo discharge of the bounded-degree Liggett, Schonmann and Stacey corollary | [Exploding.lssBoundedDegree](Exploding/External/LSSBoundedDegreeProved.lean#L8) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | The holes of the infinite cluster of site percolation (Mathieu), cited | [Exploding.External.MathieuHoleVolume](Exploding/External/MathieuHoles.lean#L28) | cited result, hypothesis |
| `paper/exploding.tex` | [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | In-repo discharge of Mathieu's hole-volume bound | [Exploding.xmf_proved](Exploding/Support/ExtMHHoleVolume.lean#L14) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 2.2](paper/exploding.tex#L482)<br>`prop:renormalization_properties` | The infinite cluster of good cubes | [Exploding.Frozen.renormalization_properties](Exploding/Frozen/Renormalization.lean#L37) | proved, independently audited |
| `paper/exploding.tex` | [Lemma 2.1](paper/exploding.tex#L531)<br>`lemma:local_convexity` | A path of topplings fills its bounding rectangle | [Exploding.Frozen.local_convexity](Exploding/Frozen/LocalConvexity.lean#L20) | proved, independently audited |
| `paper/exploding.tex` | [Lemma 3.1](paper/exploding.tex#L705)<br>`lemma:square_lower_bound` | A wave of order (2d)^(dn) covers the box of radius n | [Exploding.Frozen.square_lower_bound](Exploding/Frozen/SquareLowerBound.lean#L22) | proved, independently audited |
| `paper/exploding.tex` | [Lemma 3.2](paper/exploding.tex#L720)<br>`lemma:finite_exploding` | The last wave is well defined | [Exploding.Frozen.finite_exploding](Exploding/Frozen/FiniteExploding.lean#L28) | proved, independently audited |
| `paper/exploding.tex` | [Lemma 3.3](paper/exploding.tex#L730)<br>`lemma:last_wave_bound` | The last wave exceeds the penultimate wave by at most one | [Exploding.Frozen.last_wave_bound](Exploding/Frozen/LastWaveBound.lean#L24) | proved, independently audited |
| `paper/exploding.tex` | [Lemma 3.4](paper/exploding.tex#L760)<br>`lemma:approx_subadditivity` | Penultimate-cluster arrival times are subadditive | [Exploding.Frozen.approx_subadditivity](Exploding/Frozen/ApproxSubadditivity.lean#L105) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 3.1](paper/exploding.tex#L846)<br>`prop:convergence_of_the_last_wave` | Convergence of the last wave | [Exploding.Frozen.convergence_of_the_last_wave](Exploding/Frozen/LastWaveConvergence.lean#L34) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 4.1](paper/exploding.tex#L886)<br>`prop:approximate_subadditive` | The last wave approximates the exploding sandpile | [Exploding.Frozen.approximate_subadditive](Exploding/Frozen/ApproximateSubadditive.lean#L35) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 5.1](paper/exploding.tex#L1203)<br>`prop:convergence_of_the_generalized_last_wave` | Convergence of the last wave under the general hypotheses | [Exploding.Frozen.convergence_of_the_generalized_last_wave](Exploding/Frozen/GeneralizedLastWave.lean#L40) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 5.1](paper/exploding.tex#L1203)<br>`prop:convergence_of_the_generalized_last_wave` | Domination of a finitely dependent field by a product measure (Liggett, Schonmann and Stacey), cited | [Exploding.External.LiggettSchonmannStacey](Exploding/External/LiggettSchonmannStacey.lean#L26) | cited result, hypothesis |
| `paper/exploding.tex` | [Proposition 5.1](paper/exploding.tex#L1203)<br>`prop:convergence_of_the_generalized_last_wave` | In-repo discharge of the Liggett, Schonmann and Stacey domination theorem | [Exploding.xlse_lss_general](Exploding/Support/ExtLSSCountable.lean#L120) | proved, independently audited |
| `paper/exploding.tex` | [Theorem 5.1](paper/exploding.tex#L1249) | Convergence of the exploding sandpile under the general hypotheses | [Exploding.Frozen.generalized_convergence](Exploding/Frozen/GeneralizedConvergence.lean#L33) | proved, independently audited |
| `paper/exploding.tex` | [Theorem 6.1](paper/exploding.tex#L1351)<br>`theorem:counterexample` | The least action principle (Fey, Meester and Redig), cited | [Exploding.External.FeyMeesterRedigLeastAction](Exploding/External/FeyMeesterRedig.lean#L40) | cited result, hypothesis |
| `paper/exploding.tex` | [Theorem 6.1](paper/exploding.tex#L1351)<br>`theorem:counterexample` | In-repo discharge of the Fey, Meester and Redig least action principle | [Exploding.xfmr_proved](Exploding/Support/ExtFMR.lean#L58) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 7.1](paper/exploding.tex#L1821)<br>`prop:explosion_criteria` | A criterion for a background law to explode | [Exploding.Frozen.explosion_criteria](Exploding/Frozen/ExplosionCriteria.lean#L19) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 7.2](paper/exploding.tex#L1890)<br>`prop:dimensional_reduction` | Dynamics on a face reduce to one dimension lower | [Exploding.Frozen.dimensional_reduction](Exploding/Frozen/DimensionalReduction.lean#L24) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 7.3](paper/exploding.tex#L1927)<br>`prop:recurrence` | The constant background d is recurrent | [Exploding.Frozen.recurrence](Exploding/Frozen/Recurrence.lean#L17) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 7.4](paper/exploding.tex#L1969)<br>`prop:schonnmann_bootstrap` | Schonmann's bound for bootstrap percolation, cited | [Exploding.External.SchonmannBootstrap](Exploding/External/Schonmann.lean#L23) | cited result, hypothesis |
| `paper/exploding.tex` | [Proposition 7.4](paper/exploding.tex#L1969)<br>`prop:schonnmann_bootstrap` | In-repo discharge of Schonmann's bootstrap bound | [Exploding.xsr_schonmann](Exploding/Support/ExtSchFinal.lean#L72) | proved, independently audited |
| `paper/exploding.tex` | [Proposition 7.5](paper/exploding.tex#L1986) | The background of Theorem 1.4 is box-crossing | [Exploding.Frozen.box_crossing](Exploding/Frozen/BoxCrossing.lean#L22) | proved, independently audited |

<!-- PAPER-MAP-END -->

## Guarantees

The corrected-v10 counterexample and its four literal definitions passed exact integrated Lean checks, a full locked 9,405-job build, all eleven configured checks and independent source/body/consumer audit. That promotion covers its counterexample theorem; the [dated receipt](ledger/audits/2026-10-15-counterexample-v4-promotion.md) records the exact declaration and evidence. The corrected crossing successor has a separate [validation receipt](ledger/audits/2026-10-15-crossing-v4-promotion.md). The ordinary bond-hole Support modules imported by the root add no numbered-theorem credit; they do not establish corrected Proposition 2.2, a fixed-root hole tail or its exact alpha constant.

- No sorry, admit or custom axiom in the production library. The comparator challenge contains one intentional statement-level sorry.
- Axiom closure. The accepted theorem rows have clean closures; the corrected counterexample and its four definitions were checked against the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
- Comparator scope. The comparator remains the historical Theorem 1.2 limit-shape comparison with its four explicit hypotheses. It is not a comparator for v4 or corrected v10 as a whole.
- Pinned toolchain. The build uses the toolchain and dependency revisions recorded in lean-toolchain and lake-manifest.json.

## Size

The production library contains 357 Lean modules, including the root module and the two ordinary bond-hole Support modules.

## Building

The project uses elan and Lake. The toolchain is pinned in lean-toolchain, with dependency revisions in lakefile.lean and lake-manifest.json.

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
formalization.yaml    source, statement, axiom and review metadata
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
