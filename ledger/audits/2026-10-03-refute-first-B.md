# Independent refute-first audit — Exploding-Sandpiles, Batch B

* **Auditor:** DeepSeek fleet, second-key audit (independent; wrote none of the development).
* **Batch B:** `lem-penultimate-cluster`, `lem-penultimate-upper-bound`, `lem-penultimate-close`, `prop-last-wave-convergence`, `prop-approximate-subadditive`, `prop-generalized-last-wave`.
* **Repository:** `~/lean/Exploding-Sandpiles`.
* **Head read** (`git rev-parse HEAD`, read-only): `2ad193d428b6aee264a45b3750259c2bbaae0533`. The brief's pin `326a151` is an ancestor of this head. `git diff --stat 326a151 HEAD -- Exploding/Frozen ledger/manifest.yaml` is empty and `git diff --name-only 326a151 HEAD` lists only `Exploding.lean`, `Exploding/Support/ExtAPStarDuality.lean` and the Batch-A report, so the frozen blocks, the manifest and every provider of my six nodes are byte-identical at the two commits. I read and ran the gates on the current tree; the results apply verbatim to the pin.
* **Paper pin:** `paper/exploding.tex`, sha256 `1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44` (matches `ledger/manifest.yaml:source_pin`).
* **Constraints observed:** no `git add/commit/push`, no `lake build`, no file edited except this report. The only `git` commands were read-only (`rev-parse`, `cat-file`, `diff`, `show`).

## Gate results (exact commands and output)

```
$ cd ~/lean/Exploding-Sandpiles && export PATH=$HOME/.elan/bin:$PATH
$ python3 tools/check_manifest.py
check_manifest: OK (29 nodes, 0 unsealed; closure 29 checked, 0 skipped; 460 Exploding declarations indexed)

$ python3 tools/check_axioms.py
  clean   lem-penultimate-cluster
  clean   lem-penultimate-upper-bound
  clean   lem-penultimate-close
  clean   prop-last-wave-convergence
  clean   prop-approximate-subadditive
  clean   prop-generalized-last-wave
  ...
29 clean, 0 depend on sorryAx, 0 unresolved
verify: axiom closures agree with the manifest (29 clean, 0 open or resting on open nodes)

$ python3 tools/verify.py
... certificate: OK ... 
verify: all checks passed
```

`tools/check_warnings.py` (replaying `Exploding/Meta/AxiomsAudit.lean`) prints for
every export, including my six, exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

and `check_warnings: OK (0 registered sorry warnings)`. There is no `sorryAx` in
any closure. `check_manifest` reports `0 unsealed`, so no node is conditional on
a `DRAFT_SORRY` predecessor.

Independent byte-level recomputation of the six frozen blocks (SHA-256 over the
bytes strictly between the marker lines, marker lines excluded), plus a token
scan of the block for `axiom`, `admit`, `sorry`, `native_decide`, `set_option`:

| node | block bytes | recomputed SHA-256 | manifest | banned tokens |
|---|---|---|---|---|
| `lem-penultimate-cluster` | 539 | `3cfbfa23e89ec1c52bed2c12a4a6be62d2cd17bb135b6f9438498d8f244d8544` | ✅ | none |
| `lem-penultimate-upper-bound` | 584 | `755dc2bd6ea319253c74e38c3f0320cd0b6ec98d60157d330873710e2519e903` | ✅ | none |
| `lem-penultimate-close` | 698 | `155ee18f906de192a37114b586420bfae02efadb3d6d74235494dccf37ea9af7` | ✅ | none |
| `prop-last-wave-convergence` | 841 | `757cd6a770e4ea98496b4203ac93795842f3cbafac4b0ee55cea24e49f32e679` | ✅ | none |
| `prop-approximate-subadditive` | 504 | `724f16a435a724da7cf5af101b9d248d41329ddd4286e2360a1502aa9f2138a4` | ✅ | none |
| `prop-generalized-last-wave` | 1241 | `63edbd1a3a9902f41df41c9c3efbe3e73ae7802ffacce176582e67f10b0cf8f3` | ✅ | none |

Exactly one frozen block per file; each block contains exactly one `theorem`.
All six closure hashes also match (`closure 29 checked, 0 skipped`).

## Verdict table

| node | verdict | evidence |
|---|---|---|
| `lem-penultimate-cluster` | PASS | hash ✅; closure exactly `{propext, Classical.choice, Quot.sound}`; faithful to `exploding.tex:792-798`; proof `Frozen.last_penultimate_cluster` calls `renormalization_properties` and the guard `aux_penultimate_bounds`; non-vacuous (`P(x) ∋ x`). Conditional on `hChem` (N1). |
| `lem-penultimate-upper-bound` | PASS | hash ✅; closure ✅; faithful to `exploding.tex:807-812`; provider `Exploding.pub_penultimate_upper_bound`; non-vacuous (finiteness asserted by `∃ m`). Conditional on `hChem` (N1). |
| `lem-penultimate-close` | PASS | hash ✅; closure ✅; faithful to `exploding.tex:832-837`; provider `pclose_second` + `lastArrival_le_clusterArrival`; non-vacuous. Conditional on `hChem` (N1). |
| `prop-last-wave-convergence` | PASS | hash ✅; closure ✅; faithful to `exploding.tex:846-852`; assembles `king_hking`/`lwc_far_lipschitz`/`lwc_transfer`/`lwc3_lattice_upgrade`; finiteness of `T̂` asserted in the a.s. event. Conditional on `hChem` (N1). |
| `prop-approximate-subadditive` | PASS | hash ✅; closure ✅; faithful to `exploding.tex:886-898`; provider `asd_approximate_subadditive`; constants correctly bound after `η`. Conditional on `hChem` (N1). |
| `prop-generalized-last-wave` | PASS | hash ✅; closure ✅; faithful to `exploding.tex:1203-1207` under Section 5's standing hypotheses; provider `glws_conclusion`. Conditional on `hChem` and on `h1/h3/h4` (N1, N2). |

No FAIL. No node is conditional on a `DRAFT_SORRY` predecessor.

## Per-node source fidelity and binder classification

### `lem-penultimate-cluster` — `Exploding/Frozen/PenultimateCluster.lean:29-35`
Paper `exploding.tex:792-798`:
> There is a constant `γ > 0` so that for all `n` sufficiently large and `|x| ≤ n`, `P(x) ⊂ x + [-(log n)^γ, (log n)^γ]^d`.

Lean:
```
theorem ... (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB …) (hHole …) (hChem …) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∀ y ∈ penultimateCluster η x, ∀ i, ((|y i - x i| : ℤ) : ℝ) ≤ Real.log n ^ γ
```
* `hd : 2 ≤ d` — SOURCE (paper's `d ≥ 2`; `p` of (1.2)).
* `hp : 0 < p`, `hp1 : p < 1` — SOURCE + RULED (the paper writes `p > 0`; `p < 1` excludes the deterministic endpoint, documented by Batch A as ruling R-p; it is a hypothesis strengthening, so the formal theorem is weaker than the literal paper claim at `p = 1`).
* `hLSSB, hHole, hChem` — STANDING/External: the cited results consumed by the Section 3 proof (Liggett–Schonmann–Stacey Cor. 1.4, Mathieu Lem. 5.2, Antal–Pisztora Thm 1.1). No EXCESS binder.
* `γ` bound before `η` (deterministic), threshold `n0` bound after `η` — matches "for all `n` sufficiently large"; the paper makes the a.s. good event explicit only in the Section 3 preamble (`exploding.tex:703-704`), which the Lean makes explicit with `∀ᵐ η`.
* `P(x)` is `penultimateCluster η x`, exactly eq:penultimate_cluster (`exploding.tex:683-684`); `|y_i - x_i| ≤ (log n)^γ` is the coordinatewise containment; `Real.log n ^ γ` is `Real.rpow`.

### `lem-penultimate-upper-bound` — `Exploding/Frozen/PenultimateUpperBound.lean:27-34`
Paper `exploding.tex:807-812`:
> There are constants `γ` and `C` so that on an event of probability 1, for all `n` sufficiently large and `|x| ≤ n`, `T̂(x) ≤ C|x| + (log n)^γ`.

Lean:
```
∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
  ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
    ∃ m : ℕ, lastArrival η (0 : Site d) x = (m : ℕ∞) ∧
      (m : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ
```
`T̂(x) = lastArrival η 0 x` (eq:lastwave_fpp, `exploding.tex:690-691`); `γ, C` deterministic (before `η`), positive; the `∃ m` records that `T̂(x)` is finite so the real comparison is not read through `ENat.toNat ⊤`. `|x| = mnorm x` (ℓ¹). No EXCESS binder.

### `lem-penultimate-close` — `Exploding/Frozen/PenultimateClose.lean:31-38`
Paper `exploding.tex:832-837`:
> There exists a constant `γ > 0` so that on an event of probability 1, for all `n` sufficiently large and `|x| ≤ n`, `T̂(x) ≤ T̃(x) ≤ T̂(x) + (log n)^γ`.

Lean:
```
∃ γ : ℝ, 0 < γ ∧
  ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
    lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
      ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
        clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ
```
`T̃ = clusterArrival` (eq:lastwave_modified_fpp, `exploding.tex:694-695`); first inequality in `ℕ∞`, second through `∃ a b` so both times are finite and no `toNat ⊤ = 0` is used. Faithful. No EXCESS binder.

### `prop-last-wave-convergence` — `Exploding/Frozen/LastWaveConvergence.lean:33-44`
Paper `exploding.tex:846-852`:
> On an event of probability 1, the rescaled last-wave arrival times `n^{-1} T̂_η([n x])` converge locally uniformly to `N_p`, a continuous, convex, one-homogeneous function on `ℝ^d`.

Lean:
```
∃ N : (Fin d → ℝ) → ℝ,
  Continuous N ∧ ConvexOn ℝ Set.univ N ∧
  (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
  ∀ᵐ η ∂(toyLaw d p),
    (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
      ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
          |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) - N y| ≤ ε
```
`N` is deterministic (bound before `η`) and is the paper's `N_p`; local uniform convergence is the ε-form over compact `K`; `[n x]` is `nearestSite` (`Vocab.lean:187`); the conjunct `∀ x, lastArrival … ≠ ⊤` makes the `toNat` division honest (the paper's last wave is well defined). No EXCESS binder.

### `prop-approximate-subadditive` — `Exploding/Frozen/ApproximateSubadditive.lean:34-40`
Paper `exploding.tex:886-898`:
> On an event of probability 1, there are constants `C_1(η), C_2(η)` so that for all `x ∈ ℤ^d`, `T(x) ≤ T̂(x) + C_1(η)` and `T̂(x) ≤ T(x) + C_2(η)`, where … `T(x) := min{t ≥ 0 : v_t(x) > 0}`.

Lean:
```
∀ᵐ η ∂(toyLaw d p), ∃ C1 C2 : ℕ, ∀ x : Site d,
  arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
    lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞)
```
`T = arrival` and `T̂ = lastArrival`; constants bound after `η` (they may depend on `η`); both inequalities in `ℕ∞`. The paper's `min{t ≥ 0}` and the Lean `sInf` over `1 ≤ n` (`Vocab.lean:177`) coincide because `podo s0 0 = 0` (`Toppling.lean:77, podo_zero`), so `t = 0` never satisfies `v_t(x) > 0`; this is a definitional identity, not a hypothesis change. No EXCESS binder.

### `prop-generalized-last-wave` — `Exploding/Frozen/GeneralizedLastWave.lean:37-56`
Paper `exploding.tex:1203-1207`:
> Under Hypotheses 5.1, 5.3, and 5.4, on an event of probability 1, `η` is explosive and the rescaled last-wave arrival times `n^{-1} T̂_η([nx]) := n^{-1} min{t > 0 : u_t([nx]) > 0}` converge locally uniformly to `N_η`, a deterministic, continuous, convex, one-homogeneous function on `ℝ^d` depending only on the law of `η`.

Lean:
```
theorem ... (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : ErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P)
    (hLSS …) (hLSSB …) (hHole …) (hChem …) :
    ∃ N : (Fin d → ℝ) → ℝ, Continuous N ∧ ConvexOn ℝ Set.univ N ∧
      (∀ c, 0 ≤ c → ∀ y, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂P, Explosive η ∧ (∀ x, lastArrival η (0) x ≠ ⊤) ∧
        ∀ K, IsCompact K → ∀ ε, 0 < ε → ∀ᶠ n in atTop, ∀ y ∈ K,
          |((…).toNat : ℝ) / (n : ℝ) - N y| ≤ ε
```
* `hd : 2 ≤ d` — SOURCE (`d ≥ 2`).
* `ηmin : ℤ`, `hηmin : 0 ≤ ηmin` — SOURCE (Section 5 fixes `η_min ≥ 0`).
* `L : AddSubgroup (Site d)`, `hL : L.index ≠ 0` — SOURCE: `AddSubgroup.index : ℕ` is `Nat.card (G ⧸ H)`, and `Nat.card` of an infinite type is `0`, so `L.index ≠ 0` is exactly "finite-index subgroup" (`Mathlib/GroupTheory/Index.lean:57`, `index_top = 1`). This is the paper's finite-index sub-lattice `ℒ`.
* `P`, `hP : IsProbabilityMeasure P` — SOURCE (stationary ergodic probability measure).
* `hsupp : InOmega d ηmin η` a.s. — SOURCE (η ∈ Ω: `ηmin ≤ η ≤ 2d-1`, `Hypotheses.lean:99`).
* `hstat`, `herg` — SOURCE (`StationaryOn`/`ErgodicOn` wrt `L`, `Hypotheses.lean:103,107`).
* `h1 = Hypothesis 5.1` (`FiniteRangeOfDependence`), `h3 = Hypothesis 5.3` (`PathFillingHyp`), `h4 = Hypothesis 5.4` (`StronglyBoxCrossingHyp`) — SOURCE; Hypothesis 5.2 (`BoxCrossingHyp`) is correctly *not* assumed, as Prop 5.1 cites only 5.1, 5.3, 5.4 (`exploding.tex:1204`).
* `hLSS` (Theorem 0.0, cited at `exploding.tex:1215-1217`), `hLSSB`, `hHole`, `hChem` — STANDING/External. No EXCESS binder.
* `N` is bound before `η`, so it cannot depend on the realisation — this is the paper's "depending only on the law of `η`". `Explosive η` and finiteness of `T̂` are included in the a.s. event. Faithful.

## Recorded CONCERNs

**N1 — all six nodes are conditional on the one registered-but-unproved External `hChem`.** Each frozen statement carries `(hChem : Exploding.External.AntalPisztoraChemicalDistance)`. Of the Externals used, `hLSSB` (`Exploding.xlse_lss_bounded_degree`, `Support/ExtLSSCountable.lean:111`), `hHole` (`Exploding.xmf_proved`, `Support/ExtMHHoleVolume.lean:16`) and `hLSS` (`Exploding.xlse_lss_general`, `Support/ExtLSSCountable.lean:116`) are proved in-repo, but `AntalPisztoraChemicalDistance` is only ever a hypothesis. Reproducer:

```
$ grep -rn "AntalPisztoraChemicalDistance *:=" Exploding --include=*.lean
(no output)
$ grep -rn "theorem .*: *Exploding.External.AntalPisztoraChemicalDistance" Exploding --include=*.lean
(no output)
```

So as frozen these are **conditional theorems** relative to `hChem` (and, for `prop-generalized-last-wave`, relative to `h1/h3/h4`), by design (`CORRESPONDENCE.md`, Batch-A report N1). This does not falsify any statement, and `hChem` is a registered FROZEN provider, so the "proved from the registered providers" claim holds; but if `SEALED -> PROVED` is meant to record an unconditional proof, these nodes are PROVED only relative to that assumption.

**N2 — `prop-generalized-last-wave` is also conditional on Hypotheses 5.1/5.3/5.4.** These are the paper's own hypotheses (`exploding.tex:1137,1168,1189`) and are carried explicitly as `h1/h3/h4`; their joint satisfiability is not established in this repository for a concrete `P` (the paper constructs Bernoulli-cloud examples in §5.2). The a.s. conclusion is therefore not vacuous only *given* a model satisfying them. Recorded, not a source mismatch: the paper's Prop 5.1 is itself conditional on exactly these hypotheses.

**N3 — the "clause" and "exponent" gate scripts are vacuous for this repository.** Both select nodes with the stale regex `rotor\.tex:(\d+)-(\d+)`, whereas this manifest writes `exploding.tex:<range>`; each therefore reports `OK (0 statements …)`. Reproducer:

```
$ python3 tools/check_clauses.py
check_clauses: OK (0 statements, each read against the paper and its correspondence recorded; ...)
$ python3 tools/check_exponents.py
check_exponents: OK (0 statements; every paper exponent appears in its Lean statement or is explained above)
$ grep -n "rotor" tools/check_clauses.py tools/check_exponents.py
tools/check_clauses.py:119:        rng = re.search(r"rotor\.tex:(\d+)-(\d+)", src)
tools/check_exponents.py:126:        rng = re.search(r"rotor\.tex:(\d+)-(\d+)", node["source"])
```

My source-fidelity findings above are a hand comparison against the quoted `exploding.tex` lines, not the output of these scripts. This does not falsify any statement.

**N4 — `p < 1` strengthening.** The paper writes "Fix `p > 0`"; all five `toyLaw`-based nodes strengthen this to `0 < p < 1` (RULED, documented in Batch A). The `p = 1` deterministic endpoint is thus excluded; the formal statements are strictly weaker than the literal paper claims at that endpoint.

## What I could not verify

* I did not machine-check LaTeX-to-Lean equivalence; `check_clauses`/`check_exponents` are vacuous here (N3). My fidelity findings are a hand comparison against the quoted lines.
* I did not run `lake build` (per instructions); the clean closures come from `tools/check_axioms.py` and `tools/check_warnings.py`, which do invoke `lake env lean` on the audit files.
* I did not prove or otherwise establish the truth of the unproved External `hChem` (nor of the external results), and I did not construct a concrete `P` satisfying Hypotheses 5.1/5.3/5.4 for `prop-generalized-last-wave`; non-vacuity for those two CONCERNs rests on the paper's constructions, which I read but did not formalise.
* I did not re-derive the providers' mathematics (`renormalization_properties`, `pub_penultimate_upper_bound`, `pclose_second`, `king_hking`/`lwc_transfer`, `asd_approximate_subadditive`, `glws_conclusion`) line by line; I rely on their clean `#print axioms` (exactly `{propext, Classical.choice, Quot.sound}`, no `sorryAx`) and on `check_manifest`'s `0 unsealed`.
* The brief's suggested `python3 tools/check_manifest.py .` is not accepted (the tool takes only `--emit`); the repository-root invocation used above is the working one.

## Conclusion

All six Batch-B nodes **may be promoted `SEALED -> PROVED`**: each frozen block matches the manifest hash and its cited `exploding.tex` display, each has axiom closure exactly `{propext, Classical.choice, Quot.sound}` with no `sorryAx`, each passes `tools/verify.py`, and each is non-vacuous — with the recorded caveat that all six are **conditional on the one registered-but-unproved External `ext-antal-pisztora` (`hChem`)**, and `prop-generalized-last-wave` additionally on the paper's own Hypotheses 5.1/5.3/5.4.
