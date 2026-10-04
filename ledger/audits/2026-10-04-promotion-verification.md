# Independent promotion verification — Exploding-Sandpiles (2026-10-04)

* **Auditor:** DeepSeek fleet, independent verification of the 2026-10-04 promotion.
* **Repository:** `~/lean/Exploding-Sandpiles` (working tree as read; **no `git` and no `lake build` run**, per instructions).
* **Paper pin:** `paper/exploding.tex`, sha256 `1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44` (matches `ledger/manifest.yaml:source_pin`).
* **Scope:** (1) run `tools/verify.py`; (2) confirm the manifest tally; (3) spot-check the batch-A/B reports and the triage against the frozen blocks of three nodes; (4) confirm `check_clauses`/`check_exponents` are non-vacuous. Wrote no file except this report.

## 1. Gate suite

```
$ cd ~/lean/Exploding-Sandpiles && export PATH=$HOME/.elan/bin:$PATH && python3 tools/verify.py
check_manifest: OK (29 nodes, 0 unsealed; closure 29 checked, 0 skipped; 460 Exploding declarations indexed)
check_coverage: 24 statements in the paper, 24 formalized
check_clauses: OK (22 statements, each read against the paper and its correspondence recorded; 4 where the paper is recorded as asserting more, all explained above)
check_exponents: OK (26 statements; every paper exponent appears in its Lean statement or is explained above)
check_axioms: 29 clean, 0 depend on sorryAx, 0 unresolved
check_warnings: OK (0 registered sorry warnings)
verify: axiom closures agree with the manifest (29 clean, 0 open or resting on open nodes)
verify: all checks passed
```

`#print axioms` on all 29 exports remains exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. **PASS.**

## 2. Manifest tally

Parsed `ledger/manifest.yaml` directly:

| state | count |
|---|---|
| `PROVED` | **22** |
| `SEALED` | **0** |
| `FROZEN` | **7** |
| `DRAFT_SORRY` | 0 |
| `CONDITIONAL` | 0 |

The 7 `FROZEN` entries are the registered `Exploding.External.*` inputs `ext-fey-levine-peres`, `ext-schonmann-bootstrap`, `ext-liggett-schonmann-stacey`, `ext-lss-bounded-degree`, `ext-antal-pisztora`, `ext-mathieu-holes`, `ext-fey-meester-redig`; the 22 `PROVED` entries are all theorem nodes. **PASS.**

## 3. Spot-check of batch-A/B reports and triage vs the frozen blocks (3 nodes + the triage flag)

Frozen-block SHA-256 recomputed independently for each checked node and matched the manifest (`match=True`); each node is `PROVED`.

| node | source | report/triage claim | frozen block | verdict |
|---|---|---|---|---|
| `thm-time-constant` | batch A + triage | A report: `N` bound before `η`; `Continuous ∧ ConvexOn ∧` one-homogeneity; `ε`-form convergence; a.s. event `Explosive η ∧ ∀x, arrival η x ≠ ⊤`. Triage: "benign explicit rendering"; the added conjuncts are the a.s. content of `hFLP` and the finiteness implicit in convergence. | `TimeConstant.lean:38-46`: exactly `∃N, Continuous N ∧ ConvexOn ℝ Set.univ N ∧ (∀c≥0, N(c•y)=c·N y) ∧ ∀ᵐη ∂(toyLaw d p), Explosive η ∧ (∀x, arrival η x ≠ ⊤) ∧ …` | **MATCH** |
| `prop-renormalization` | batch A + `check_clauses` flag | A report: quantifier order `∃k0, ∀k≥k0, ∃c C>0`, then a.s. `η`; clause (1) `IsInfiniteConnectedGoodSet`; clause (2) finiteness + `< (log n)^{5/2}`; clause (3) `ℕ∞` + `∃m` + two-sided bound. `check_clauses` REVIEWED: three Lean conjuncts; paper count 5 = three items plus the two relations of item 3 (count artifact). | `Renormalization.lean:41-51`: exactly three top-level conjuncts — `IsInfiniteConnectedGoodSet … ∧ (∃n0 … (componentIn …).Finite ∧ ncard < (log n)^{5/2}) ∧ (∃n0 … ∃m, chemDist = m ∧ c·mnorm ≤ m ≤ C·mnorm)` | **MATCH** |
| `prop-generalized-last-wave` | batch B + `check_clauses` REVIEWED | B report: `hηmin`/`hsupp`/`hstat`/`herg`/`h1`/`h3`/`h4` are the paper's own Section 5 hypotheses; `hLSS`, `hLSSB`, `hHole`, `hChem` registered Externals; `N` before `η`; a.s. event carries `Explosive η` and finiteness of `lastArrival`. REVIEWED: same. | `GeneralizedLastWave.lean:40-60`: binders `ηmin, hηmin, L, hL, P, hP, hsupp, hstat, herg, h1, h3, h4, hLSS, hLSSB, hHole, hChem`; conclusion `∃N, Continuous ∧ ConvexOn ∧ one-homog ∧ ∀ᵐη ∂P, Explosive η ∧ (∀x, lastArrival η 0 x ≠ ⊤) ∧ ε-convergence` | **MATCH** |
| `lem-finite-exploding` (triage flag) | triage + `check_clauses` `FLAGGED` | Triage: "Lean conclusion is `∀ᵐ η ∂(toyLaw d p), ∃ n ≥ 1, ¬ WaveStabilizable η n 0` … does **not** assert `\hat M_η(0) < ∞`". | `FiniteExploding.lean:31`: `∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)` | **MATCH (flag is real)** |

No source-fidelity mismatch was found between the two audit reports, the `check_clauses` REVIEWED lines, and the frozen blocks for these nodes. The `lem-finite-exploding` partial-transcription flag is correctly wired (`check_clauses.FLAGGED` contains it) and matches the frozen bytes; it is a recorded weakening, not a hidden one.

## 4. `check_clauses` / `check_exponents` non-vacuity

Both gates now derive the paper stem from `paper_path().name`; `grep -n rotor tools/check_clauses.py tools/check_exponents.py` returns nothing.

```
$ python3 tools/check_clauses.py
  ... 22 node rows ...
check_clauses: OK (22 statements, each read against the paper and its correspondence recorded; 4 where the paper is recorded as asserting more, all explained above)

$ python3 tools/check_exponents.py
  ... 26 node rows ...
check_exponents: OK (26 statements; every paper exponent appears in its Lean statement or is explained above)
```

`check_clauses` inspects **22** paper-bearing statements (its `REVIEWED` table is populated for all of them) and `check_exponents` inspects **26** statements with `EXPECTED_ABSENT` reasons for every notation-only superscript (`d`, `(d)`, `(i)`, `(z)`, `c` in `C_∞^c`, etc.). **Both gates are non-vacuous. PASS.** This supersedes the "vacuous gate" notes in the batch-A report (N5) and the batch-B report (N3), which were written before `2026-10-04-gates-repaired.md`.

## 5. Findings

1. **DEFECT (documentation only) — the triage names a non-existent External.** `ledger/audits/2026-10-03-script-audit-triage.md:13` lists the carried binders as `Exploding.External.{LiggettSchonmannStacey, LiggettSchonmannStaceyBoundedDegree, MathieuHoleVolume, AntalPisztoraChemicalDistance, FeyMeesterRedigLeastAction, SchonmannBootstrap, Schauder}`. There is **no `Exploding.External.Schauder`** anywhere: the production tree defines exactly seven `External` `Prop`s (`AntalPisztoraChemicalDistance`, `FeyLevinePeresExplosive`, `FeyMeesterRedigLeastAction`, `LiggettSchonmannStacey`, `LiggettSchonmannStaceyBoundedDegree`, `MathieuHoleVolume`, `SchonmannBootstrap`), the manifest has exactly those 7 `FROZEN` nodes, and `grep -rin schauder` matches only that one triage line. Reproducer:
   ```
   $ grep -rho "def Exploding\.External\.[A-Za-z]*" Exploding/External/*.lean | sort -u
   def Exploding.External.AntalPisztoraChemicalDistance
   def Exploding.External.FeyLevinePeresExplosive
   def Exploding.External.FeyMeesterRedigLeastAction
   def Exploding.External.LiggettSchonmannStacey
   def Exploding.External.LiggettSchonmannStaceyBoundedDegree
   def Exploding.External.MathieuHoleVolume
   def Exploding.External.SchonmannBootstrap
   $ grep -rin schauder . --include=*.lean --include=*.md --include=*.yaml --include=*.py | grep -v '^./.lake'
   ./ledger/audits/2026-10-03-script-audit-triage.md:13:Schauder}`, every one a registered ...
   ```
   This does not affect any frozen statement or proof (no node uses a `Schauder` binder); it is a stale name in the triage's prose and should be struck from that document.
2. **Conditionality still stands (recorded, unchanged).** `thm-limit-shape`, `thm-time-constant`, `prop-renormalization`, all six batch-B nodes and `prop-generalized-last-wave` remain conditional on the one registered-but-unproved External `ext-antal-pisztora` (`hChem`), and `prop-generalized-last-wave` additionally on Hypotheses 5.1/5.3/5.4. This is the documented design and is not a promotion blocker; the 22 `PROVED` states record a proved conditional theorem, as the promotion note says.
3. **`lem-finite-exploding`** is `PROVED` while carrying the triage's partial-transcription flag (existence half of the paper's last-wave lemma, without `\hat M_\eta(0) < ∞`). The flag is correctly recorded and printed by `check_clauses`; it is a tracked weakening for the owner, not a hidden one.

## 6. What I could not verify

* The exact commit id: instructions forbade `git`, so I did not read `HEAD`; the verification is of the working tree as read (the manifest, paper pin and all 29 frozen hashes are self-consistent).
* I did not re-run `lake build` (forbidden); the clean closures come from `check_axioms`/`check_warnings`, which invoke `lake env lean` on the audit file.
* I re-read 3 nodes' reports/triage against their frozen blocks in detail, not all 22; the other 19 `check_clauses` `REVIEWED` lines and the batch reports were read for consistency but not byte-diffed line by line in this pass.
* I did not adjudicate the truth of the unproved External `ext-antal-pisztora` or the satisfiability of Hypotheses 5.1/5.3/5.4.

## Conclusion

The promotion is **verified**: `tools/verify.py` passes; the manifest is exactly **22 `PROVED` / 0 `SEALED` / 7 `FROZEN`**; the three spot-checked nodes (`thm-time-constant`, `prop-renormalization`, `prop-generalized-last-wave`) and the `lem-finite-exploding` flag match their frozen blocks and the batch-A/B reports and triage; and `check_clauses` (22 statements) and `check_exponents` (26 statements) are non-vacuous. The only discrepancy found is a documentation-only stale name (`Schauder`) in the triage's External list, which names no existing node and affects neither the frozen statements nor the proofs.
