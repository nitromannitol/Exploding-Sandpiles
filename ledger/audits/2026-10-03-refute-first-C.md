# Independent refute-first audit — Exploding-Sandpiles, Batch C

Auditor: independent second-key audit, refute-first, read-only. This file is the only thing
written. `git add/commit/push` was not run; `lake build` was not invoked directly (the repo's
`tools/verify.py` ran the build step through `check_warnings`, which the brief names as a gate).

## Head commit read

* `git rev-parse HEAD` at report time: `9c6fedd5fdf0e6f69e50eebfba772f51e0a17fe9`.
* The brief pins the audit at `326a151`. That commit is not the current tree and I did not check
  it out (`git` is read-only here), so the frozen blocks audited are the ones in the current tree.
  The manifest `frozen_sha256` values match the current blocks, and all six nodes are now
  `state: PROVED` rather than `SEALED`, so the repository moved after the brief was written.

## Gates / integrity (exact commands)

Frozen-byte recomputation for the six nodes (one leading newline dropped) and a banned-token scan:
`sha_ok=True banned=[]` for all six. `banned` covers `axiom`, `native_decide`, `set_option`,
`sorry`, `admit`, `sorryAx`.

```
$ python3 tools/check_manifest.py
check_manifest: OK (29 nodes, 0 unsealed; closure 29 checked, 0 skipped; 460 Exploding declarations indexed)

$ python3 tools/verify.py
...
29 clean, 0 depend on sorryAx, 0 unresolved
verify: axiom closures agree with the manifest (29 clean, 0 open or resting on open nodes)

verify: all checks passed
```

`check_axioms.py` itself only tests the absence of `sorryAx`, so the exact closure was checked by
hand for the six exports:

```
$ lake env lean scratch/BatchCAx.lean
'Exploding.Frozen.generalized_convergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Exploding.Frozen.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'Exploding.Frozen.explosion_criteria' depends on axioms: [propext, Classical.choice, Quot.sound]
'Exploding.Frozen.box_crossing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Exploding.Frozen.last_wave_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Exploding.Frozen.dimensional_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All six closures are exactly `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.

## Verdicts

| node | verdict | evidence |
|---|---|---|
| `thm-generalized-convergence` | PASS | Frozen matches `exploding.tex:1249-1253`: `∃N` bound before `∀ᵐη`, `Continuous`/`ConvexOn`/one-homogeneous, local-uniform convergence of `arrival/n` to `N`. Carries the four registered External binders `hLSS`, `hLSSB`, `hHole`, `hChem` by design (all passed to the provider). Hash `d81928d…`, closure clean. Non-vacuity is conditional (see below). |
| `thm-counterexample` | FAIL | Unused registered External binder `hFMR` (EXCESS): present in the frozen statement but discarded by `have _ := hFMR`; the proof constructs `ceEta d` without it. Details below. |
| `prop-explosion-criteria` | PASS | Frozen matches `exploding.tex:1821-1825`: `h1`, `h2`, `hrec ⇒ ExplosiveLaw`; standing Section 5 binders (`hd`, `hηmin`, `L`, `hL`, `hP`, `hsupp`, `hstat`, `herg`). `hrec`/`hstat`/`herg`/`hL` are unused (proof proves the stronger `h1,h2` statement) but all are paper hypotheses, so not EXCESS. No External. Hash `1346c0f…`, closure clean. |
| `prop-box-crossing` | CONCERN | Paper states "In all dimensions" (`exploding.tex:1987`), and its proof handles dimension one (`:1990`); the frozen requires `hd : 2 ≤ d`, so the `d = 1` case is dropped. Weaker than the paper. Details below. |
| `lem-last-wave-bound` | PASS | Frozen matches `exploding.tex:730-735`: `lastWave η z t x ≤ 1 + penultimateWave η z x` under Section 3's `2d-2 ≤ η ≤ 2d-1` and the `hlast` well-definedness hypothesis; `ht : 1 ≤ t` is paper's (unused, linter silenced). Hash `747c9a0…`, closure clean. |
| `prop-dimensional-reduction` | PASS | Frozen matches `exploding.tex:1890-1899`: `redOdoUp (cons 1 y) = redOdoDown y` and `redConfUp (cons 1 y) = redConfDown y + 2` when the odometer is `0`, for `cons 1 y ∈ faceLow (d+1) n 0`. `hy` is a paper hypothesis (face membership), unused but not EXCESS. Hash `5777a52…`, closure clean. |

## FAIL / CONCERN details

### F1. `thm-counterexample` — unused registered External `hFMR`

Paper (`exploding.tex:1351-1361`): the theorem has no external hypothesis; Fey–Meester–Redig is
cited only inside the proof. Lean binder (`Exploding/Frozen/Counterexample.lean:30`):
```
(hFMR : Exploding.External.FeyMeesterRedigLeastAction) :
```
and the proof at line 40 is `have _ := hFMR`, after which `hFMR` is never used; the witness is
constructed unconditionally as `ceEta d`. By the brief's rule ("EXCESS = neither used by the proof
nor a paper hypothesis … any EXCESS is a FAIL") this is EXCESS. It only makes the frozen theorem
weaker, so the fix is either to drop the binder from the statement or to use it. Unlike the
discharged Externals in the Divisible-Sandpile-Percolation repository,
`Exploding.External.FeyMeesterRedigLeastAction` is an opaque `Prop` with no `...Proved` discharge
in this tree.

Smallest reproducer:
```
$ grep -n 'hFMR' Exploding/Frozen/Counterexample.lean
27:as the explicit hypothesis `hFMR`. -/
30:    (hFMR : Exploding.External.FeyMeesterRedigLeastAction) :
40:  have _ := hFMR
$ grep -n 'ce_limsup\|ce_liminf\|ce_slow\|ce_explosive' Exploding/Frozen/Counterexample.lean
41:  refine ⟨ceEta d, ce_explosive d hd, ce_not_ge d hd, hFin, ?_, ?_⟩
42:  · exact ce_limsup d hd (ce_slow d hd hSlow2D hFin) hBdd
43:  · exact ce_liminf d hd hFin
```
(no argument in the construction takes `hFMR`).

Note: the paper's separate clause "fail to have a limit shape / the first arrival times do not
converge" (`:1352-1353`) is implied by the two frozen displays `limsup ≥ 3/2` and `liminf = 1`,
so its absence as a separate conjunct is not a defect.

### C1. `prop-box-crossing` — paper covers all dimensions, Lean requires `d ≥ 2`

Paper (`exploding.tex:1986-1988`):
```
1986: \begin{prop}
1987:   In all dimensions, $\mathbf{P}$ is box-crossing
1988: \end{prop}
```
and the proof's first line (`:1990`) is `The claim is immediate in dimension one.` The frozen
binder (`Exploding/Frozen/BoxCrossing.lean:22`) is
```
theorem Exploding.Frozen.box_crossing (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
```
and the provider `Exploding/Support/BCProofMain.lean:347` has the same `hd : 2 ≤ d`. The `d = 1`
case is therefore not formalized. This is a strict weakening of the paper's proposition; the
missing case is trivial (with `P(η ≥ 1) = 1` every box crosses), so it is a fidelity gap rather
than a mathematical error.

Smallest reproducer:
```
$ awk 'NR>=1986 && NR<=1990 {printf "%d: %s\n", NR, $0}' paper/exploding.tex
1986: \begin{prop}
1987:   In all dimensions, $\mathbf{P}$ is box-crossing
1988: \end{prop}
1989: \begin{proof}
1990:   The claim is immediate in dimension one.
$ grep -n 'theorem Exploding.Frozen.box_crossing' Exploding/Frozen/BoxCrossing.lean
22:theorem Exploding.Frozen.box_crossing (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) ...
```

## Non-vacuity

* `thm-counterexample` is non-vacuous and the witness is explicit: `ceEta d`, with `ce_explosive`,
  `ce_not_ge`, `ce_limsup`, `ce_liminf`, `ce_arrival_finite_of_low` all proved unconditionally in
  the support tree (the conclusion `∃η, …` holds even ignoring `hFMR`).
* `prop-box-crossing` is non-vacuous: `ν := δ_{2d-1}` satisfies `hlow` and `hhit`; `hSch` is a
  registered External `Prop`.
* `lem-last-wave-bound` and `prop-dimensional-reduction` have concrete instantiations
  (`faceLow`/`cons`), and `prop-dimensional-reduction` additionally has `redOdo_agree` proved.
* `thm-generalized-convergence` and `prop-explosion-criteria` are hypotheses-satisfiability
  conditional: their hypotheses are the Section 5 setup plus the registered Externals. I did not
  find, in the repo, a single concrete background `η`/`P` exhibited as simultaneously satisfying
  `h1`, `h3`, `h4`, `h5` and the four Externals (or `hrec` and the externals), and because the
  Externals are opaque `Prop`s their truth is not machine-established here. This does not make the
  theorems vacuous in the formal system (the hypothesis types are nonempty `Prop`s and the proofs
  are function-valued), but it is a non-vacuity obligation not discharged by a witness in this batch.

## What I could not verify

* The frozen blocks at the brief's pin `326a151`; I audited the current tree `9c6fedd` (blocks and
  hashes are internally consistent, but they may have advanced).
* Satisfaction of the registered External `Prop`s (`hLSS`, `hLSSB`, `hHole`, `hChem`, `hSch`,
  `hFMR`): they are cited inputs, not proved here.
* A concrete background satisfying all of `h1`–`h5` for `thm-generalized-convergence`, or
  `h1,h2,hrec` for `prop-explosion-criteria`.

## Conclusion

Batch C cannot be promoted as-is: `thm-counterexample` carries an unused registered External
(`hFMR`) that is EXCESS per the brief, and `prop-box-crossing` is strictly weaker than the
paper's all-dimensions statement (it omits `d = 1`); `thm-generalized-convergence`,
`prop-explosion-criteria`, `lem-last-wave-bound` and `prop-dimensional-reduction` pass on
statement, proof, closure and non-vacuity grounds (the first two conditional on their registered
Externals). At report time all six are in any case already marked `PROVED`.
