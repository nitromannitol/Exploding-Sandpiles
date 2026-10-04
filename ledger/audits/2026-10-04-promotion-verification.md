# Independent verification — Exploding-Sandpiles full promotion (28 PROVED / 0 SEALED)

* **Auditor:** independent verification pass (this report only; no other file written).
* **Repository:** `~/lean/Exploding-Sandpiles` (working tree as read).
* **Constraints observed:** no `git`, no `lake build`. `tools/verify.py` was run, which internally
  invokes `python3 tools/check_axioms.py` (`lake env lean` on one scratch audit file); that is the
  standard gate and not a `lake build`.
* **Paper pin:** `paper/exploding.tex`, sha256 `1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44` (matches `ledger/manifest.yaml:source_pin`).
* **Scope:** (1) run `tools/verify.py`; (2) confirm the 28/0 tally; (3) confirm
  `check_clauses`/`check_exponents` are non-vacuous; (4) spot-check `lem-finite-exploding` v6 against
  `exploding.tex:720-722` and its axiom closure.

## 1. Gate suite

```
$ cd ~/lean/Exploding-Sandpiles && export PATH=$HOME/.elan/bin:$PATH && python3 tools/verify.py
check_manifest: OK (35 nodes, 0 unsealed; closure 35 checked, 0 skipped; 469 Exploding declarations indexed)
check_coverage: 24 statements in the paper, 24 formalized
check_constants: OK (35 statements; every existential constant is bound before every paper parameter, so it is a genuine constant)
check_clauses: OK (24 statements, each read against the paper and its correspondence recorded; 5 where the paper is recorded as asserting more, all explained above)
check_exponents: OK (30 statements; every paper exponent appears in its Lean statement or is explained above)
paper_anchors: OK (24 anchors resolved, 11 nodes carry no paper label)
paper_citations: 20 correct, 0 stale, 59 not anchored to a label, 0 unresolvable
sync_docs: OK (35 nodes; README.md and CORRESPONDENCE.md agree with the manifest)
check_warnings: OK (0 registered sorry warnings)
check_axioms: 35 clean, 0 depend on sorryAx, 0 unresolved
verify: axiom closures agree with the manifest (35 clean, 0 open or resting on open nodes)
verify: all checks passed
```
Exit code 0. **PASS.**

## 2. Manifest tally

Parsed `ledger/manifest.yaml` directly (`grep -c 'state: …'`):

| state | count |
|---|---|
| `PROVED` | **28** |
| `SEALED` | **0** |
| `FROZEN` | 7 |
| `DRAFT_SORRY` | 0 |
| `CONDITIONAL` | 0 |
| total `- id:` entries | 35 |

* The 28 `PROVED` are the 22 theorem nodes already audited in batches A–D plus the 6 new in-repo
  discharges `ext-fey-levine-peres-proved`, `ext-schonmann-bootstrap-proved`,
  `ext-liggett-schonmann-stacey-proved`, `ext-lss-bounded-degree-proved`,
  `ext-mathieu-holes-proved`, `ext-fey-meester-redig-proved`. Each of the 6 carries a manifest
  `note` naming the discharging Lean declaration and its clean closure.
* The 7 `FROZEN` are the registered `Exploding.External.*` inputs `ext-fey-levine-peres`,
  `ext-schonmann-bootstrap`, `ext-liggett-schonmann-stacey`, `ext-lss-bounded-degree`,
  `ext-antal-pisztora`, `ext-mathieu-holes`, `ext-fey-meester-redig`.
* `ext-antal-pisztora` is the **only** External with no `-proved` counterpart; it remains a carried
  hypothesis (`hChem`) in the conditional nodes, as documented. This is consistent with the 28/0
  tally: the promotion counts theorem nodes and the six discharged externals, not the one unproved
  cited input.

**PASS** (tally matches 28 `PROVED` / 0 `SEALED`).

## 3. `check_clauses` / `check_exponents` non-vacuity

Both gates derive the paper stem from `paper_path().name`; `grep -n rotor tools/check_clauses.py tools/check_exponents.py` returns nothing.

```
$ python3 tools/check_clauses.py
  ... 24 node rows ...
check_clauses: OK (24 statements, each read against the paper and its correspondence recorded; 5 where the paper is recorded as asserting more, all explained above)

$ python3 tools/check_exponents.py
  ... 30 node rows ...
check_exponents: OK (30 statements; every paper exponent appears in its Lean statement or is explained above)
```

`check_clauses` inspects **24** paper-bearing statements with a populated `REVIEWED` line for each
(the count grew from 22 with the two new `-proved` nodes that carry a paper label), and
`check_exponents` inspects **30** statements with `EXPECTED_ABSENT` reasons for every notation-only
superscript. Both counts are non-zero; neither gate is vacuous. The five printed flags are
`prop-renormalization`, `ext-schonmann-bootstrap`, `prop-dimensional-reduction`,
`lem-finite-exploding`, and `ext-schonmann-bootstrap-proved`, all explained in their `REVIEWED`
lines (the last two are count artifacts of the two-sided display / the `η'` cases definition; the
first three are the recorded count-heuristic flags). **PASS (non-vacuous).**

## 4. Spot-check — `lem-finite-exploding` v6

Manifest entry: `version: 6`, `state: PROVED`, `source: exploding.tex:720-722 (label lemma:finite_exploding)`,
`frozen_sha256: 2bdfdb526cdb4146e9765019df878274f2d3d49991244591748bbce579ac9772`,
`closure_sha256: 77673f7e7668fc185b4aa41a865f2abe3a7deca9485e1c58d58353968b2ca7f5`.

Paper `exploding.tex:720-722` (exact):
```
\begin{lemma} \label{lemma:finite_exploding}
	The last-wave is well-defined, $\hat{M}_{\eta}(0) < \infty$.
\end{lemma}
```
Frozen block `Exploding/Frozen/FiniteExploding.lean:27-31` (exact):
```
theorem Exploding.Frozen.finite_exploding (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)
```

* **Integrity.** Recomputing SHA-256 over the bytes strictly between the markers gives
  `2bdfdb526cdb4146e9765019df878274f2d3d49991244591748bbce579ac9772`, matching the manifest
  (`match=True`); no `axiom`, `admit`, `sorry`, `native_decide` or `set_option` in the block;
  `check_manifest` reports `closure 35 checked, 0 skipped`, so the recorded `closure_sha256`
  matches too.
* **Closure.** `check_axioms` prints `clean lem-finite-exploding`; `check_warnings` replays
  `Exploding/Meta/AxiomsAudit.lean` and prints
  `'Exploding.finite_exploding' depends on axioms: [propext, Classical.choice, Quot.sound]`,
  with `check_warnings: OK (0 registered sorry warnings)`. No `sorryAx`. **Closure is clean.**
* **Statement fidelity.** The frozen conclusion is the existence half. In the library,
  `Exploding.waveThreshold η z : ℕ := sInf {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z}`
  (`Exploding/Support/Toppling.lean:224`) is the paper's `M̂_η(z)`; because its codomain is `ℕ`,
  `M̂_η(0) < ∞` is automatic and the mathematical content of the paper's display is exactly that
  the defining set is non-empty, which is the frozen conclusion (and the file docstring states this
  reading). So under the documented `ℕ`-valued reading the frozen block captures the paper's
  assertion. It is **not** a literal reproduction of the display `M̂_η(0) < ∞`, and
  `check_clauses` still prints `lem-finite-exploding … <-- paper asserts more` with the `REVIEWED`
  line `… not the finiteness of M̂ (flagged: partial transcription, triage)`. This is the same
  partial-transcription concern recorded in `2026-10-03-script-audit-triage.md`,
  `2026-10-03-refute-first-D.md`, and the proposal `2026-10-04-finite-exploding-erratum.md`.
* **Tally discrepancy to note (documentation, not proof).** `2026-10-04-finite-exploding-erratum.md`
  proposed reverting this node to `SEALED` "until a ruling"; the current manifest instead records
  `PROVED` (v6, frozen bytes unchanged). Either the erratum is superseded by a later ruling accepting
  the `ℕ`-valued reading, or it was not applied. No frozen statement was edited, and the proof and
  closure are clean either way; the only open item is the fidelity ruling.

**Verdict:** closure clean and the theorem is proved (PASS); statement fidelity is a **CONCERN**
(documented partial transcription / modelling choice, correctly flagged by `check_clauses` and the
erratum), not a proof defect.

## 5. What I could not verify

* The exact commit id: instructions forbade `git`, so `HEAD` was not read; the verification is of the
  working tree as read (manifest, paper pin and all 35 frozen hashes are self-consistent).
* I did not re-run `lake build` (forbidden). The clean closures come from `check_axioms` /
  `check_warnings`, which compile the audit file with `lake env lean`.
* I did not adjudicate the truth of the one unproved External `ext-antal-pisztora`, nor the
  satisfiability of the Section-5 hypotheses carried by `prop-generalized-last-wave`; the promotion
  records proved conditional theorems, as before.
* I spot-checked `lem-finite-exploding` in detail and re-read the 24 `check_clauses` rows for
  consistency, but did not byte-diff every `REVIEWED` line against the paper.

## 6. Conclusion

The full promotion is **verified as to its machine-checkable content**: `python3 tools/verify.py`
passes; the manifest is exactly **28 `PROVED` / 0 `SEALED` / 7 `FROZEN`**; `check_clauses` (24
statements) and `check_exponents` (30 statements) are non-vacuous; and `lem-finite-exploding` v6 has
a matching frozen hash and a clean axiom closure `[propext, Classical.choice, Quot.sound]` with no
`sorryAx`. The single caveat is fidelity, not soundness: `lem-finite-exploding` reproduces the
paper's `lemma:finite_exploding` content under the `ℕ`-valued `waveThreshold` reading but not its
literal `M̂_η(0) < ∞` display, and both `check_clauses` and the erratum flag it — the outstanding
item is the owner's ruling on that modelling choice, not a promoted proof error.
