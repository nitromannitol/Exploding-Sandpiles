# Gate repair — `check_clauses.py` and `check_exponents.py` (vacuous `rotor.tex` stem)

* **Repository:** `~/lean/Exploding-Sandpiles`
* **Paper:** `paper/exploding.tex`, sha256 `1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44` (matches `ledger/manifest.yaml:source_pin`).
* **Constraints observed:** no `git`, no `lake build`/`update`/`clean`, no frozen `Exploding/Frozen/**`, `Exploding/External/**` or `Exploding/Support/**` statement touched. Only `tools/check_clauses.py`, `tools/check_exponents.py` and this report were written.

## Defect

Both gates selected nodes with the stale regex `r"rotor\.tex:(\d+)-(\d+)"`, but this manifest writes `source: exploding.tex:<range>`. Both matched nothing and returned `OK (0 statements)`, while `tools/verify.py` reported them green. `check_clauses.REVIEWED` was empty and `check_exponents.EXPECTED_ABSENT` had no Exploding entries.

## Step 1 — `tools/check_exponents.py`

Replaced the literal stem (line 126) with the paper-derived one:

```python
rng = re.search(rf"{re.escape(paper_path().name)}:(\d+)-(\d+)", node["source"])
```

First run after the regex fix listed every paper exponent without a Lean counterpart. Each was a genuine notation reason (not a mismatch), so a one-line reason was added to `EXPECTED_ABSENT`:

* `d` / `(d)` / `(d-1)` / `(i)` / `(i+1)` / `(z)` / `(i,z)` — dimension, box, path or label superscripts that are not exponents of a quantity (`\Z^d`, `\R^d`, `Q_n^{(d)}`, `z^{(i)}`, `u_t^{(z)}`, `\mathfrak{C}_k^{(i,z)}`).
* `\gamma` — notation: the paper writes `\gamma`, Lean writes `γ`.
* `dn` — notation: the paper's `(2d)^{d n}` is Lean's `(2*d)^(d*n)`.
* `c` in `prop-renormalization` — set-complement superscript in `\mathcal{C}_\infty^c`.
* `d` in `prop-crossing-time` — the exponent `k^d` is carried by the definition `GoodCube` (`GoodCube η k ≜ max crossing time ≤ k^d`), not repeated in the frozen block.

No unexplained paper exponent and no real mismatch remains.

```
$ python3 tools/check_exponents.py
...
check_exponents: OK (26 statements; every paper exponent appears in its Lean statement or is explained above)
```

## Step 2 — `tools/check_clauses.py`

Applied the same regex fix (line 113), then populated `REVIEWED` with one recorded correspondence per node (22 nodes with a paper label). The lines state what the paper displays and how the Lean conjuncts carry them; the extra conjuncts of several statements are the paper's standing hypotheses (`hlow`/`hhigh`), explicit finiteness witnesses guarding `ℕ∞` junk values (`∃ m`, `∃ a b`, `∃ n`), registered `External` inputs, or a two-sided display collapsed into one conjunct.

The hand triage (`ledger/audits/2026-10-03-script-audit-triage.md`) records one genuine partial transcription the count heuristic cannot see: `lem-finite-exploding` asserts the existence of a non-stabilising wave but not the paper's `\hat M_\eta(0) < \infty`. That node is entered in the module-level `FLAGGED` set (printed like an automatic flag, does not fail the check); no other node is flagged by hand.

```
$ python3 tools/check_clauses.py
node                       label                  paper  lean
  thm-limit-shape          theorem:limit_shape        1     4
  thm-time-constant        theorem:convergence_of_time_constant     0     1
  thm-explosive            theorem:explosive          0     1
  prop-renormalization     prop:renormalization_properties     5     3  <-- paper asserts more
  lem-square-lower-bound   lemma:square_lower_bound     0     1
  lem-penultimate-cluster  lemma:last_penultimate_cluster     1     1
  lem-penultimate-upper-bound lemma:penultimate_upper_bound     1     2
  lem-penultimate-close    lemma:last_penultimate_close     2     3
  prop-last-wave-convergence prop:convergence_of_the_last_wave     1     1
  prop-approximate-subadditive prop:approximate_subadditive     2     2
  prop-generalized-last-wave prop:convergence_of_the_generalized_last_wave     0     1
  thm-counterexample       theorem:counterexample     2     5
  prop-explosion-criteria  prop:explosion_criteria     0     1
  ext-fey-levine-peres     prop:fey_levine_peres_explode     0     1
  ext-schonmann-bootstrap  prop:schonnmann_bootstrap     2     1  <-- paper asserts more
  lem-last-wave-bound      lemma:last_wave_bound      1     1
  prop-dimensional-reduction prop:dimensional_reduction     3     2  <-- paper asserts more
  lem-approx-subadditivity lemma:approx_subadditivity     1     1
  prop-recurrence          prop:recurrence            0     1
  lem-local-convexity      lemma:local_convexity      0     1
  lem-finite-exploding     lemma:finite_exploding     0     2  <-- paper asserts more
  prop-crossing-time       prop:crossing_time         1     2

Recorded correspondence, one line per statement:
  ... (22 lines; full text in tools/check_clauses.py REVIEWED)

check_clauses: OK (22 statements, each read against the paper and its correspondence recorded; 4 where the paper is recorded as asserting more, all explained above)
```

The four printed flags are `prop-renormalization` and `ext-schonmann-bootstrap` and `prop-dimensional-reduction` (count artifacts: a two-sided display or a definitional `:=` counted as an extra relation) and `lem-finite-exploding` (the hand flag above). All four are explained in their `REVIEWED` lines.

## Step 3 — full gate suite

```
$ cd ~/lean/Exploding-Sandpiles && export PATH=$HOME/.elan/bin:$PATH
$ python3 tools/verify.py
check_manifest: OK (29 nodes, 0 unsealed; closure 29 checked, 0 skipped; 460 Exploding declarations indexed)
...
check_clauses: OK (22 statements, each read against the paper and its correspondence recorded; 4 where the paper is recorded as asserting more, all explained above)
...
check_exponents: OK (26 statements; every paper exponent appears in its Lean statement or is explained above)
...
check_warnings: OK (0 registered sorry warnings)
verify: axiom closures agree with the manifest (29 clean, 0 open or resting on open nodes)

verify: all checks passed
```

Neither gate is vacuous any more: `check_exponents` inspects 26 statements and `check_clauses` inspects 22. `tools/verify.py` passes all checks.

## Files changed

* `tools/check_exponents.py` — paper-derived regex; `EXPECTED_ABSENT` entries for every Exploding node.
* `tools/check_clauses.py` — paper-derived regex; `REVIEWED` for all 22 paper-bearing nodes; module-level `FLAGGED` set merged into the printed flags.

Nothing under `Exploding/Frozen/`, `Exploding/External/` or `Exploding/Support/` was modified; no manifest entry, frozen hash or statement byte was changed.
