# Promotion of the 22 Exploding SEALED nodes to PROVED (2026-10-04)

Independent evidence, all committed:
* `2026-10-03-refute-first-A.md` — batch A (`thm-limit-shape`, `thm-time-constant`,
  `thm-explosive`, `prop-renormalization`, `lem-square-lower-bound`): no refutation.
* `2026-10-03-refute-first-B.md` — batch B (`lem-penultimate-cluster`,
  `lem-penultimate-upper-bound`, `lem-penultimate-close`, `prop-last-wave-convergence`,
  `prop-approximate-subadditive`, `prop-generalized-last-wave`): no refutation.
* `2026-10-03-script-audit-triage.md` and `~/fleet/runs/exploding-sandpiles-audit/` — the systematic
  audit of all 22 nodes (58 lenses): no proof error; every transcription flag is a registered
  `Exploding.External.*` binder, the model's own range (`toyLaw` support `{2d-2, 2d-1}`), or a benign
  explicit rendering. Vacuity lens: none.
* `2026-10-04-gates-repaired.md` — the two vacuous gates are repaired.

Recorded caveats (frozen statements, not self-edited): `lem-finite-exploding` asserts the existence
half of the paper's last-wave lemma but not `\hat M_η(0) < ∞` (printed by `check_clauses` as
`FLAGGED`, tracked for the owner); `thm-time-constant` makes the `Explosive ∧ all arrival times
finite` content explicit inside the a.s. event. Every node's axiom closure is exactly
`propext, Classical.choice, Quot.sound`. `python3 tools/verify.py`: all checks passed.
