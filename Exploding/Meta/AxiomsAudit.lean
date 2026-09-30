import Exploding.MainTheorems

/-!
# Axioms audit

Building this module prints the axiom dependencies of the six proved results restated in
`Exploding/MainTheorems.lean`.  Each must report exactly the three standard foundational
axioms of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

None of the paper's main results is proved yet, so none is printed here: the frozen
statements of Theorems 1.2, 1.3, 1.4, 5.1 and 6.1 still depend on `sorryAx`.
`python3 tools/check_axioms.py` prints the axiom closure of every registered statement,
open ones included.

No `axiom` is declared in this development.  The cited results are stated as propositions
in `Exploding/External/` and taken as explicit hypotheses by the theorems that use them;
none of the six theorems below uses any of them (see `ASSUMPTIONS.md`).

This file is not imported by the library root; the report runs when it is built explicitly
(`lake build Exploding.Meta.AxiomsAudit`).
-/

#print axioms Exploding.square_lower_bound
#print axioms Exploding.last_wave_bound
#print axioms Exploding.approx_subadditivity
#print axioms Exploding.dimensional_reduction
#print axioms Exploding.recurrence
#print axioms Exploding.crossing_time
