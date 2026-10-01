import Exploding.MainTheorems

/-!
# Axioms audit

Building this module prints the axiom dependencies of the fifteen proved results restated
in `Exploding/MainTheorems.lean`.  Each must report exactly the three standard foundational
axioms of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

Of the paper's main results, Theorem 1.4 is proved and appears among them; Theorems 1.2,
1.3, 5.1 and 6.1 are still open, so their frozen statements still depend on `sorryAx` and
are not printed here.  `python3 tools/check_axioms.py` prints the axiom closure of every
registered statement, open ones included.

No `axiom` is declared in this development.  The cited results are stated as propositions
in `Exploding/External/` and taken as explicit hypotheses by the theorems that use them;
none of the fifteen theorems below uses any of them (see `ASSUMPTIONS.md`).

This file is not imported by the library root; the report runs when it is built explicitly
(`lake build Exploding.Meta.AxiomsAudit`).
-/

#print axioms Exploding.square_lower_bound
#print axioms Exploding.last_wave_bound
#print axioms Exploding.approx_subadditivity
#print axioms Exploding.dimensional_reduction
#print axioms Exploding.recurrence
#print axioms Exploding.crossing_time
#print axioms Exploding.local_convexity
#print axioms Exploding.renormalization_properties
#print axioms Exploding.finite_exploding
#print axioms Exploding.last_penultimate_cluster
#print axioms Exploding.penultimate_upper_bound
#print axioms Exploding.last_penultimate_close
#print axioms Exploding.explosive
#print axioms Exploding.explosion_criteria
#print axioms Exploding.box_crossing
