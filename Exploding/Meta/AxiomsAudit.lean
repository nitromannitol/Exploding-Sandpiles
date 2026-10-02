import Exploding.MainTheorems
import Exploding.Support.ExtFMR
import Exploding.Support.LSProofAux
import Exploding.Support.ExtLSSCountable
import Exploding.Support.ExtMHHoleVolume
import Exploding.Support.ExtSchFinal
import Exploding.Support.ExtSchFLP

/-!
# Axioms audit

Building this module prints the axiom dependencies of the 22 proved results restated in
`Exploding/MainTheorems.lean`, one for each node registered as `SEALED` in
`ledger/manifest.yaml`.  Each must report exactly the three standard foundational axioms of
Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

All of the paper's main results are proved and appear among them: Theorems 1.2, 1.3, 1.4,
5.1 and 6.1, together with Propositions 2.1, 2.2, 3.1, 4.1, 5.1, 7.1, 7.2, 7.3 and 7.5 and
Lemmas 2.1 and 3.1 to 3.7.  No registered statement is open, so none depends on `sorryAx`.
`python3 tools/check_axioms.py` prints the axiom closure of every registered statement.

No `axiom` is declared in this development.  The seven cited results are stated as
propositions in `Exploding/External/` and taken as explicit hypotheses by the theorems that
use them (see `ASSUMPTIONS.md`), so they never appear as axioms here.  Six of them are
discharged by proofs in the repository, and the last seven lines audit those proofs:
`Exploding.xfmr_proved` proves the least-action principle of Fey, Meester and Redig,
`Exploding.xlse_lss_bounded_degree` and `Exploding.xlse_lss_general` prove the two
domination theorems of Liggett, Schonmann and Stacey, `Exploding.xmf_proved` proves the hole
bound of Mathieu, `Exploding.xsr_schonmann` proves Schonmann's bootstrap bound, and
`Exploding.xsr_flp` derives the theorem of Fey, Levine and Peres (Theorem 1.1) from it by
`Exploding.LSProof.ls_flp_from_explosive`.  Only the chemical distance of Antal and Pisztora
is assumed.

This file is not imported by the library root; the report runs when it is built explicitly
(`lake build Exploding.Meta.AxiomsAudit`).
-/

-- Theorems 1.2, 1.3 and 1.4
#print axioms Exploding.limit_shape
#print axioms Exploding.convergence_of_time_constant
#print axioms Exploding.explosive
-- Section 2
#print axioms Exploding.crossing_time
#print axioms Exploding.renormalization_properties
#print axioms Exploding.local_convexity
-- Section 3
#print axioms Exploding.square_lower_bound
#print axioms Exploding.finite_exploding
#print axioms Exploding.last_wave_bound
#print axioms Exploding.approx_subadditivity
#print axioms Exploding.last_penultimate_cluster
#print axioms Exploding.penultimate_upper_bound
#print axioms Exploding.last_penultimate_close
#print axioms Exploding.convergence_of_the_last_wave
-- Section 4
#print axioms Exploding.approximate_subadditive
-- Section 5
#print axioms Exploding.convergence_of_the_generalized_last_wave
#print axioms Exploding.generalized_convergence
-- Section 6
#print axioms Exploding.counterexample
-- Section 7
#print axioms Exploding.explosion_criteria
#print axioms Exploding.dimensional_reduction
#print axioms Exploding.recurrence
#print axioms Exploding.box_crossing
-- The proofs that discharge six of the cited results
#print axioms Exploding.xfmr_proved
#print axioms Exploding.xlse_lss_bounded_degree
#print axioms Exploding.xlse_lss_general
#print axioms Exploding.xmf_proved
#print axioms Exploding.xsr_schonmann
#print axioms Exploding.xsr_flp
#print axioms Exploding.LSProof.ls_flp_from_explosive
