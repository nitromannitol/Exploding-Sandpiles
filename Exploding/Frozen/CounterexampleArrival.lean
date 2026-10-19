import Exploding.Frozen.CounterexamplePile

/-!
# Counterexample arrival time

The first positive time when the odometer of the counterexample pile at a site is positive.
-/

open Exploding LatticeProb

/-- The least positive integer time at which the counterexample pile has toppled at x. -/
-- FROZEN-STATEMENT-BEGIN
noncomputable def Exploding.counterexampleArrival {d : ℕ}
    (η : Site d → ℤ) (hη : Explosive η) (x : Site d) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ 1 ≤ n ∧
    0 < podo (counterexamplePile η hη) n x}
-- FROZEN-STATEMENT-END
