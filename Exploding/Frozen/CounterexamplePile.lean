import Exploding.Frozen.CounterexampleThreshold

/-!
# Counterexample pile

The pile formed by adding the first explosive mass at the origin.
-/

open Exploding LatticeProb

/-- The background after adding its threshold mass at the origin. -/
-- FROZEN-STATEMENT-BEGIN
noncomputable def Exploding.counterexamplePile {d : ℕ}
    (η : Site d → ℤ) (hη : Explosive η) : Site d → ℤ :=
  fun x => η x + (counterexampleThreshold η hη : ℤ) * dirac (0 : Site d) x
-- FROZEN-STATEMENT-END
