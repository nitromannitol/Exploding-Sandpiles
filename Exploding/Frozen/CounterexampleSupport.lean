import Exploding.Frozen.CounterexamplePile

/-!
# Counterexample support

The rescaled support of the counterexample pile under nearest-site interpolation.
-/

open Exploding LatticeProb

/-- The positive-odometer set under the nearest-site convention. -/
-- FROZEN-STATEMENT-BEGIN
noncomputable def Exploding.counterexampleSupport {d : ℕ}
    (η : Site d → ℤ) (hη : Explosive η) (t : ℕ) : Set (Fin d → ℝ) :=
  {y | 0 < podo (counterexamplePile η hη) t
    (nearestSite ((t : ℝ) • y))}
-- FROZEN-STATEMENT-END
