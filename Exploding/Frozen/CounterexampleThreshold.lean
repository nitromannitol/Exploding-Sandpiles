import Exploding.Support.Vocab

/-!
# Counterexample threshold

The first positive added mass for which an explosive background fails to stabilize.
-/

open Exploding LatticeProb

/-- The source minimum on the carrier of explosive backgrounds.
The carrier supplies nonemptiness of the defining set. -/
-- FROZEN-STATEMENT-BEGIN
noncomputable def Exploding.counterexampleThreshold {d : ℕ}
    (η : Site d → ℤ) (_hη : Explosive η) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧
    ¬ Stabilizable (fun x => η x + n * dirac (0 : Site d) x)}
-- FROZEN-STATEMENT-END
