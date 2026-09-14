/-
The bootstrap-percolation odometer vanishes off its cube, the first ingredient
of the coupling used in the proof of Proposition 7.5.
-/
import Exploding.Support.Hypotheses

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- Off the cube the bootstrap odometer is zero. -/
theorem spanOdo_of_notMem (n : ℕ) (η : Site d → ℤ) (t : ℕ) {y : Site d}
    (hy : y ∉ cube d n) : spanOdo n η t y = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [spanOdo, if_pos hy]

end Exploding
