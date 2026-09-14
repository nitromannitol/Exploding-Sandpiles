/-
The one-step unfolding of the frozen odometer off its frozen set, the first
step of the toppling argument in the proof of Proposition 7.5.
-/
import Exploding.Support.Hypotheses

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- Off the frozen set the frozen odometer takes one parallel-toppling step. -/
theorem fodo_succ_of_notMem (S : Set (Site d)) (s0 w0 : Site d → ℤ) (t : ℕ) {x : Site d}
    (hx : x ∉ S) :
    fodo S s0 w0 (t + 1) x =
      fodo S s0 w0 t x + (if 2 * d ≤ fconf S s0 w0 t x then 1 else 0) := by
  rw [Exploding.fodo_succ, if_neg hx]

end Exploding
