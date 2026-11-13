/-
The coupling between the reduced constrained odometer of Proposition 7.2 and
bootstrap percolation, used in the proof of Proposition 7.5: the `d`-dimensional
constrained frozen odometer on the background `η(1, ·) - 1` is the bootstrap
percolation odometer of that background.
-/
import Exploding.Support.Reduction
import Exploding.Support.SubSpanZero

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The reduced constrained odometer is the bootstrap odometer of the shifted
background. -/
theorem redOdoDown_eq_spanOdo (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) :
    redOdoDown n η t y = spanOdo n (fun w => η (cons 1 w) - 1) t y := by
  classical
  induction t generalizing y with
  | zero => rfl
  | succ t ih =>
    rw [redOdoDown_succ]
    have hlap : lap (fun w => redOdoDown n η t w) y
        = lap (spanOdo n (fun w => η (cons 1 w) - 1) t) y := by
      simp only [lap]
      rw [nbrSumZ_congr (fun w => ih w) y, ih y]
    rw [hlap, ih y]
    simp only [spanOdo]
    by_cases hy : y ∉ cube d n
    · rw [ite_eq_left hy, ite_eq_left hy]; exact spanOdo_of_notMem n _ t hy
    · rw [ite_eq_right hy, ite_eq_right hy]
      by_cases h1 : spanOdo n (fun w => η (cons 1 w) - 1) t y = 1
      · simp only [ite_eq_left h1]; exact h1
      · rw [ite_eq_right h1, ite_eq_right h1]

end Exploding
