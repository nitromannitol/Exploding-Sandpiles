/-
The stable branch of the arithmetic step of Section 4 of `paper/exploding.tex`.
-/
import Exploding.Support.SubArith

set_option linter.unusedVariables false

namespace Exploding

variable {d : ℕ}

/-- The stable branch of `ediv_step_ge`: when the frozen site is stable the
frozen odometer does not move. -/
theorem ediv_step_ge_neg (d : ℕ) (hd : 1 ≤ d) (A B w : ℤ) (hBA : B ≤ A)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hA : A ≤ 4 * (d : ℤ) - 1)
    (h : ¬ 2 * (d : ℤ) ≤ A - 2 * (d : ℤ) * w) :
    B / (2 * (d : ℤ)) ≤ w := by
  have hd' : (0 : ℤ) < 2 * (d : ℤ) := by omega
  rw [Int.ediv_le_iff_le_mul hd']
  simp only [not_le] at h
  nlinarith [hBA, hA, hw0, hw1, h, hd']

end Exploding
