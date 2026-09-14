/-
The unstable branch of the arithmetic step of Section 4 of `paper/exploding.tex`.
-/
import Exploding.Support.SubArith

set_option linter.unusedVariables false

namespace Exploding

variable {d : ℕ}

/-- The unstable branch of `ediv_step_ge`: when the frozen site is unstable the
frozen odometer gains a full unit. -/
theorem ediv_step_ge_pos (d : ℕ) (hd : 1 ≤ d) (A B w : ℤ) (hBA : B ≤ A)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hA : A ≤ 4 * (d : ℤ) - 1)
    (h : 2 * (d : ℤ) ≤ A - 2 * (d : ℤ) * w) :
    B / (2 * (d : ℤ)) ≤ w + 1 := by
  have hd' : (0 : ℤ) < 2 * (d : ℤ) := by omega
  rw [Int.ediv_le_iff_le_mul hd']
  nlinarith [hBA, hA, hw0, hw1, h, hd']

end Exploding
