/-
The arithmetic step of the comparison between the frozen odometer and the last
wave in Section 4 of `paper/corrected-arxiv/exploding-corrected-arxiv.tex`: one step of the frozen recursion
dominates one step of the wave recursion when the frozen value is in `{0, 1}`
and the frozen sandpile is at most `4d - 1`.
-/
import Mathlib

set_option linter.unusedVariables false

namespace Exploding

/-- One step of the frozen recursion dominates one step of the wave recursion:
if `B ≤ A`, `0 ≤ w ≤ 1` and `A ≤ 4d - 1`, then
`B / 2d ≤ w + 1{2d ≤ A - 2d·w}`. -/
theorem ediv_step_ge (d : ℕ) (hd : 1 ≤ d) (A B w : ℤ) (hBA : B ≤ A)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hA : A ≤ 4 * (d : ℤ) - 1) :
    B / (2 * (d : ℤ)) ≤ w + (if 2 * (d : ℤ) ≤ A - 2 * (d : ℤ) * w then 1 else 0) := by
  have hd1 : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  by_cases h : 2 * (d : ℤ) ≤ A - 2 * (d : ℤ) * w
  · rw [if_pos h, Int.ediv_le_iff_le_mul hd0]
    nlinarith
  · rw [if_neg h, Int.ediv_le_iff_le_mul hd0]
    nlinarith

end Exploding
