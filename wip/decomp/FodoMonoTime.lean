/-
The frozen odometer is monotone in time.  The base case is `fodo_zero`; the step
needs `fconf` monotone in `t`, which follows from `nbrSumZ_mono` applied to the
inductive hypothesis.  The remaining arithmetic is the last `linarith` below:
the goal has `- 2*d*v` on both sides, so the two monotonicity facts
(`nbrSumZ` and `fodo` itself) must be combined with `d ≥ 0` in the right
orientation.
-/
import Exploding.Support.ReductionShift
open Exploding LatticeProb MeasureTheory
open scoped Classical
variable {d : ℕ}

/-- The frozen odometer never decreases in time. -/
theorem fodo_mono_time (S : Set (Site d)) (s0 w0 : Site d → ℤ) :
    ∀ t x, fodo S s0 w0 t x ≤ fodo S s0 w0 (t + 1) x := by
  intro t
  induction t with
  | zero =>
    intro x
    show fodo S s0 w0 0 x ≤ fodo S s0 w0 (0 + 1) x
    rw [fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx]
      exact le_of_eq rfl
    · rw [if_neg hx]
      split_ifs <;> omega
  | succ t ih =>
    intro x
    have h := ih x
    rw [fodo_succ, fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx]
      have hconf : fconf S s0 w0 t x ≤ fconf S s0 w0 (t + 1) x := by
        simp only [fconf, lap]
        have h1 : nbrSumZ (fodo S s0 w0 t) x ≤ nbrSumZ (fodo S s0 w0 (t + 1)) x :=
          nbrSumZ_mono (fun y => ih y) x
        have h2 : fodo S s0 w0 t x ≤ fodo S s0 w0 (t + 1) x := ih x
        have hd0 : (0 : ℤ) ≤ (d : ℤ) := by positivity
        have h3 : 2 * (d : ℤ) * fodo S s0 w0 t x ≤ 2 * (d : ℤ) * fodo S s0 w0 (t + 1) x :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        linarith [h1, h3]
      by_cases hc : 2 * (d : ℤ) ≤ fconf S s0 w0 t x
      · rw [if_pos hc]
        by_cases hc' : 2 * (d : ℤ) ≤ fconf S s0 w0 (t + 1) x
        · rw [if_pos hc']; omega
        · rw [if_neg hc']; omega
      · rw [if_neg hc]
        by_cases hc' : 2 * (d : ℤ) ≤ fconf S s0 w0 (t + 1) x
        · rw [if_pos hc']; omega
        · rw [if_neg hc']; omega
