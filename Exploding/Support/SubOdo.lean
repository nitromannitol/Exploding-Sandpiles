/-
The elementary API of the bootstrap odometer `spanOdo` and of the constrained
odometer `redOdoUp` of the reduction: both are nonnegative, bounded by one on
the sites that matter, monotone in time, and absorbing at one.  These are the
facts the layer induction of Proposition 7.5 consumes.
-/
import Exploding.Support.SubSpanBridge
import Exploding.Support.SubLayer

namespace Exploding

open LatticeProb

open scoped Classical

variable {d : ℕ}

/-- The one-step unfolding of the bootstrap odometer. -/
theorem spanOdo_succ_eq (n : ℕ) (η : Site d → ℤ) (t : ℕ) (x : Site d) :
    spanOdo n η (t + 1) x =
      (if x ∉ cube d n then 0
       else if spanOdo n η t x = 1 then 1
       else spanOdo n η t x +
         (if 2 * (d : ℤ) ≤ η x + lap (spanOdo n η t) x then 1 else 0)) := rfl

/-- The bootstrap odometer is nonnegative. -/
theorem spanOdo_nonneg (n : ℕ) (η : Site d → ℤ) : ∀ t x, 0 ≤ spanOdo n η t x := by
  intro t
  induction t with
  | zero => intro x; exact le_rfl
  | succ t ih =>
    intro x
    rw [spanOdo_succ_eq]
    have h := ih x
    split_ifs <;> omega

/-- The bootstrap odometer is at most one. -/
theorem spanOdo_le_one (n : ℕ) (η : Site d → ℤ) : ∀ t x, spanOdo n η t x ≤ 1 := by
  intro t
  induction t with
  | zero => intro x; exact zero_le_one
  | succ t ih =>
    intro x
    rw [spanOdo_succ_eq]
    have h := ih x
    split_ifs <;> omega

/-- Once the bootstrap odometer is one at a site it stays one. -/
theorem spanOdo_one_stays (n : ℕ) (η : Site d → ℤ) (t : ℕ) (x : Site d)
    (h : spanOdo n η t x = 1) : spanOdo n η (t + 1) x = 1 := by
  rw [spanOdo_succ_eq]
  by_cases hx : x ∉ cube d n
  · rw [if_pos hx]
    rw [spanOdo_of_notMem n η t hx] at h
    exact h
  · rw [if_neg hx, if_pos h]

/-- The bootstrap odometer is monotone in time. -/
theorem spanOdo_mono (n : ℕ) (η : Site d → ℤ) :
    ∀ t x, spanOdo n η t x ≤ spanOdo n η (t + 1) x := by
  intro t x
  have hle := spanOdo_le_one n η t x
  have hnn := spanOdo_nonneg n η (t + 1) x
  rcases eq_or_ne (spanOdo n η t x) 1 with h1 | h1
  · rw [spanOdo_one_stays n η t x h1]; omega
  · omega

end Exploding
