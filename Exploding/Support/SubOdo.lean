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

/-- `redOdoUp` is nonnegative. -/
theorem redOdoUp_nonneg (n : ℕ) (η : Site (d + 1) → ℤ) : ∀ t x, 0 ≤ redOdoUp n η t x := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [redOdoUp_zero]
    split_ifs <;> omega
  | succ t ih =>
    intro x
    rw [redOdoUp_succ]
    have h := ih x
    split_ifs <;> omega

/-- `redOdoUp` is at most one. -/
theorem redOdoUp_le_one (n : ℕ) (η : Site (d + 1) → ℤ) : ∀ t x, redOdoUp n η t x ≤ 1 := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [redOdoUp_zero]
    split_ifs <;> omega
  | succ t ih =>
    intro x
    rw [redOdoUp_succ]
    have h := ih x
    split_ifs <;> omega

/-- Once `redOdoUp` is one at a site it stays one. -/
theorem redOdoUp_one_stays (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (x : Site (d + 1))
    (h : redOdoUp n η t x = 1) : redOdoUp n η (t + 1) x = 1 := by
  rw [redOdoUp_succ]
  by_cases hx : x ∉ cube (d + 1) n
  · rw [if_pos hx]; exact h
  · rw [if_neg hx]
    by_cases h1 : 1 < x 0
    · rw [if_pos h1]; exact h
    · rw [if_neg h1]
      rw [if_pos h]
      exact h

/-- `redOdoUp` is monotone in time. -/
theorem redOdoUp_mono (n : ℕ) (η : Site (d + 1) → ℤ) :
    ∀ t x, redOdoUp n η t x ≤ redOdoUp n η (t + 1) x := by
  intro t x
  have hle := redOdoUp_le_one n η t x
  have hnn := redOdoUp_nonneg n η (t + 1) x
  rcases eq_or_ne (redOdoUp n η t x) 1 with h1 | h1
  · rw [redOdoUp_one_stays n η t x h1]; omega
  · omega

/-- The `(d+1)`-dimensional constrained odometer at layer `1` equals the `d`-dimensional
bootstrap odometer of the shifted background. -/
theorem redOdoUp_cons_one_eq_spanOdo (hd : 1 ≤ d) (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ)
    (y : Site d) :
    redOdoUp n η t (cons 1 y) = spanOdo n (fun w => η (cons 1 w) - 1) t y := by
  rw [redOdo_agree (d := d) hd t y]
  exact redOdoDown_eq_spanOdo n η t y

end Exploding
