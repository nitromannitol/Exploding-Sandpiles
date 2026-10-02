/-
Geometry of the growth schedule: the box at time `0` is the starting box, the boxes increase
inside the target and equal the target at the final time, the layers added lie inside the
target and away from the starting box, and the side of the box is the side of the schedule.
-/
import Exploding.Support.ExtSchSched

namespace Exploding

open LatticeProb

variable {d : ℕ}

section Geom
variable (P : xss_Plan d) {s : ℕ}

/-- The quotient and the remainder by a positive number after one more step: either the remainder
increases by one, or the quotient increases by one and the remainder returns to `0`. -/
theorem xsg_succ_divmod {k : ℕ} (hk : 0 < k) (t : ℕ) :
    ((t + 1) / k = t / k ∧ (t + 1) % k = t % k + 1) ∨
      ((t + 1) / k = t / k + 1 ∧ (t + 1) % k = 0 ∧ t % k + 1 = k) := by
  have hm : t % k < k := Nat.mod_lt t hk
  have ht : k * (t / k) + t % k = t := Nat.div_add_mod t k
  rcases Nat.lt_or_ge (t % k + 1) k with h | h
  · left
    exact (Nat.div_mod_unique hk).2 ⟨by omega, h⟩
  · right
    have hk1 : t % k + 1 = k := by omega
    have hmul : k * (t / k + 1) = k * (t / k) + k := Nat.mul_succ k (t / k)
    have hu : (t + 1) / k = t / k + 1 ∧ (t + 1) % k = 0 :=
      (Nat.div_mod_unique hk).2 ⟨by omega, hk⟩
    exact ⟨hu.1, hu.2, hk1⟩

/-- The side of the schedule is at most the side of the target box. -/
theorem xsg_side_le (hP : xss_Valid P s) (t : ℕ) (j : Fin d) :
    xss_side P t j ≤ xss_len P.LO P.HI j := by
  unfold xss_side
  by_cases hj : j ∈ P.J
  · rw [if_pos hj]
    exact min_le_left _ _
  · rw [if_neg hj]
    have h := hP.2.2.2.1 j
    unfold xss_len
    omega

/-- The side of the schedule is at least the side of the starting box. -/
theorem xsg_len_le_side (hP : xss_Valid P s) (t : ℕ) (j : Fin d) :
    xss_len P.lo0 P.hi0 j ≤ xss_side P t j := by
  unfold xss_side
  by_cases hj : j ∈ P.J
  · rw [if_pos hj]
    have h := hP.2.2.2.1 j
    unfold xss_len
    omega
  · rw [if_neg hj]

/-- The side of the schedule does not decrease with time. -/
theorem xsg_side_succ (hP : xss_Valid P s) (t : ℕ) (j : Fin d) :
    xss_side P t j ≤ xss_side P (t + 1) j := by
  unfold xss_side
  by_cases hj : j ∈ P.J
  · rw [if_pos hj, if_pos hj]
    have hk : 0 < P.J.card := Finset.card_pos.mpr hP.1
    rcases xsg_succ_divmod hk t with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2]
      split_ifs <;> omega
    · rw [h1, h2]
      split_ifs <;> push_cast <;> omega
  · rw [if_neg hj, if_neg hj]

/-- The growth in each direction does not decrease with time. -/
theorem xsg_grown_succ (hP : xss_Valid P s) (t : ℕ) (j : Fin d) :
    xss_grown P t j ≤ xss_grown P (t + 1) j := by
  have h := xsg_side_succ P hP t j
  unfold xss_grown
  omega

/-- Nothing has grown at time `0`. -/
theorem xsg_grown_zero (hP : xss_Valid P s) (j : Fin d) : xss_grown P 0 j = 0 := by
  unfold xss_grown xss_side
  by_cases hj : j ∈ P.J
  · rw [if_pos hj]
    have h1 := hP.2.2.1.1 j hj
    have h2 := hP.2.2.2.1 j
    simp only [Nat.zero_div, Nat.zero_mod, Nat.not_lt_zero, if_false, Nat.cast_zero, add_zero]
    unfold xss_len
    omega
  · rw [if_neg hj]
    omega

/-- The side of the schedule at the last time is the side of the target box. -/
theorem xsg_side_final (hP : xss_Valid P s) (j : Fin d) :
    xss_side P (xss_steps P s) j = xss_len P.LO P.HI j := by
  have hk : 0 < P.J.card := Finset.card_pos.mpr hP.1
  have h1 : xss_steps P s / P.J.card = s - P.L + 1 := Nat.mul_div_cancel _ hk
  have h2 : xss_steps P s % P.J.card = 0 := Nat.mul_mod_left _ _
  have hLs : P.L ≤ s := hP.2.2.2.2
  unfold xss_side
  by_cases hj : j ∈ P.J
  · rw [if_pos hj, h1, h2]
    have h3 := hP.2.1.1 j hj
    simp only [Nat.not_lt_zero, if_false, add_zero]
    unfold xss_len at h3 ⊢
    push_cast [Nat.cast_sub hLs]
    omega
  · rw [if_neg hj]
    have h3 := hP.2.2.1.2 j hj
    have h4 := hP.2.1.2 j hj
    have h5 := hP.2.2.2.1 j
    unfold xss_len
    omega

/-- The side of the box after `t` steps is the side of the schedule. -/
theorem xss_len_box (t : ℕ) (j : Fin d) :
    xss_hi P t j - xss_lo P t j + 1 = xss_side P t j := by
  unfold xss_hi xss_lo xss_grown xss_len
  omega

/-- The box at time `0` is the starting box. -/
theorem xss_box_zero (hP : xss_Valid P s) : xss_box P 0 = xsb_box P.lo0 P.hi0 := by
  have hlo : (fun j => xss_lo P 0 j) = P.lo0 := by
    funext j
    have h := hP.2.2.2.1 j
    unfold xss_lo
    rw [xsg_grown_zero P hP j]
    omega
  have hhi : (fun j => xss_hi P 0 j) = P.hi0 := by
    funext j
    have h := hP.2.2.2.1 j
    unfold xss_hi
    rw [xsg_grown_zero P hP j]
    omega
  unfold xss_box
  rw [hlo, hhi]

/-- The corners of the box stay inside the target box. -/
theorem xsg_corners_outer (hP : xss_Valid P s) (t : ℕ) (j : Fin d) :
    P.LO j ≤ xss_lo P t j ∧ xss_hi P t j ≤ P.HI j := by
  have h1 := xsg_side_le P hP t j
  have h2 := hP.2.2.2.1 j
  unfold xss_lo xss_hi xss_grown
  unfold xss_len at h1 ⊢
  omega

/-- The corners of the box are ordered when the starting box is not empty. -/
theorem xsg_corners_le (hP : xss_Valid P s) (hL : 1 ≤ P.L) (t : ℕ) (j : Fin d) :
    P.LO j ≤ xss_lo P t j ∧ xss_lo P t j ≤ xss_hi P t j ∧ xss_hi P t j ≤ P.HI j := by
  have h1 := xsg_corners_outer P hP t j
  have h2 := xss_len_box P t j
  have h3 := xsg_len_le_side P hP t j
  have h4 : 1 ≤ xss_len P.lo0 P.hi0 j := by
    by_cases hj : j ∈ P.J
    · have h5 := hP.2.2.1.1 j hj
      unfold xss_len
      omega
    · have h5 := hP.2.2.1.2 j hj
      unfold xss_len
      omega
  omega

/-- The corners of the box move outward with time. -/
theorem xss_corners_mono (hP : xss_Valid P s) (t : ℕ) (j : Fin d) :
    xss_lo P (t + 1) j ≤ xss_lo P t j ∧ xss_hi P t j ≤ xss_hi P (t + 1) j := by
  have h := xsg_grown_succ P hP t j
  unfold xss_lo xss_hi
  constructor <;> omega

/-- At the last time the box is the target box. -/
theorem xss_box_final (hP : xss_Valid P s) :
    xss_box P (xss_steps P s) = xsb_box P.LO P.HI := by
  have hlo : (fun j => xss_lo P (xss_steps P s) j) = P.LO := by
    funext j
    have h1 := hP.2.2.2.1 j
    unfold xss_lo xss_grown
    rw [xsg_side_final P hP j]
    unfold xss_len
    omega
  have hhi : (fun j => xss_hi P (xss_steps P s) j) = P.HI := by
    funext j
    have h1 := hP.2.2.2.1 j
    unfold xss_hi xss_grown
    rw [xsg_side_final P hP j]
    unfold xss_len
    omega
  unfold xss_box
  rw [hlo, hhi]

/-- The boxes increase with time. -/
theorem xss_box_mono_step (hP : xss_Valid P s) (t : ℕ) : xss_box P t ⊆ xss_box P (t + 1) :=
  xsb_box_mono (fun j => (xss_corners_mono P hP t j).1) fun j => (xss_corners_mono P hP t j).2

/-- Every box of the schedule contains the starting box. -/
theorem xss_box_zero_subset (hP : xss_Valid P s) (t : ℕ) :
    xsb_box P.lo0 P.hi0 ⊆ xss_box P t := by
  induction t with
  | zero => exact (xss_box_zero P hP).symm.subset
  | succ t ih => exact ih.trans (xss_box_mono_step P hP t)

/-- Every layer added lies inside the target box. -/
theorem xss_layer_subset_target (hP : xss_Valid P s) (t : ℕ) :
    xss_layer P t ⊆ xsb_box P.LO P.HI := by
  intro x hx
  have hx' : x ∈ xss_box P (t + 1) \ xss_box P t := hx
  have h : xss_box P (t + 1) ⊆ xsb_box P.LO P.HI :=
    xsb_box_mono (fun j => (xsg_corners_outer P hP (t + 1) j).1)
      fun j => (xsg_corners_outer P hP (t + 1) j).2
  exact h hx'.1

/-- Every layer added is disjoint from the starting box. -/
theorem xss_layer_disjoint_seed (hP : xss_Valid P s) (t : ℕ) :
    Disjoint (xss_layer P t) (xsb_box P.lo0 P.hi0) := by
  rw [Set.disjoint_left]
  intro x hx hxs
  have hx' : x ∈ xss_box P (t + 1) \ xss_box P t := hx
  exact hx'.2 (xss_box_zero_subset P hP t hxs)

end Geom

end Exploding
