/-
Stacking the two-dimensional schedule of `CELow2` into `ℤ^{n+2}`: the profile `cel_p`,
its legality (`cel_hstep`), and the resulting linear upper bound on the arrival times
of the counterexample background.
-/
import Exploding.Support.CELow2

namespace Exploding

open LatticeProb

variable {n : ℕ}

theorem cel_add_unit_apply (x : Site (n + 2)) (i j : Fin (n + 2)) :
    (x + unit i) j = x j + (if j = i then 1 else 0) := by
  simp [unit, Pi.single_apply]

theorem cel_sub_unit_apply (x : Site (n + 2)) (i j : Fin (n + 2)) :
    (x - unit i) j = x j - (if j = i then 1 else 0) := by
  simp [unit, Pi.single_apply]

theorem cel_ceEta (x : Site (n + 2)) :
    ceEta (n + 2) x = 2 * (n : ℤ) + zeta1 (x 0) (x 1) := by
  unfold ceEta
  have h0 : 0 < n + 2 := by omega
  have h1 : 1 < n + 2 := by omega
  rw [dif_pos h0, dif_pos h1]
  push_cast
  have e0 : (⟨0, h0⟩ : Fin (n + 2)) = 0 := rfl
  have e1 : (⟨1, h1⟩ : Fin (n + 2)) = 1 := rfl
  rw [e0, e1]
  ring

/-! ### The coordinates of the neighbours -/

theorem cel_ne0 (k : Fin n) : k.succ.succ ≠ (0 : Fin (n + 2)) := Fin.succ_ne_zero _

theorem cel_ne1 (k : Fin n) : k.succ.succ ≠ (1 : Fin (n + 2)) := by
  intro h
  have := congrArg Fin.val h
  simp at this


section Nbr

variable (x : Site (n + 2))

theorem cel_a_add0 : (x + unit (0 : Fin (n + 2))) 0 = x 0 + 1 := by rw [cel_add_unit_apply]; simp
theorem cel_b_add0 : (x + unit (0 : Fin (n + 2))) 1 = x 1 := by rw [cel_add_unit_apply]; simp
theorem cel_a_sub0 : (x - unit (0 : Fin (n + 2))) 0 = x 0 - 1 := by rw [cel_sub_unit_apply]; simp
theorem cel_b_sub0 : (x - unit (0 : Fin (n + 2))) 1 = x 1 := by rw [cel_sub_unit_apply]; simp
theorem cel_a_add1 : (x + unit (1 : Fin (n + 2))) 0 = x 0 := by rw [cel_add_unit_apply]; simp
theorem cel_b_add1 : (x + unit (1 : Fin (n + 2))) 1 = x 1 + 1 := by rw [cel_add_unit_apply]; simp
theorem cel_a_sub1 : (x - unit (1 : Fin (n + 2))) 0 = x 0 := by rw [cel_sub_unit_apply]; simp
theorem cel_b_sub1 : (x - unit (1 : Fin (n + 2))) 1 = x 1 - 1 := by rw [cel_sub_unit_apply]; simp
theorem cel_a_addk (k : Fin n) : (x + unit k.succ.succ) 0 = x 0 := by
  rw [cel_add_unit_apply, if_neg (fun h => cel_ne0 k h.symm), add_zero]
theorem cel_b_addk (k : Fin n) : (x + unit k.succ.succ) 1 = x 1 := by
  rw [cel_add_unit_apply, if_neg (fun h => cel_ne1 k h.symm), add_zero]
theorem cel_a_subk (k : Fin n) : (x - unit k.succ.succ) 0 = x 0 := by
  rw [cel_sub_unit_apply, if_neg (fun h => cel_ne0 k h.symm), sub_zero]
theorem cel_b_subk (k : Fin n) : (x - unit k.succ.succ) 1 = x 1 := by
  rw [cel_sub_unit_apply, if_neg (fun h => cel_ne1 k h.symm), sub_zero]

end Nbr

/-- The `ℓ¹`-norm of the coordinates beyond the first two. -/
def cel_rho (x : Site (n + 2)) : ℤ := ∑ k : Fin n, |x k.succ.succ|

theorem cel_rho_nonneg (x : Site (n + 2)) : 0 ≤ cel_rho x :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem cel_rho_eq_zero_iff (x : Site (n + 2)) :
    cel_rho x = 0 ↔ ∀ k : Fin n, x k.succ.succ = 0 := by
  unfold cel_rho
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)]
  simp

theorem cel_rho_add0 (x : Site (n + 2)) : cel_rho (x + unit (0 : Fin (n + 2))) = cel_rho x := by
  unfold cel_rho
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [cel_add_unit_apply, if_neg (cel_ne0 k), add_zero]

theorem cel_rho_sub0 (x : Site (n + 2)) : cel_rho (x - unit (0 : Fin (n + 2))) = cel_rho x := by
  unfold cel_rho
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [cel_sub_unit_apply, if_neg (cel_ne0 k), sub_zero]

theorem cel_rho_add1 (x : Site (n + 2)) : cel_rho (x + unit (1 : Fin (n + 2))) = cel_rho x := by
  unfold cel_rho
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [cel_add_unit_apply, if_neg (cel_ne1 k), add_zero]

theorem cel_rho_sub1 (x : Site (n + 2)) : cel_rho (x - unit (1 : Fin (n + 2))) = cel_rho x := by
  unfold cel_rho
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [cel_sub_unit_apply, if_neg (cel_ne1 k), sub_zero]

theorem cel_rho_addk_of_zero (x : Site (n + 2)) (hr : cel_rho x = 0) (k : Fin n) :
    cel_rho (x + unit k.succ.succ) = 1 := by
  have hx := (cel_rho_eq_zero_iff x).1 hr
  unfold cel_rho
  have h : ∀ j : Fin n, |(x + unit k.succ.succ) j.succ.succ| = if j = k then 1 else 0 := by
    intro j
    rw [cel_add_unit_apply, hx j]
    by_cases hjk : j = k
    · simp [hjk]
    · simp [hjk]
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  simp

theorem cel_rho_subk_of_zero (x : Site (n + 2)) (hr : cel_rho x = 0) (k : Fin n) :
    cel_rho (x - unit k.succ.succ) = 1 := by
  have hx := (cel_rho_eq_zero_iff x).1 hr
  unfold cel_rho
  have h : ∀ j : Fin n, |(x - unit k.succ.succ) j.succ.succ| = if j = k then 1 else 0 := by
    intro j
    rw [cel_sub_unit_apply, hx j]
    by_cases hjk : j = k
    · simp [hjk]
    · simp [hjk]
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  simp

/-- If some coordinate beyond the first two is nonzero, one of the two neighbours in that
direction is closer to the plane. -/
theorem cel_rho_toward (x : Site (n + 2)) (h : 1 ≤ cel_rho x) :
    ∃ k : Fin n, cel_rho (x + unit k.succ.succ) = cel_rho x - 1 ∨
      cel_rho (x - unit k.succ.succ) = cel_rho x - 1 := by
  have hne : ¬ cel_rho x = 0 := by omega
  rw [cel_rho_eq_zero_iff] at hne
  push Not at hne
  obtain ⟨k, hk⟩ := hne
  refine ⟨k, ?_⟩
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · left
    unfold cel_rho
    have hpt : ∀ j : Fin n, |(x + unit k.succ.succ) j.succ.succ|
        = |x j.succ.succ| - (if j = k then 1 else 0) := by
      intro j
      rw [cel_add_unit_apply]
      by_cases hjk : j = k
      · subst hjk
        simp only [if_true]
        rw [abs_of_neg hneg, abs_of_nonpos (by omega)]
        ring
      · simp [hjk]
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib]
    simp
  · right
    unfold cel_rho
    have hpt : ∀ j : Fin n, |(x - unit k.succ.succ) j.succ.succ|
        = |x j.succ.succ| - (if j = k then 1 else 0) := by
      intro j
      rw [cel_sub_unit_apply]
      by_cases hjk : j = k
      · subst hjk
        simp only [if_true]
        rw [abs_of_pos hpos, abs_of_nonneg (by omega)]
      · simp [hjk]
    rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib]
    simp

/-! ### The neighbour sum -/

theorem cel_nbr_split (u : Site (n + 2) → ℤ) (x : Site (n + 2)) :
    nbrSumZ u x = (u (x + unit (0 : Fin (n + 2))) + u (x - unit (0 : Fin (n + 2))))
      + (u (x + unit (1 : Fin (n + 2))) + u (x - unit (1 : Fin (n + 2))))
      + ∑ k : Fin n, (u (x + unit k.succ.succ) + u (x - unit k.succ.succ)) := by
  unfold nbrSumZ
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  ring

theorem cel_single_add {d : ℕ} (u : Site d → ℤ) (hu : ∀ y, 0 ≤ u y) (x : Site d) (i : Fin d) :
    u (x + unit i) ≤ nbrSumZ u x := by
  have h := Finset.single_le_sum
    (f := fun j : Fin d => u (x + unit j) + u (x - unit j))
    (fun j _ => add_nonneg (hu _) (hu _)) (Finset.mem_univ i)
  have h2 := hu (x - unit i)
  simp only [nbrSumZ]
  linarith

theorem cel_single_sub {d : ℕ} (u : Site d → ℤ) (hu : ∀ y, 0 ≤ u y) (x : Site d) (i : Fin d) :
    u (x - unit i) ≤ nbrSumZ u x := by
  have h := Finset.single_le_sum
    (f := fun j : Fin d => u (x + unit j) + u (x - unit j))
    (fun j _ => add_nonneg (hu _) (hu _)) (Finset.mem_univ i)
  have h2 := hu (x + unit i)
  simp only [nbrSumZ]
  linarith

/-- Three distinct neighbours: the two positive neighbours in the first two directions and
one neighbour off the plane. -/
theorem cel_nbr_three (u : Site (n + 2) → ℤ) (hu : ∀ y, 0 ≤ u y) (x : Site (n + 2))
    (k : Fin n) (y : Site (n + 2))
    (hy : y = x + unit k.succ.succ ∨ y = x - unit k.succ.succ) :
    u (x + unit (0 : Fin (n + 2))) + u (x + unit (1 : Fin (n + 2))) + u y ≤ nbrSumZ u x := by
  rw [cel_nbr_split]
  have h0 := hu (x - unit (0 : Fin (n + 2)))
  have h1 := hu (x - unit (1 : Fin (n + 2)))
  have hk : u y ≤ ∑ k : Fin n, (u (x + unit k.succ.succ) + u (x - unit k.succ.succ)) := by
    have h := Finset.single_le_sum
      (f := fun j : Fin n => u (x + unit j.succ.succ) + u (x - unit j.succ.succ))
      (fun j _ => add_nonneg (hu _) (hu _)) (Finset.mem_univ k)
    rcases hy with rfl | rfl
    · have := hu (x - unit k.succ.succ)
      linarith
    · have := hu (x + unit k.succ.succ)
      linarith
  linarith

/-! ### The stacked profile -/

theorem cel_Q_zero (a b : ℤ) : cel_Q 0 a b = 0 := by
  obtain ⟨c1, c2⟩ := cel_chk_all a b
  unfold cel_Q cel_f1 cel_f2
  by_cases hA : cel_in1 a b
  · have h1 := (c1 hA).1
    have e1 : ¬ cel_t1 a b ≤ 0 := by omega
    by_cases hB : cel_in2 a b
    · have h2 := (c2 hB).1
      have e2 : ¬ cel_t2 a b ≤ 0 := by omega
      simp [e1, e2]
    · simp [e1, hB]
  · have hB : ¬ cel_in2 a b := fun hh => hA hh.1
    simp [hA, hB]

theorem cel_val_zero (a b r : ℤ) (hr : 0 ≤ r) : cel_val 0 a b r = 0 := by
  unfold cel_val
  by_cases h0 : r = 0
  · rw [if_pos h0]; exact cel_Q_zero a b
  · rw [if_neg h0]
    by_cases hH : cel_H a b
    · rw [if_pos hH]
      have h1 := (((cel_chk_all a b).1) hH.1).1
      have : ¬ cel_t1 a b + r ≤ 0 := by omega
      simp [this]
    · rw [if_neg hH]
      by_cases hC : a = 0 ∧ b = 0 ∧ r = 1
      · rw [if_pos hC]; norm_num
      · rw [if_neg hC]

/-- The profile: the schedule `cel_val`, evaluated at the first two coordinates and the
`ℓ¹`-norm of the others. -/
def cel_p (t : ℕ) (x : Site (n + 2)) : ℤ := cel_val (t : ℤ) (x 0) (x 1) (cel_rho x)

theorem cel_p_nonneg (t : ℕ) (x : Site (n + 2)) : 0 ≤ cel_p t x :=
  cel_val_nonneg _ _ _ _

theorem cel_p_zero (x : Site (n + 2)) : cel_p 0 x = 0 := by
  unfold cel_p
  rw [Nat.cast_zero]
  exact cel_val_zero _ _ _ (cel_rho_nonneg x)

/-! ### Legality in the plane -/

theorem cel_zero_iff (x : Site (n + 2)) (hr : cel_rho x = 0) :
    x = 0 ↔ (x 0 = 0 ∧ x 1 = 0) := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1⟩
    have hk := (cel_rho_eq_zero_iff x).1 hr
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · simpa using h0
    · simpa using h1
    · simpa using hk k

theorem cel_s0_plane (x : Site (n + 2)) (hr : cel_rho x = 0) :
    ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x = 2 * (n : ℤ) + cel_zh (x 0) (x 1) := by
  rw [cel_ceEta]
  unfold cel_zh dirac
  by_cases h : x 0 = 0 ∧ x 1 = 0
  · have hx : x = 0 := (cel_zero_iff x hr).2 h
    rw [if_pos hx, if_pos h]
    ring
  · have hx : x ≠ 0 := fun hx => h ((cel_zero_iff x hr).1 hx)
    rw [if_neg hx, if_neg h]
    ring

theorem cel_s0_off (x : Site (n + 2)) (hr : 1 ≤ cel_rho x) :
    ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x = 2 * (n : ℤ) + zeta1 (x 0) (x 1) := by
  have hx : x ≠ 0 := by
    intro h
    subst h
    simp [cel_rho] at hr
  rw [cel_ceEta, dirac_of_ne hx]
  ring

section Plane

variable (t : ℕ) (x : Site (n + 2)) (hr : cel_rho x = 0)

include hr

theorem cel_p_add0 : cel_p t (x + unit (0 : Fin (n + 2))) = cel_Q (t : ℤ) (x 0 + 1) (x 1) := by
  unfold cel_p
  rw [cel_a_add0, cel_b_add0, cel_rho_add0, hr]
  unfold cel_val
  rw [if_pos rfl]

theorem cel_p_sub0 : cel_p t (x - unit (0 : Fin (n + 2))) = cel_Q (t : ℤ) (x 0 - 1) (x 1) := by
  unfold cel_p
  rw [cel_a_sub0, cel_b_sub0, cel_rho_sub0, hr]
  unfold cel_val
  rw [if_pos rfl]

theorem cel_p_add1 : cel_p t (x + unit (1 : Fin (n + 2))) = cel_Q (t : ℤ) (x 0) (x 1 + 1) := by
  unfold cel_p
  rw [cel_a_add1, cel_b_add1, cel_rho_add1, hr]
  unfold cel_val
  rw [if_pos rfl]

theorem cel_p_sub1 : cel_p t (x - unit (1 : Fin (n + 2))) = cel_Q (t : ℤ) (x 0) (x 1 - 1) := by
  unfold cel_p
  rw [cel_a_sub1, cel_b_sub1, cel_rho_sub1, hr]
  unfold cel_val
  rw [if_pos rfl]

theorem cel_p_addk (k : Fin n) :
    cel_p t (x + unit k.succ.succ) = cel_val (t : ℤ) (x 0) (x 1) 1 := by
  unfold cel_p
  rw [cel_a_addk, cel_b_addk, cel_rho_addk_of_zero x hr]

theorem cel_p_subk (k : Fin n) :
    cel_p t (x - unit k.succ.succ) = cel_val (t : ℤ) (x 0) (x 1) 1 := by
  unfold cel_p
  rw [cel_a_subk, cel_b_subk, cel_rho_subk_of_zero x hr]

theorem cel_p_plane : cel_p t x = cel_Q (t : ℤ) (x 0) (x 1) := by
  unfold cel_p cel_val
  rw [hr, if_pos rfl]

end Plane

theorem cel_hstep_plane (t : ℕ) (x : Site (n + 2)) (hr : cel_rho x = 0) :
    cel_p (t + 1) x ≤ cel_p t x +
      (if 2 * (((n + 2 : ℕ)) : ℤ) ≤
          (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p t) x
        then 1 else 0) := by
  by_cases h : cel_Q (t : ℤ) (x 0) (x 1) < cel_Q ((t + 1 : ℕ) : ℤ) (x 0) (x 1)
  · have h' : cel_Q (t : ℤ) (x 0) (x 1) < cel_Q ((t : ℤ) + 1) (x 0) (x 1) := by
      push_cast at h; exact h
    obtain ⟨e, h2D, hc⟩ := cel_ev (t : ℤ) (x 0) (x 1) h'
    have hcond : 2 * (((n + 2 : ℕ)) : ℤ) ≤
        (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p t) x := by
      rw [cel_s0_plane x hr, lap_eq, cel_nbr_split, cel_p_add0 t x hr, cel_p_sub0 t x hr,
        cel_p_add1 t x hr, cel_p_sub1 t x hr, cel_p_plane t x hr]
      simp only [cel_p_addk t x hr, cel_p_subk t x hr]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold cel_S at h2D
      have hprod : 0 ≤ (n : ℤ) * (cel_val (t : ℤ) (x 0) (x 1) 1 - cel_Q (t : ℤ) (x 0) (x 1)) :=
        mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.2 hc)
      push_cast
      nlinarith [hprod, h2D]
    rw [if_pos hcond, cel_p_plane t x hr, cel_p_plane (t + 1) x hr]
    push_cast at e ⊢
    linarith
  · rw [cel_p_plane t x hr, cel_p_plane (t + 1) x hr]
    have hind : (0 : ℤ) ≤ (if 2 * (((n + 2 : ℕ)) : ℤ) ≤
          (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p t) x
        then 1 else 0) := by
      split <;> norm_num
    push Not at h
    linarith

/-! ### Legality off the plane -/

theorem cel_val_ge_H (t a b r : ℤ) (hH : cel_H a b)
    (h : cel_t1 a b + r ≤ t) : 1 ≤ cel_val t a b r := by
  unfold cel_val
  by_cases h0 : r = 0
  · rw [if_pos h0]
    unfold cel_Q cel_f1
    have : cel_in1 a b ∧ cel_t1 a b ≤ t := ⟨hH.1, by omega⟩
    rw [if_pos this]
    have := cel_Q_nonneg t a b
    have h2 : (0 : ℤ) ≤ cel_f2 t a b := by
      unfold cel_f2; split_ifs <;> norm_num
    linarith
  · rw [if_neg h0, if_pos hH, if_pos h]

/-- A site off the plane whose plane projection is high has a neighbour, closer to the plane,
which has already toppled. -/
theorem cel_toward_ge (t : ℕ) (x : Site (n + 2)) (hr : 1 ≤ cel_rho x)
    (hH : cel_H (x 0) (x 1)) (h : cel_t1 (x 0) (x 1) + cel_rho x ≤ (t : ℤ) + 1) :
    1 ≤ nbrSumZ (cel_p t) x := by
  obtain ⟨k, hk⟩ := cel_rho_toward x hr
  rcases hk with hk | hk
  · have h1 := cel_single_add (cel_p t) (cel_p_nonneg t) x k.succ.succ
    have h2 : 1 ≤ cel_p t (x + unit k.succ.succ) := by
      unfold cel_p
      rw [cel_a_addk, cel_b_addk, hk]
      exact cel_val_ge_H _ _ _ _ hH (by omega)
    linarith
  · have h1 := cel_single_sub (cel_p t) (cel_p_nonneg t) x k.succ.succ
    have h2 : 1 ≤ cel_p t (x - unit k.succ.succ) := by
      unfold cel_p
      rw [cel_a_subk, cel_b_subk, hk]
      exact cel_val_ge_H _ _ _ _ hH (by omega)
    linarith

theorem cel_hstep_H (t : ℕ) (x : Site (n + 2)) (hr : 1 ≤ cel_rho x)
    (hH : cel_H (x 0) (x 1)) :
    cel_p (t + 1) x ≤ cel_p t x +
      (if 2 * (((n + 2 : ℕ)) : ℤ) ≤
          (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p t) x
        then 1 else 0) := by
  have hp : ∀ s : ℕ, cel_p s x
      = if cel_t1 (x 0) (x 1) + cel_rho x ≤ (s : ℤ) then 1 else 0 := by
    intro s
    unfold cel_p cel_val
    rw [if_neg (by omega), if_pos hH]
  have hind : (0 : ℤ) ≤ (if 2 * (((n + 2 : ℕ)) : ℤ) ≤
          (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p t) x
        then 1 else 0) := by
    split <;> norm_num
  have hnn := cel_p_nonneg t x
  by_cases hev : cel_t1 (x 0) (x 1) + cel_rho x ≤ (t : ℤ)
  · have h1 : cel_p t x = 1 := by rw [hp, if_pos hev]
    have h2 : cel_p (t + 1) x = 1 := by
      rw [hp, if_pos (by push_cast; omega)]
    rw [h1, h2]
    linarith
  · by_cases hev1 : cel_t1 (x 0) (x 1) + cel_rho x ≤ ((t + 1 : ℕ) : ℤ)
    · have h1 : cel_p t x = 0 := by rw [hp, if_neg hev]
      have h2 : cel_p (t + 1) x = 1 := by rw [hp, if_pos hev1]
      have hge := cel_toward_ge t x hr hH (by push_cast at hev1; exact hev1)
      have hcond : 2 * (((n + 2 : ℕ)) : ℤ) ≤
          (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p t) x := by
        rw [cel_s0_off x hr, lap_eq, h1, hH.2]
        push_cast
        linarith
      rw [if_pos hcond, h1, h2]
      norm_num
    · have h2 : cel_p (t + 1) x = 0 := by rw [hp, if_neg hev1]
      rw [h2]
      linarith

theorem cel_hstep_C (t : ℕ) (x : Site (n + 2)) (h0 : x 0 = 0) (h1 : x 1 = 0)
    (hr : cel_rho x = 1) :
    cel_p (t + 1) x ≤ cel_p t x +
      (if 2 * (((n + 2 : ℕ)) : ℤ) ≤
          (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p t) x
        then 1 else 0) := by
  have hnH : ¬ cel_H 0 0 := by decide
  have hp : ∀ s : ℕ, cel_p s x = if 4 ≤ (s : ℤ) then 1 else 0 := by
    intro s
    unfold cel_p cel_val
    rw [h0, h1, hr, if_neg (by norm_num), if_neg hnH, if_pos ⟨rfl, rfl, rfl⟩]
  have hind : (0 : ℤ) ≤ (if 2 * (((n + 2 : ℕ)) : ℤ) ≤
          (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p t) x
        then 1 else 0) := by
    split <;> norm_num
  have hnn := cel_p_nonneg t x
  by_cases hev : 4 ≤ (t : ℤ)
  · have e1 : cel_p t x = 1 := by rw [hp, if_pos hev]
    have e2 : cel_p (t + 1) x = 1 := by rw [hp, if_pos (by push_cast; omega)]
    rw [e1, e2]
    linarith
  · by_cases hev1 : 4 ≤ ((t + 1 : ℕ) : ℤ)
    · have e1 : cel_p t x = 0 := by rw [hp, if_neg hev]
      have e2 : cel_p (t + 1) x = 1 := by rw [hp, if_pos hev1]
      have ht : t = 3 := by push_cast at hev1; omega
      subst ht
      have hy : ∀ y : Site (n + 2), 0 ≤ cel_p 3 y := fun y => cel_p_nonneg 3 y
      obtain ⟨k, hk⟩ := cel_rho_toward x (by omega)
      have hthree : 3 ≤ nbrSumZ (cel_p 3) x := by
        have v0 : cel_p 3 (x + unit (0 : Fin (n + 2))) = 1 := by
          unfold cel_p
          rw [cel_a_add0, cel_b_add0, cel_rho_add0, h0, h1, hr]
          decide
        have v1 : cel_p 3 (x + unit (1 : Fin (n + 2))) = 1 := by
          unfold cel_p
          rw [cel_a_add1, cel_b_add1, cel_rho_add1, h0, h1, hr]
          decide
        rcases hk with hk | hk
        · have v2 : cel_p 3 (x + unit k.succ.succ) = 1 := by
            unfold cel_p
            rw [cel_a_addk, cel_b_addk, hk, h0, h1, hr]
            decide
          have := cel_nbr_three (cel_p 3) hy x k _ (Or.inl rfl)
          linarith
        · have v2 : cel_p 3 (x - unit k.succ.succ) = 1 := by
            unfold cel_p
            rw [cel_a_subk, cel_b_subk, hk, h0, h1, hr]
            decide
          have := cel_nbr_three (cel_p 3) hy x k _ (Or.inr rfl)
          linarith
      have hcond : 2 * (((n + 2 : ℕ)) : ℤ) ≤
          (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p 3) x := by
        rw [cel_s0_off x (by omega), lap_eq, e1, h0, h1]
        have hz : zeta1 0 0 = 1 := by decide
        rw [hz]
        push_cast
        linarith
      rw [if_pos hcond, e1, e2]
      norm_num
    · have e2 : cel_p (t + 1) x = 0 := by rw [hp, if_neg hev1]
      rw [e2]
      linarith

theorem cel_hstep_D (t : ℕ) (x : Site (n + 2)) (hr : 1 ≤ cel_rho x)
    (hH : ¬ cel_H (x 0) (x 1)) (hC : ¬ (x 0 = 0 ∧ x 1 = 0 ∧ cel_rho x = 1)) :
    cel_p (t + 1) x ≤ cel_p t x +
      (if 2 * (((n + 2 : ℕ)) : ℤ) ≤
          (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p t) x
        then 1 else 0) := by
  have hp : ∀ s : ℕ, cel_p s x = 0 := by
    intro s
    unfold cel_p cel_val
    rw [if_neg (by omega), if_neg hH, if_neg hC]
  have hind : (0 : ℤ) ≤ (if 2 * (((n + 2 : ℕ)) : ℤ) ≤
          (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p t) x
        then 1 else 0) := by
    split <;> norm_num
  rw [hp, hp]
  linarith

theorem cel_hstep (t : ℕ) (x : Site (n + 2)) :
    cel_p (t + 1) x ≤ cel_p t x +
      (if 2 * (((n + 2 : ℕ)) : ℤ) ≤
          (ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x) + lap (cel_p t) x
        then 1 else 0) := by
  by_cases hr : cel_rho x = 0
  · exact cel_hstep_plane t x hr
  · have hr1 : 1 ≤ cel_rho x := by have := cel_rho_nonneg x; omega
    by_cases hH : cel_H (x 0) (x 1)
    · exact cel_hstep_H t x hr1 hH
    · by_cases hC : x 0 = 0 ∧ x 1 = 0 ∧ cel_rho x = 1
      · exact cel_hstep_C t x hC.1 hC.2.1 hC.2.2
      · exact cel_hstep_D t x hr1 hH hC

/-! ### The arrival bound on the axis -/

theorem cel_in1_axis (m : ℕ) : cel_in1 (m : ℤ) 0 := by
  unfold cel_in1
  omega

theorem cel_t1_axis (m : ℕ) : cel_t1 (m : ℤ) 0 ≤ 2 * (m : ℤ) + 6 := by
  by_cases hm : m < 2
  · interval_cases m <;> decide
  · have h2 : (2 : ℤ) ≤ (m : ℤ) := by omega
    have hcol : cel_col (m : ℤ) = 2 + ((m : ℤ) - 2) % 4 := by
      unfold cel_col
      rw [if_neg (by omega)]
    have hsh : cel_sh (m : ℤ) = 6 * (((m : ℤ) - 2) / 4) := by
      unfold cel_sh
      rw [if_neg (by omega)]
    unfold cel_t1
    rw [hcol, hsh]
    have hr : ((m : ℤ) - 2) % 4 = 0 ∨ ((m : ℤ) - 2) % 4 = 1 ∨ ((m : ℤ) - 2) % 4 = 2 ∨
        ((m : ℤ) - 2) % 4 = 3 := by omega
    rcases hr with hr | hr | hr | hr
    · rw [hr, show cel_lk cel_tab1 (2 + 0) 0 = 3 by decide]
      omega
    · rw [hr, show cel_lk cel_tab1 (2 + 1) 0 = 12 by decide]
      omega
    · rw [hr, show cel_lk cel_tab1 (2 + 2) 0 = 13 by decide]
      omega
    · rw [hr, show cel_lk cel_tab1 (2 + 3) 0 = 8 by decide]
      omega

theorem cel_e1_0 (m : ℤ) : (m • e1 (n + 2)) (0 : Fin (n + 2)) = m := by
  simp [e1]

theorem cel_e1_1 (m : ℤ) : (m • e1 (n + 2)) (1 : Fin (n + 2)) = 0 := by
  simp [e1]

theorem cel_e1_k (m : ℤ) (k : Fin n) : (m • e1 (n + 2)) k.succ.succ = 0 := by
  simp [e1]

theorem cel_rho_e1 (m : ℤ) : cel_rho (m • e1 (n + 2)) = 0 := by
  rw [cel_rho_eq_zero_iff]
  exact fun k => cel_e1_k m k

end Exploding
