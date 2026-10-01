/-
The explicit two-dimensional toppling schedule used to bound the arrival times
`T(n e₁)` of the counterexample background from above.

On the half strip `{a ≥ -2, -2 ≤ b ≤ 5}` of `ℤ²` every site topples once
(`cel_t1`), and the "high" sites (those with `ζ₁ = 3`) topple a second time
(`cel_t2`), at the times of two tables whose columns `a ≥ 2` repeat with period `4`
in space and `6` in time.  The legality of every toppling of the schedule is the
finite check `cel_chk`, verified on the columns `-2 ≤ a ≤ 6` by computation and
propagated to every column by the translation `(a, t) ↦ (a + 4, t + 6)`.
-/
import Exploding.Support.CELow

namespace Exploding

open LatticeProb

/-- The first-toppling times, rows `b = -2, …, 5`, columns `a = -2, …, 5`. -/
def cel_tab1 : List (List ℤ) :=
  [[7, 6, 5, 4, 5, 6, 7, 8],
   [6, 7, 6, 3, 4, 13, 14, 9],
   [5, 6, 1, 2, 3, 12, 13, 8],
   [4, 3, 2, 3, 4, 5, 6, 7],
   [5, 4, 3, 4, 5, 6, 7, 8],
   [6, 13, 12, 5, 6, 15, 16, 9],
   [7, 14, 13, 6, 7, 16, 17, 10],
   [8, 9, 8, 7, 8, 9, 10, 11]]

/-- The second-toppling times (`0` where there is no second toppling), same layout. -/
def cel_tab2 : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 9, 12, 0, 0, 17],
   [0, 0, 7, 8, 11, 0, 0, 16],
   [0, 9, 8, 9, 10, 13, 14, 15],
   [0, 12, 11, 10, 11, 14, 15, 16],
   [0, 0, 0, 13, 14, 0, 0, 17],
   [0, 0, 0, 14, 15, 0, 0, 18],
   [0, 0, 0, 0, 0, 0, 0, 0]]

/-- Table lookup at the site `(a, b)`. -/
def cel_lk (L : List (List ℤ)) (a b : ℤ) : ℤ :=
  (L.getD (b + 2).toNat []).getD (a + 2).toNat 0

/-- The table column used for column `a`: columns `a ≥ 2` repeat with period `4`. -/
def cel_col (a : ℤ) : ℤ := if a < 2 then a else 2 + (a - 2) % 4

/-- The time shift of column `a`: `6` per period. -/
def cel_sh (a : ℤ) : ℤ := if a < 2 then 0 else 6 * ((a - 2) / 4)

/-- The half strip carrying the schedule. -/
def cel_in1 (a b : ℤ) : Prop := -2 ≤ a ∧ -2 ≤ b ∧ b ≤ 5

instance (a b : ℤ) : Decidable (cel_in1 a b) :=
  inferInstanceAs (Decidable (-2 ≤ a ∧ -2 ≤ b ∧ b ≤ 5))

/-- The sites of the strip that topple twice. -/
def cel_in2 (a b : ℤ) : Prop := cel_in1 a b ∧ cel_lk cel_tab2 (cel_col a) b ≠ 0

instance (a b : ℤ) : Decidable (cel_in2 a b) :=
  inferInstanceAs (Decidable (cel_in1 a b ∧ cel_lk cel_tab2 (cel_col a) b ≠ 0))

/-- Time of the first toppling of `(a, b)`. -/
def cel_t1 (a b : ℤ) : ℤ := cel_lk cel_tab1 (cel_col a) b + cel_sh a

/-- Time of the second toppling of `(a, b)`. -/
def cel_t2 (a b : ℤ) : ℤ := cel_lk cel_tab2 (cel_col a) b + cel_sh a

/-- The number of the first topplings of `(a, b)` completed by time `t`. -/
def cel_f1 (t a b : ℤ) : ℤ := if cel_in1 a b ∧ cel_t1 a b ≤ t then 1 else 0

/-- The number of the second topplings of `(a, b)` completed by time `t`. -/
def cel_f2 (t a b : ℤ) : ℤ := if cel_in2 a b ∧ cel_t2 a b ≤ t then 1 else 0

/-- The number of topplings of `(a, b)` completed by time `t`. -/
def cel_Q (t a b : ℤ) : ℤ := cel_f1 t a b + cel_f2 t a b

/-- The background `ζ₁` plus the three extra chips at the origin. -/
def cel_zh (a b : ℤ) : ℤ := zeta1 a b + (if a = 0 ∧ b = 0 then 3 else 0)

/-- The in-plane neighbour sum of the schedule at time `t`. -/
def cel_S (t a b : ℤ) : ℤ :=
  cel_Q t (a + 1) b + cel_Q t (a - 1) b + cel_Q t a (b + 1) + cel_Q t a (b - 1)

/-- Legality of every toppling of the schedule at the site `(a, b)`. -/
def cel_chk (a b : ℤ) : Prop :=
  (cel_in1 a b → 1 ≤ cel_t1 a b ∧ 4 ≤ cel_zh a b + cel_S (cel_t1 a b - 1) a b) ∧
  (cel_in2 a b → cel_t1 a b + 2 ≤ cel_t2 a b ∧
    8 ≤ cel_zh a b + cel_S (cel_t2 a b - 1) a b)

instance (a b : ℤ) : Decidable (cel_chk a b) := by
  unfold cel_chk; infer_instance

theorem cel_chk_base (a b : ℤ) (h1 : -2 ≤ a) (h2 : a ≤ 6) (h3 : -2 ≤ b) (h4 : b ≤ 5) :
    cel_chk a b := by
  interval_cases a <;> interval_cases b <;> decide

/-! ### The translation `(a, t) ↦ (a + 4, t + 6)` -/

theorem cel_col_add4 {a : ℤ} (ha : 2 ≤ a) : cel_col (a + 4) = cel_col a := by
  unfold cel_col
  split_ifs <;> omega

theorem cel_sh_add4 {a : ℤ} (ha : 2 ≤ a) : cel_sh (a + 4) = cel_sh a + 6 := by
  unfold cel_sh
  split_ifs <;> omega

theorem cel_t1_add4 {a : ℤ} (ha : 2 ≤ a) (b : ℤ) : cel_t1 (a + 4) b = cel_t1 a b + 6 := by
  unfold cel_t1
  rw [cel_col_add4 ha, cel_sh_add4 ha]
  ring

theorem cel_t2_add4 {a : ℤ} (ha : 2 ≤ a) (b : ℤ) : cel_t2 (a + 4) b = cel_t2 a b + 6 := by
  unfold cel_t2
  rw [cel_col_add4 ha, cel_sh_add4 ha]
  ring

theorem cel_in1_add4 {a : ℤ} (ha : 2 ≤ a) (b : ℤ) : cel_in1 (a + 4) b ↔ cel_in1 a b := by
  unfold cel_in1
  omega

theorem cel_in2_add4 {a : ℤ} (ha : 2 ≤ a) (b : ℤ) : cel_in2 (a + 4) b ↔ cel_in2 a b := by
  unfold cel_in2
  rw [cel_in1_add4 ha, cel_col_add4 ha]

theorem cel_f1_add4 {a : ℤ} (ha : 2 ≤ a) (t b : ℤ) :
    cel_f1 (t + 6) (a + 4) b = cel_f1 t a b := by
  unfold cel_f1
  rw [cel_t1_add4 ha]
  have h : cel_t1 a b + 6 ≤ t + 6 ↔ cel_t1 a b ≤ t := by omega
  simp only [cel_in1_add4 ha, h]

theorem cel_f2_add4 {a : ℤ} (ha : 2 ≤ a) (t b : ℤ) :
    cel_f2 (t + 6) (a + 4) b = cel_f2 t a b := by
  unfold cel_f2
  rw [cel_t2_add4 ha]
  have h : cel_t2 a b + 6 ≤ t + 6 ↔ cel_t2 a b ≤ t := by omega
  simp only [cel_in2_add4 ha, h]

theorem cel_Q_add4 {a : ℤ} (ha : 2 ≤ a) (t b : ℤ) :
    cel_Q (t + 6) (a + 4) b = cel_Q t a b := by
  unfold cel_Q
  rw [cel_f1_add4 ha, cel_f2_add4 ha]

theorem cel_zh_add4 {a : ℤ} (ha : 1 ≤ a) (b : ℤ) : cel_zh (a + 4) b = cel_zh a b := by
  unfold cel_zh zeta1
  have h4 : (a + 4) % 4 = a % 4 := by omega
  have h0 : ¬ (a + 4 = 0) := by omega
  have h0' : ¬ (a = 0) := by omega
  simp only [h4, h0, h0', false_and, if_false]

theorem cel_S_add4 {a : ℤ} (ha : 3 ≤ a) (t b : ℤ) :
    cel_S (t + 6) (a + 4) b = cel_S t a b := by
  unfold cel_S
  have e1 : a + 4 + 1 = (a + 1) + 4 := by ring
  have e2 : a + 4 - 1 = (a - 1) + 4 := by ring
  rw [e1, e2, cel_Q_add4 (by omega : 2 ≤ a + 1), cel_Q_add4 (by omega : 2 ≤ a - 1),
    cel_Q_add4 (by omega : 2 ≤ a), cel_Q_add4 (by omega : 2 ≤ a)]

/-- Legality of the schedule propagates from column `a` to column `a + 4`. -/
theorem cel_chk_add4 {a : ℤ} (ha : 3 ≤ a) (b : ℤ) (h : cel_chk a b) : cel_chk (a + 4) b := by
  have ha2 : 2 ≤ a := by omega
  unfold cel_chk at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hin => ?_, fun hin => ?_⟩
  · rw [cel_in1_add4 ha2] at hin
    obtain ⟨hh1, hh2⟩ := h1 hin
    rw [cel_t1_add4 ha2, cel_zh_add4 (by omega)]
    have e : cel_t1 a b + 6 - 1 = (cel_t1 a b - 1) + 6 := by ring
    rw [e, cel_S_add4 ha]
    exact ⟨by omega, hh2⟩
  · rw [cel_in2_add4 ha2] at hin
    obtain ⟨hh1, hh2⟩ := h2 hin
    rw [cel_t1_add4 ha2, cel_t2_add4 ha2, cel_zh_add4 (by omega)]
    have e : cel_t2 a b + 6 - 1 = (cel_t2 a b - 1) + 6 := by ring
    rw [e, cel_S_add4 ha]
    exact ⟨by omega, hh2⟩

theorem cel_chk_all (a b : ℤ) : cel_chk a b := by
  by_cases hb : -2 ≤ b ∧ b ≤ 5
  swap
  · refine ⟨fun h => absurd h ?_, fun h => absurd h.1 ?_⟩ <;>
      · unfold cel_in1; omega
  by_cases ha : a ≤ 6
  · by_cases ha' : -2 ≤ a
    · exact cel_chk_base a b ha' ha hb.1 hb.2
    · refine ⟨fun h => absurd h ?_, fun h => absurd h.1 ?_⟩ <;>
        · unfold cel_in1; omega
  · have key : ∀ k : ℕ, ∀ a₀ : ℤ, 3 ≤ a₀ → a₀ ≤ 6 → cel_chk (a₀ + 4 * k) b := by
      intro k
      induction k with
      | zero =>
        intro a₀ h1 h2
        simpa using cel_chk_base a₀ b (by omega) h2 hb.1 hb.2
      | succ k ih =>
        intro a₀ h1 h2
        have := cel_chk_add4 (by omega : 3 ≤ a₀ + 4 * k) b (ih a₀ h1 h2)
        have e : a₀ + 4 * ((k + 1 : ℕ) : ℤ) = a₀ + 4 * k + 4 := by push_cast; ring
        rw [e]
        exact this
    have h := key ((a - 3) / 4).toNat (3 + (a - 3) % 4) (by omega) (by omega)
    have e : (3 + (a - 3) % 4) + 4 * (((a - 3) / 4).toNat : ℤ) = a := by omega
    rw [e] at h
    exact h

/-! ### The value of the schedule off the plane, and the event lemma -/

/-- The sites of the strip with `ζ₁ = 3`. -/
def cel_H (a b : ℤ) : Prop := cel_in1 a b ∧ zeta1 a b = 3

instance (a b : ℤ) : Decidable (cel_H a b) :=
  inferInstanceAs (Decidable (cel_in1 a b ∧ zeta1 a b = 3))

/-- The value at time `t` of the schedule at a site whose first two coordinates are
`(a, b)` and whose remaining coordinates have `ℓ¹`-norm `r`: in the plane `r = 0` the
schedule `cel_Q`; off the plane the high sites topple once, `r` steps after the
plane site, and the sites above the origin topple once at time `4`. -/
def cel_val (t a b r : ℤ) : ℤ :=
  if r = 0 then cel_Q t a b
  else if cel_H a b then (if cel_t1 a b + r ≤ t then 1 else 0)
  else if a = 0 ∧ b = 0 ∧ r = 1 then (if 4 ≤ t then 1 else 0)
  else 0

theorem cel_Q_nonneg (t a b : ℤ) : 0 ≤ cel_Q t a b := by
  unfold cel_Q cel_f1 cel_f2
  split_ifs <;> norm_num

theorem cel_val_nonneg (t a b r : ℤ) : 0 ≤ cel_val t a b r := by
  unfold cel_val
  split_ifs <;> first | exact cel_Q_nonneg _ _ _ | norm_num

theorem cel_in2_cases {a b : ℤ} (h : cel_in2 a b) : zeta1 a b = 3 ∨ (a = 0 ∧ b = 0) := by
  have hfin : ∀ a' b' : ℤ, -2 ≤ a' → a' ≤ 5 → -2 ≤ b' → b' ≤ 5 →
      cel_lk cel_tab2 a' b' ≠ 0 → zeta1 a' b' = 3 ∨ (a' = 0 ∧ b' = 0) := by
    intro a' b' h1 h2 h3 h4
    interval_cases a' <;> interval_cases b' <;> decide
  obtain ⟨hin, hne⟩ := h
  obtain ⟨_, hb1, hb2⟩ := hin
  have hcol1 : -2 ≤ cel_col a := by
    unfold cel_col; split_ifs <;> omega
  have hcol2 : cel_col a ≤ 5 := by
    unfold cel_col; split_ifs <;> omega
  have hz : zeta1 a b = zeta1 (cel_col a) b := by
    unfold zeta1 cel_col
    split_ifs <;> first | rfl | omega
  have hcase := hfin (cel_col a) b hcol1 hcol2 hb1 hb2 hne
  rw [hz]
  rcases hcase with h | ⟨h1, h2⟩
  · exact Or.inl h
  · by_cases ha : a < 2
    · unfold cel_col at h1
      rw [if_pos ha] at h1
      exact Or.inr ⟨h1, h2⟩
    · unfold cel_col at h1
      rw [if_neg ha] at h1
      omega

theorem cel_t2_origin : cel_t2 0 0 = 7 := by decide

/-- **The event lemma.**  Whenever the schedule topples `(a, b)` at the step `t → t + 1`,
the toppling is legal in the plane (`4 ≤ ζ + S - 4 Q`) and the site is not ahead of its
neighbours above and below the plane (`Q ≤ cel_val t a b 1`). -/
theorem cel_ev (t a b : ℤ) (h : cel_Q t a b < cel_Q (t + 1) a b) :
    cel_Q (t + 1) a b = cel_Q t a b + 1 ∧
    4 ≤ cel_zh a b + cel_S t a b - 4 * cel_Q t a b ∧
    cel_Q t a b ≤ cel_val t a b 1 := by
  obtain ⟨c1, c2⟩ := cel_chk_all a b
  by_cases hA : cel_in1 a b
  swap
  · exfalso
    have hB : ¬ cel_in2 a b := fun hh => hA hh.1
    unfold cel_Q cel_f1 cel_f2 at h
    simp only [hA, hB, false_and, if_false] at h
    omega
  obtain ⟨hT1, hS1⟩ := c1 hA
  by_cases hB : cel_in2 a b
  · obtain ⟨hT12, hS2⟩ := c2 hB
    unfold cel_Q cel_f1 cel_f2 at h ⊢
    simp only [hA, hB, true_and] at h ⊢
    by_cases hj1 : cel_t1 a b = t + 1
    · have e1 : ¬ cel_t1 a b ≤ t := by omega
      have e2 : ¬ cel_t2 a b ≤ t := by omega
      have e3 : ¬ cel_t2 a b ≤ t + 1 := by omega
      have e4 : cel_t1 a b ≤ t + 1 := by omega
      simp only [e1, e2, e3, e4, if_true, if_false]
      have hSt : cel_S t a b = cel_S (cel_t1 a b - 1) a b := by
        congr 1; omega
      refine ⟨by norm_num, ?_, ?_⟩
      · rw [← hSt] at hS1; omega
      · have := cel_val_nonneg t a b 1
        simpa using this
    · by_cases hj2 : cel_t2 a b = t + 1
      · have e1 : cel_t1 a b ≤ t := by omega
        have e2 : ¬ cel_t2 a b ≤ t := by omega
        have e3 : cel_t2 a b ≤ t + 1 := by omega
        have e4 : cel_t1 a b ≤ t + 1 := by omega
        simp only [e1, e2, e3, e4, if_true, if_false]
        have hSt : cel_S t a b = cel_S (cel_t2 a b - 1) a b := by
          congr 1; omega
        refine ⟨by norm_num, ?_, ?_⟩
        · rw [← hSt] at hS2; omega
        · unfold cel_val
          simp only [one_ne_zero, if_false]
          rcases cel_in2_cases hB with hz | ⟨ha0, hb0⟩
          · have hH : cel_H a b := ⟨hA, hz⟩
            simp only [hH, if_true]
            have : cel_t1 a b + 1 ≤ t := by omega
            simp [this]
          · have hnH : ¬ cel_H a b := by
              rintro ⟨_, hz⟩
              subst ha0; subst hb0
              revert hz; decide
            simp only [hnH, if_false]
            subst ha0; subst hb0
            have h7 : t = 6 := by
              have := cel_t2_origin
              omega
            simp [h7]
      · exfalso
        have e1 : (cel_t1 a b ≤ t + 1 ↔ cel_t1 a b ≤ t) := by omega
        have e2 : (cel_t2 a b ≤ t + 1 ↔ cel_t2 a b ≤ t) := by omega
        simp only [e1, e2] at h
        omega
  · unfold cel_Q cel_f1 cel_f2 at h ⊢
    simp only [hA, hB, true_and, false_and, if_false] at h ⊢
    by_cases hj1 : cel_t1 a b = t + 1
    · have e1 : ¬ cel_t1 a b ≤ t := by omega
      have e4 : cel_t1 a b ≤ t + 1 := by omega
      simp only [e1, e4, if_true, if_false]
      have hSt : cel_S t a b = cel_S (cel_t1 a b - 1) a b := by
        congr 1; omega
      refine ⟨by norm_num, ?_, ?_⟩
      · rw [← hSt] at hS1; omega
      · have := cel_val_nonneg t a b 1
        simpa using this
    · exfalso
      have e1 : (cel_t1 a b ≤ t + 1 ↔ cel_t1 a b ≤ t) := by omega
      simp only [e1] at h
      omega

end Exploding
