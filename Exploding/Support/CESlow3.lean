/-
The slow front of the counterexample background in dimension two: lifting the
cylinder supersolution of `CESlow2` to `ℤ²` by reflection and periodicity, and the
resulting lower bound `T((3 + 8n) e₁) ≥ 12 n` of `theorem:counterexample`, Step 4.
-/
import Exploding.Support.CESlow2

namespace Exploding

open LatticeProb

/-! ### The plane supersolution -/

/-- The supersolution on `ℤ²`: the cylinder function evaluated at the folded site. -/
def cels_w (t a b : ℤ) : ℤ := cels_cw t (cels_fold a) (b % 4)

/-- The reflected, periodic background `η̂` on `ℤ²`: `ζ₁`, with three extra chips at
`(0, 4k)` and `(-1, 4k)`. -/
def cels_eh (a b : ℤ) : ℤ := zeta1 a b + (if (a = 0 ∨ a = -1) ∧ b % 4 = 0 then 3 else 0)

/-- The neighbour sum of `cels_w` on `ℤ²`. -/
def cels_wN (t a b : ℤ) : ℤ :=
  cels_w t (a + 1) b + cels_w t (a - 1) b + cels_w t a (b + 1) + cels_w t a (b - 1)

theorem cels_zeta_fold (a b : ℤ) : zeta1 (cels_fold a) (b % 4) = zeta1 a b := by
  unfold zeta1 cels_fold
  split_ifs <;> omega

theorem cels_eh_eq (a b : ℤ) : cels_eh a b = cels_ceta (cels_fold a) (b % 4) := by
  unfold cels_eh cels_ceta
  rw [cels_zeta_fold]
  have h : (cels_fold a = 0 ∧ b % 4 = 0) ↔ ((a = 0 ∨ a = -1) ∧ b % 4 = 0) := by
    unfold cels_fold
    split_ifs <;> omega
  by_cases hh : (a = 0 ∨ a = -1) ∧ b % 4 = 0
  · rw [if_pos hh, if_pos (h.2 hh)]
  · rw [if_neg hh, if_neg (fun h' => hh (h.1 h'))]

theorem cels_fold_nbr (a : ℤ) :
    (cels_fold (a + 1) = cels_fold a + 1 ∧ cels_fold (a - 1) = cels_fold (cels_fold a - 1)) ∨
    (cels_fold (a + 1) = cels_fold (cels_fold a - 1) ∧ cels_fold (a - 1) = cels_fold a + 1) := by
  unfold cels_fold
  split_ifs <;> omega

theorem cels_wN_eq (t a b : ℤ) : cels_wN t a b = cels_cN t (cels_fold a) (b % 4) := by
  unfold cels_wN cels_cN cels_w
  have h1 : (b + 1) % 4 = (b % 4 + 1) % 4 := by omega
  have h2 : (b - 1) % 4 = (b % 4 + 3) % 4 := by omega
  rw [h1, h2]
  rcases cels_fold_nbr a with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
  · rw [e1, e2]
    ring

theorem cels_plane_ok (t a b : ℤ) (ht : 0 ≤ t)
    (h : 4 ≤ cels_eh a b + cels_wN t a b - 4 * cels_w t a b) :
    cels_w t a b + 1 ≤ cels_w (t + 1) a b := by
  have hc : 0 ≤ cels_fold a := by unfold cels_fold; split_ifs <;> omega
  have := cels_ok_all (cels_fold a) (b % 4) t hc (by omega) (by omega) ht
  unfold cels_ok at this
  rw [cels_eh_eq, cels_wN_eq] at h
  exact this h

theorem cels_W_nonneg (t c y : ℤ) (ht : 0 ≤ t) : 0 ≤ cels_W t c y := by
  unfold cels_W
  split_ifs <;> omega

theorem cels_cw_nonneg (t c y : ℤ) (ht : 0 ≤ t) : 0 ≤ cels_cw t c y := by
  unfold cels_cw cels_u
  have := cels_W_nonneg t c y ht
  split_ifs <;> omega

theorem cels_cw_mono (t c y : ℤ) : cels_cw t c y ≤ cels_cw (t + 1) c y := by
  unfold cels_cw cels_W
  split_ifs <;> omega

theorem cels_w_mono (t a b : ℤ) : cels_w t a b ≤ cels_w (t + 1) a b :=
  cels_cw_mono _ _ _

/-! ### The family on `Site 2` -/

/-- The supersolution as a family of functions on `ℤ²`. -/
def cels_wP (t : ℕ) (x : Site 2) : ℤ := cels_w (t : ℤ) (x 0) (x 1)

theorem cels_a_add0 (x : Site 2) : (x + unit (0 : Fin 2)) 0 = x 0 + 1 := by
  simp [unit]
theorem cels_b_add0 (x : Site 2) : (x + unit (0 : Fin 2)) 1 = x 1 := by
  simp [unit]
theorem cels_a_sub0 (x : Site 2) : (x - unit (0 : Fin 2)) 0 = x 0 - 1 := by
  simp [unit]
theorem cels_b_sub0 (x : Site 2) : (x - unit (0 : Fin 2)) 1 = x 1 := by
  simp [unit]
theorem cels_a_add1 (x : Site 2) : (x + unit (1 : Fin 2)) 0 = x 0 := by
  simp [unit]
theorem cels_b_add1 (x : Site 2) : (x + unit (1 : Fin 2)) 1 = x 1 + 1 := by
  simp [unit]
theorem cels_a_sub1 (x : Site 2) : (x - unit (1 : Fin 2)) 0 = x 0 := by
  simp [unit]
theorem cels_b_sub1 (x : Site 2) : (x - unit (1 : Fin 2)) 1 = x 1 - 1 := by
  simp [unit]

theorem cels_lap (t : ℕ) (x : Site 2) :
    lap (cels_wP t) x = cels_wN (t : ℤ) (x 0) (x 1) - 4 * cels_w (t : ℤ) (x 0) (x 1) := by
  unfold lap nbrSumZ cels_wN
  rw [Fin.sum_univ_two]
  unfold cels_wP
  rw [cels_a_add0, cels_b_add0, cels_a_sub0, cels_b_sub0, cels_a_add1, cels_b_add1,
    cels_a_sub1, cels_b_sub1]
  push_cast
  ring

theorem cels_ceEta (x : Site 2) : ceEta 2 x = zeta1 (x 0) (x 1) := by
  unfold ceEta
  have e0 : (⟨0, by norm_num⟩ : Fin 2) = 0 := rfl
  have e1 : (⟨1, by norm_num⟩ : Fin 2) = 1 := rfl
  simp [e0, e1]

theorem cels_s0_le (x : Site 2) :
    ceEta 2 x + 3 * dirac (0 : Site 2) x ≤ cels_eh (x 0) (x 1) := by
  rw [cels_ceEta]
  unfold cels_eh dirac
  by_cases hx : x = 0
  · have h0 : x 0 = 0 := by rw [hx]; rfl
    have h1 : x 1 = 0 := by rw [hx]; rfl
    rw [if_pos hx, if_pos (by rw [h0, h1]; decide)]
    linarith
  · rw [if_neg hx]
    split_ifs <;> omega

theorem cels_hstep (t : ℕ) (x : Site 2)
    (h : 2 * (((2 : ℕ)) : ℤ) ≤ (ceEta 2 x + 3 * dirac (0 : Site 2) x) + lap (cels_wP t) x) :
    cels_wP t x + 1 ≤ cels_wP (t + 1) x := by
  rw [cels_lap] at h
  have hs := cels_s0_le x
  have h' : 4 ≤ cels_eh (x 0) (x 1) + cels_wN (t : ℤ) (x 0) (x 1)
      - 4 * cels_w (t : ℤ) (x 0) (x 1) := by
    push_cast at h
    linarith
  have := cels_plane_ok (t : ℤ) (x 0) (x 1) (by positivity) h'
  unfold cels_wP
  push_cast
  exact this

/-- **The supersolution bound.**  The parallel toppling odometer of the exploding
sandpile of `ceEta 2` is at most `cels_wP`. -/
theorem cels_podo_le (t : ℕ) (x : Site 2) :
    podo (fun y => ceEta 2 y + 3 * dirac (0 : Site 2) y) t x ≤ cels_wP t x := by
  refine cels_supsol (fun y => ceEta 2 y + 3 * dirac (0 : Site 2) y) cels_wP ?_ ?_ ?_ t x
  · intro y
    unfold cels_wP
    have := cels_cw_nonneg ((0 : ℕ) : ℤ) (cels_fold (y 0)) (y 1 % 4) (by norm_num)
    simpa [cels_w] using this
  · intro t y
    unfold cels_wP
    push_cast
    exact cels_w_mono _ _ _
  · intro t y h
    exact cels_hstep t y h

end Exploding
