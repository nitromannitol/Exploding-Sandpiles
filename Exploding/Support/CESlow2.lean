/-
The explicit odometer on the reflected cylinder and the finite check that it is a
supersolution; see `CESlow`.
-/
import Exploding.Support.CESlow

namespace Exploding

open LatticeProb

/-- Toppling times of the sites of the first columns of the cylinder, rows `y = 0, …, 3`,
columns `c = 0, …, 5`. -/
def cels_tab : List (List ℤ) :=
  [[1, 4, 7, 8, 9, 12],
   [4, 5, 6, 9, 10, 11],
   [5, 6, 7, 10, 11, 12],
   [2, 5, 8, 9, 10, 13]]

def cels_lk (c y : ℤ) : ℤ := (cels_tab.getD y.toNat []).getD c.toNat 0

/-- The table column of column `c`: columns `c ≥ 2` repeat with period `4`. -/
def cels_col (c : ℤ) : ℤ := if c < 2 then c else 2 + (c - 2) % 4

/-- The time shift of column `c`: `6` per period. -/
def cels_sh (c : ℤ) : ℤ := if c < 2 then 0 else 6 * ((c - 2) / 4)

/-- The time of the first toppling of the second wave at the cylinder site `(c, y)`. -/
def cels_tau (c y : ℤ) : ℤ := cels_lk (cels_col c) y + cels_sh c

/-- The number of topplings of the second wave of `(c, y)` by time `t`: the origin topples
at the times `1, 3, 7, 11, …`, every other site at `τ, τ + 4, τ + 8, …`. -/
def cels_W (t c y : ℤ) : ℤ :=
  if c = 0 ∧ y = 0 then (if 1 ≤ t then 1 else 0) + (if 3 ≤ t then (t - 3) / 4 + 1 else 0)
  else if t < cels_tau c y then 0 else (t - cels_tau c y) / 4 + 1

/-- The first wave: every site with `ζ₁ = 3` has toppled once. -/
def cels_u (c y : ℤ) : ℤ := if zeta1 c y = 3 then 1 else 0

/-- The candidate bound on the odometer on the cylinder. -/
def cels_cw (t c y : ℤ) : ℤ := cels_u c y + cels_W t c y

/-- The reflection of the half line `c < 0` onto `c ≥ 0`. -/
def cels_fold (a : ℤ) : ℤ := if 0 ≤ a then a else -1 - a

/-- The cylinder neighbour sum (reflecting at the wall, periodic in the rows). -/
def cels_cN (t c y : ℤ) : ℤ :=
  cels_cw t (c + 1) y + cels_cw t (cels_fold (c - 1)) y + cels_cw t c ((y + 1) % 4)
    + cels_cw t c ((y + 3) % 4)

/-- The reflected background `η̂` on the cylinder: `ζ₁`, with three extra chips at the
wall corner. -/
def cels_ceta (c y : ℤ) : ℤ := zeta1 c y + (if c = 0 ∧ y = 0 then 3 else 0)

/-- The supersolution property at the cylinder site `(c, y)` at time `t`. -/
def cels_ok (c y t : ℤ) : Prop :=
  4 ≤ cels_ceta c y + cels_cN t c y - 4 * cels_cw t c y →
    cels_cw t c y + 1 ≤ cels_cw (t + 1) c y

instance (c y t : ℤ) : Decidable (cels_ok c y t) := by
  unfold cels_ok; infer_instance

theorem cels_ok_base (c y t : ℤ) (hc0 : 0 ≤ c) (hc1 : c ≤ 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 19) : cels_ok c y t := by
  interval_cases c <;> interval_cases y <;> interval_cases t <;> decide

/-! ### Bounds on the toppling times -/

theorem cels_lk_pos (c y : ℤ) (hc0 : 0 ≤ c) (hc1 : c ≤ 5) (hy0 : 0 ≤ y) (hy1 : y ≤ 3) :
    1 ≤ cels_lk c y := by
  interval_cases c <;> interval_cases y <;> decide

theorem cels_col_range (c : ℤ) (hc : 0 ≤ c) : 0 ≤ cels_col c ∧ cels_col c ≤ 5 := by
  unfold cels_col
  split_ifs <;> omega

theorem cels_sh_nonneg (c : ℤ) : 0 ≤ cels_sh c := by
  unfold cels_sh
  split_ifs <;> omega

theorem cels_tau_pos (c y : ℤ) (hc : 0 ≤ c) (hy0 : 0 ≤ y) (hy1 : y ≤ 3) :
    1 ≤ cels_tau c y := by
  have h1 := cels_col_range c hc
  have h2 := cels_lk_pos (cels_col c) y h1.1 h1.2 hy0 hy1
  have h3 := cels_sh_nonneg c
  unfold cels_tau
  omega

theorem cels_tau_le (c y : ℤ) (hc0 : 0 ≤ c) (hc1 : c ≤ 7) (hy0 : 0 ≤ y) (hy1 : y ≤ 3) :
    cels_tau c y ≤ 16 := by
  interval_cases c <;> interval_cases y <;> decide

theorem cels_tau_add4 {c : ℤ} (hc : 2 ≤ c) (y : ℤ) :
    cels_tau (c + 4) y = cels_tau c y + 6 := by
  have h1 : cels_col (c + 4) = cels_col c := by
    unfold cels_col; split_ifs <;> omega
  have h2 : cels_sh (c + 4) = cels_sh c + 6 := by
    unfold cels_sh; split_ifs <;> omega
  unfold cels_tau
  rw [h1, h2]
  ring

/-! ### Stationarity and translation -/

theorem cels_W_add {c : ℤ} (hc : 2 ≤ c) (t y : ℤ) :
    cels_W (t + 6) (c + 4) y = cels_W t c y := by
  have h1 : ¬ (c + 4 = 0 ∧ y = 0) := by omega
  have h2 : ¬ (c = 0 ∧ y = 0) := by omega
  unfold cels_W
  rw [if_neg h1, if_neg h2, cels_tau_add4 hc]
  split_ifs <;> omega

theorem cels_W_stat (c y t : ℤ) (hne : ¬ (c = 0 ∧ y = 0)) (h : cels_tau c y ≤ t + 4) :
    cels_W (t + 4) c y = cels_W t c y + 1 := by
  unfold cels_W
  rw [if_neg hne, if_neg hne]
  split_ifs <;> omega

theorem cels_W_stat0 (t : ℤ) (h : 1 ≤ t) : cels_W (t + 4) 0 0 = cels_W t 0 0 + 1 := by
  unfold cels_W
  simp only [and_self, if_true]
  split_ifs <;> omega

theorem cels_u_add4 (c y : ℤ) : cels_u (c + 4) y = cels_u c y := by
  unfold cels_u zeta1
  have h4 : (c + 4) % 4 = c % 4 := by omega
  rw [h4]

theorem cels_cw_add {c : ℤ} (hc : 2 ≤ c) (t y : ℤ) :
    cels_cw (t + 6) (c + 4) y = cels_cw t c y := by
  unfold cels_cw
  rw [cels_u_add4, cels_W_add hc]

theorem cels_cw_stat (c y t : ℤ) (hc0 : 0 ≤ c) (hc1 : c ≤ 7) (hy0 : 0 ≤ y) (hy1 : y ≤ 3)
    (ht : 16 ≤ t) : cels_cw (t + 4) c y = cels_cw t c y + 1 := by
  unfold cels_cw
  by_cases ho : c = 0 ∧ y = 0
  · obtain ⟨h1, h2⟩ := ho
    subst h1; subst h2
    have := cels_W_stat0 t (by omega)
    omega
  · have h1 := cels_tau_le c y hc0 hc1 hy0 hy1
    have := cels_W_stat c y t ho (by omega)
    omega

/-- Legality propagates `4` steps forward in time once all the toppling times of the
neighbourhood have passed. -/
theorem cels_ok_add4 (c y t : ℤ) (hc0 : 0 ≤ c) (hc1 : c ≤ 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 3)
    (ht : 16 ≤ t) (h : cels_ok c y t) : cels_ok c y (t + 4) := by
  have hf0 : 0 ≤ cels_fold (c - 1) := by unfold cels_fold; split_ifs <;> omega
  have hf1 : cels_fold (c - 1) ≤ 7 := by unfold cels_fold; split_ifs <;> omega
  have e0 := cels_cw_stat c y t hc0 (by omega) hy0 hy1 ht
  have e1 := cels_cw_stat (c + 1) y t (by omega) (by omega) hy0 hy1 ht
  have e2 := cels_cw_stat (cels_fold (c - 1)) y t hf0 hf1 hy0 hy1 ht
  have e3 := cels_cw_stat c ((y + 1) % 4) t hc0 (by omega) (by omega) (by omega) ht
  have e4 := cels_cw_stat c ((y + 3) % 4) t hc0 (by omega) (by omega) (by omega) ht
  have e5 := cels_cw_stat c y (t + 1) hc0 (by omega) hy0 hy1 (by omega)
  unfold cels_ok cels_cN at h ⊢
  rw [show t + 4 + 1 = (t + 1) + 4 by ring, e5, e0, e1, e2, e3, e4]
  intro hc
  have := h (by omega)
  omega

theorem cels_ok_nat (c y : ℤ) (hc0 : 0 ≤ c) (hc1 : c ≤ 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 3) :
    ∀ t : ℕ, cels_ok c y (t : ℤ) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t ≤ 19
    · exact cels_ok_base c y t hc0 hc1 hy0 hy1 (by omega) (by omega)
    · have h1 := ih (t - 4) (by omega)
      have h2 := cels_ok_add4 c y ((t - 4 : ℕ) : ℤ) hc0 hc1 hy0 hy1 (by omega) h1
      have e : ((t - 4 : ℕ) : ℤ) + 4 = (t : ℤ) := by omega
      rw [e] at h2
      exact h2

/-! ### Before the wave, and translation in space -/

theorem cels_cw_nonpos (t c y : ℤ) (ht : t ≤ 0) (hc : 0 ≤ c) (hy0 : 0 ≤ y) (hy1 : y ≤ 3) :
    cels_cw t c y = cels_u c y := by
  have htau := cels_tau_pos c y hc hy0 hy1
  unfold cels_cw cels_W
  split_ifs <;> omega

theorem cels_ok_nonpos (c y t : ℤ) (hc0 : 3 ≤ c) (hc1 : c ≤ 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 3)
    (ht : t ≤ 0) : cels_ok c y t := by
  intro hcond
  exfalso
  have hf0 : 0 ≤ cels_fold (c - 1) := by unfold cels_fold; split_ifs <;> omega
  unfold cels_cN at hcond
  rw [cels_cw_nonpos t c y ht (by omega) hy0 hy1, cels_cw_nonpos t (c + 1) y ht (by omega) hy0 hy1,
    cels_cw_nonpos t (cels_fold (c - 1)) y ht hf0 hy0 hy1,
    cels_cw_nonpos t c ((y + 1) % 4) ht (by omega) (by omega) (by omega),
    cels_cw_nonpos t c ((y + 3) % 4) ht (by omega) (by omega) (by omega)] at hcond
  revert hcond
  interval_cases c <;> interval_cases y <;> decide

theorem cels_ok_mid (c y t : ℤ) (hc0 : 3 ≤ c) (hc1 : c ≤ 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 3) :
    cels_ok c y t := by
  by_cases ht : t ≤ 0
  · exact cels_ok_nonpos c y t hc0 hc1 hy0 hy1 ht
  · have h := cels_ok_nat c y (by omega) hc1 hy0 hy1 t.toNat
    have e : ((t.toNat : ℕ) : ℤ) = t := by omega
    rw [e] at h
    exact h

theorem cels_ceta_add4 {c : ℤ} (hc : 1 ≤ c) (y : ℤ) : cels_ceta (c + 4) y = cels_ceta c y := by
  unfold cels_ceta zeta1
  have h4 : (c + 4) % 4 = c % 4 := by omega
  have h0 : ¬ (c + 4 = 0 ∧ y = 0) := by omega
  have h0' : ¬ (c = 0 ∧ y = 0) := by omega
  rw [h4, if_neg h0, if_neg h0']

/-- Legality propagates from column `c` to column `c + 4`, `6` steps later. -/
theorem cels_ok_add_c (c y t : ℤ) (hc : 3 ≤ c) (h : cels_ok c y t) :
    cels_ok (c + 4) y (t + 6) := by
  have hf : cels_fold (c + 4 - 1) = (c - 1) + 4 := by unfold cels_fold; split_ifs <;> omega
  have hf' : cels_fold (c - 1) = c - 1 := by unfold cels_fold; split_ifs <;> omega
  have e0 := cels_cw_add (by omega : 2 ≤ c) t y
  have e1 := cels_cw_add (by omega : 2 ≤ c + 1) t y
  have e2 := cels_cw_add (by omega : 2 ≤ c - 1) t y
  have e3 := cels_cw_add (by omega : 2 ≤ c) t ((y + 1) % 4)
  have e4 := cels_cw_add (by omega : 2 ≤ c) t ((y + 3) % 4)
  have e5 := cels_cw_add (by omega : 2 ≤ c) (t + 1) y
  unfold cels_ok cels_cN at h ⊢
  rw [hf, show c + 4 + 1 = (c + 1) + 4 by ring, show t + 6 + 1 = (t + 1) + 6 by ring, e5, e0,
    e1, e2, e3, e4, cels_ceta_add4 (by omega : 1 ≤ c)]
  rw [hf'] at h
  exact h

theorem cels_ok_ge3 (c y t : ℤ) (hc : 3 ≤ c) (hy0 : 0 ≤ y) (hy1 : y ≤ 3) : cels_ok c y t := by
  have key : ∀ q : ℕ, ∀ c₀ : ℤ, 3 ≤ c₀ → c₀ ≤ 6 → ∀ t : ℤ, cels_ok (c₀ + 4 * q) y t := by
    intro q
    induction q with
    | zero =>
      intro c₀ h1 h2 t
      simpa using cels_ok_mid c₀ y t h1 h2 hy0 hy1
    | succ q ih =>
      intro c₀ h1 h2 t
      have h := cels_ok_add_c (c₀ + 4 * q) y (t - 6) (by omega) (ih c₀ h1 h2 (t - 6))
      have e1 : c₀ + 4 * (q : ℤ) + 4 = c₀ + 4 * ((q + 1 : ℕ) : ℤ) := by push_cast; ring
      have e2 : t - 6 + 6 = t := by ring
      rw [e1, e2] at h
      exact h
  have h := key ((c - 3) / 4).toNat (3 + (c - 3) % 4) (by omega) (by omega) t
  have e : (3 + (c - 3) % 4) + 4 * (((c - 3) / 4).toNat : ℤ) = c := by omega
  rw [e] at h
  exact h

/-- **The finite check.**  Every site of the cylinder, at every time `t ≥ 0`, increases
whenever it is unstable for `η̂ + Δ w_t`. -/
theorem cels_ok_all (c y t : ℤ) (hc : 0 ≤ c) (hy0 : 0 ≤ y) (hy1 : y ≤ 3) (ht : 0 ≤ t) :
    cels_ok c y t := by
  by_cases h6 : c ≤ 6
  · have h := cels_ok_nat c y hc h6 hy0 hy1 t.toNat
    have e : ((t.toNat : ℕ) : ℤ) = t := by omega
    rw [e] at h
    exact h
  · exact cels_ok_ge3 c y t (by omega) hy0 hy1

end Exploding
