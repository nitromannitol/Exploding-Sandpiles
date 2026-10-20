/-
The linear upper bound `T(n e₁) ≤ 2n + 6` for the arrival times of the counterexample
background of `paper/corrected-arxiv/exploding-corrected-arxiv.tex` Section 6, in every dimension `d ≥ 2`, and the two
consequences used by the frozen proof of `theorem:counterexample`: finiteness of the
arrival time at the low-type points, and the eventual linear bound on `T(n)/n`.
-/
import Exploding.Support.CELow3

namespace Exploding

open LatticeProb Filter

/-- **Upper bound.**  The arrival time of the explosion of `ceEta d` at `m e₁` is finite
and at most `2 m + 6`. -/
theorem cel_upper (d : ℕ) (hd : 2 ≤ d) (m : ℕ) :
    ∃ T : ℕ, arrival (ceEta d) ((m : ℤ) • e1 d) = (T : ℕ∞) ∧ T ≤ 2 * m + 6 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  have hsub := cel_subsol (fun x => ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x)
    (cel_p (n := n)) (fun x => (cel_p_zero x).le) (fun t x => cel_hstep t x)
  have hch := ((cel_chk_all (m : ℤ) 0).1 (cel_in1_axis m)).1
  have hbd := cel_t1_axis m
  have hTcast : (((cel_t1 (m : ℤ) 0).toNat : ℕ) : ℤ) = cel_t1 (m : ℤ) 0 :=
    Int.toNat_of_nonneg (by omega)
  have hT1 : 1 ≤ (cel_t1 (m : ℤ) 0).toNat := by omega
  have hpos : 0 < podo (fun x => ceEta (n + 2) x + 3 * dirac (0 : Site (n + 2)) x)
      (cel_t1 (m : ℤ) 0).toNat ((m : ℤ) • e1 (n + 2)) := by
    have h1 := hsub (cel_t1 (m : ℤ) 0).toNat ((m : ℤ) • e1 (n + 2))
    have h2 : 1 ≤ cel_p (cel_t1 (m : ℤ) 0).toNat ((m : ℤ) • e1 (n + 2)) := by
      unfold cel_p
      rw [cel_e1_0, cel_e1_1, cel_rho_e1]
      unfold cel_val
      rw [if_pos rfl]
      unfold cel_Q cel_f1
      have hc : cel_in1 (m : ℤ) 0 ∧ cel_t1 (m : ℤ) 0 ≤ (((cel_t1 (m : ℤ) 0).toNat : ℕ) : ℤ) :=
        ⟨cel_in1_axis m, by omega⟩
      rw [if_pos hc]
      have h3 : (0 : ℤ) ≤ cel_f2 (((cel_t1 (m : ℤ) 0).toNat : ℕ) : ℤ) (m : ℤ) 0 := by
        unfold cel_f2
        split <;> norm_num
      linarith
    linarith
  have hle := aux_ce_arrival_le (n + 2) hd m _ hT1 hpos
  have hne := aux_ce_arrival_finite_of_pos (n + 2) hd m _ hT1 hpos
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.mp hne
  refine ⟨T, hT.symm, ?_⟩
  rw [← hT] at hle
  have := ENat.coe_le_coe.mp hle
  omega

/-- Finiteness of the arrival time at the low-type row-`0` points (`hLow` of the frozen
proof of `theorem:counterexample`). -/
theorem cel_low (d : ℕ) (hd : 2 ≤ d) : ∀ n : ℕ, n % 4 = 0 ∨ n % 4 = 3 →
    arrival (ceEta d) ((n : ℤ) • e1 d) ≠ ⊤ := by
  intro n _
  obtain ⟨T, hT, _⟩ := cel_upper d hd n
  rw [hT]
  exact ENat.coe_ne_top T

/-- The eventual linear bound on `T(n)/n` (`hBdd` of the frozen proof of
`theorem:counterexample`). -/
theorem cel_bdd (d : ℕ) (hd : 2 ≤ d) : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ) ≤ C := by
  refine ⟨8, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨T, hT, hle⟩ := cel_upper d hd n
  rw [hT, ENat.toNat_coe]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hn']
  have h1 : (T : ℝ) ≤ 2 * n + 6 := by exact_mod_cast hle
  have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end Exploding
