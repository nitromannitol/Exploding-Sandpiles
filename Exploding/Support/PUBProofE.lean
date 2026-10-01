/-
Support for Lemma 3.6 of `paper/exploding.tex`: the deterministic core.  On a
background carrying a non-stabilizing wave, an infinite cluster of good cubes with small holes and a
linear chemical distance, the wave is positive at every site `x` by a time at most
`K + k^d C |x| + C' (log n)^3`, for all large `n` and `|x| ≤ n`.
-/
import Exploding.Support.PUBProofD

namespace Exploding

open LatticeProb

variable {d : ℕ}

theorem pub_rho_le (n : ℕ) (hn : 3 ≤ n) :
    ((Nat.ceil (Real.log n ^ ((5 : ℝ) / 2)) : ℕ) : ℝ) ≤ Real.log n ^ 3 + 1 := by
  have hL1 := pub_log_ge_one n hn
  have h0 : (0 : ℝ) ≤ Real.log n ^ ((5 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have := Nat.ceil_lt_add_one h0
  have h2 := pub_log_pow_le (Real.log n) hL1
  linarith

theorem pub_core {η : Site d → ℤ} {N k : ℕ} {Cinf : Set (Site d)} {n0h n0c : ℕ} {Cr : ℝ}
    (S : pub_Setup d η N k Cinf n0h n0c Cr) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
      ∃ τ : ℕ, 1 ≤ τ ∧ 0 < wave η N (0 : Site d) τ x ∧
        (τ : ℝ) ≤ K + (k : ℝ) ^ d * Cr * (mnorm x : ℝ) +
          2 * (10 * ((k : ℝ) ^ d * Cr) + k) * Real.log n ^ 3 := by
  classical
  have hd := S.hd
  have hk2 := S.hk
  have hk1 : 1 ≤ k := by omega
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [S.hlow x]
  -- the first lit cube of the cluster
  obtain ⟨N0, hN0⟩ := pub_eventually_room 3 (by norm_num)
  set nstar : ℕ := max (max N0 n0h) 3 with hnstar
  have hn3s : 3 ≤ nstar := le_max_right _ _
  have hN0s : N0 ≤ nstar := le_trans (le_max_left _ _) (le_max_left _ _)
  have hn0s : n0h ≤ nstar := le_trans (le_max_right _ _) (le_max_left _ _)
  have hρs : ((Nat.ceil (Real.log nstar ^ ((5 : ℝ) / 2)) : ℕ) : ℤ) + 2 ≤ (nstar : ℤ) := by
    have hL1 := pub_log_ge_one nstar hn3s
    have h1 := pub_rho_le nstar hn3s
    have h2 := hN0 nstar hN0s
    have hL3 : 1 ≤ Real.log nstar ^ 3 := one_le_pow₀ hL1
    have : ((Nat.ceil (Real.log nstar ^ ((5 : ℝ) / 2)) : ℕ) : ℝ) + 2 ≤ (nstar : ℝ) := by
      nlinarith
    exact_mod_cast this
  obtain ⟨z0, hz0, T1, hT1⟩ := pub_initial_cube S.hd η S.hlow S.hhigh N S.hN S.hns k hk1 Cinf
    S.hCinf n0h S.hhole nstar hn0s hρs
  -- constants
  set P : ℝ := (k : ℝ) ^ d * Cr with hP
  have hP0 : 0 ≤ P := by have := S.hCr; positivity
  set Z : ℤ := mnorm z0 with hZ
  have hZ0 : (0 : ℤ) ≤ Z := pub_mnorm_nonneg z0
  have hZR : (0 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ0
  refine ⟨T1 + 2 + P * (Z + d) + k * d, by positivity, ?_⟩
  obtain ⟨N1, hN1⟩ := pub_eventually_room ((Z : ℝ) + 4) (by linarith)
  refine ⟨max (max N1 (max n0h n0c)) 3, fun n hn x hx => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn0 : n0h ≤ n :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hn
  have hn1c : n0c ≤ n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hn
  set L : ℝ := Real.log n with hL
  set ρ : ℕ := Nat.ceil (L ^ ((5 : ℝ) / 2)) with hρdef
  have hL1 : 1 ≤ L := pub_log_ge_one n hn3
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have hρ1 : L ^ ((5 : ℝ) / 2) ≤ (ρ : ℝ) := Nat.le_ceil _
  have hρ3 : (ρ : ℝ) ≤ L ^ 3 + 1 := pub_rho_le n hn3
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
  have hρ2L : (ρ : ℝ) ≤ 2 * L ^ 3 := by linarith
  have hroomR : (Z : ℝ) + 4 * (ρ : ℝ) ≤ (n : ℝ) := by
    have h1 := hN1 n hnN1
    nlinarith
  have hroom : mnorm z0 + 4 * (ρ : ℤ) ≤ (n : ℤ) := by
    have : ((Z + 4 * (ρ : ℤ) : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  -- the macroscopic cube of `x`
  set i : Site d := Exploding.macroIdx k x with hi
  have hcx : x - (k : ℤ) • i ∈ cube d k := mem_cube_of_macroIdx k hk1 x
  have hxd : ∀ τ : ℕ, (∀ u ∈ cube d k, 0 < wave η N (0 : Site d) τ (u + (k : ℤ) • i)) →
      0 < wave η N (0 : Site d) τ x := by
    intro τ h
    have := h _ hcx
    rwa [sub_add_cancel] at this
  have hmi : mnorm i ≤ mnorm x + d := by
    calc mnorm i = ∑ l, |i l| := rfl
      _ ≤ ∑ l, (|x l| + 1) := Finset.sum_le_sum fun l _ => pub_macro_abs_le k hk1 (x l)
      _ = mnorm x + d := by simp [mnorm, Finset.sum_add_distrib]
  have hzi : mnorm (z0 - i) ≤ Z + mnorm x + d := by
    have := pub_mnorm_sub_le z0 0 i
    rw [sub_zero, zero_sub, pub_mnorm_neg] at this
    linarith
  have hziR : (mnorm (z0 - i) : ℝ) ≤ Z + (mnorm x : ℝ) + d := by exact_mod_cast hzi
  by_cases hiC : i ∈ Cinf
  · obtain ⟨τ0, hcov, hτ0⟩ := pub_cinf_cover S z0 hz0 T1 hT1 n hn0 hn1c hn3 hroom i hiC
    refine ⟨τ0 + 1, by omega, ?_, ?_⟩
    · exact lt_of_lt_of_le (hxd τ0 hcov)
        (wave_mono_time η hlow0 hd0 N 0 (Nat.le_succ τ0) x)
    · push_cast
      have h1 : P * (mnorm (z0 - i) : ℝ) ≤ P * (Z + (mnorm x : ℝ) + d) :=
        mul_le_mul_of_nonneg_left hziR hP0
      have h2 : P * (9 * (ρ : ℝ)) ≤ P * (18 * L ^ 3) :=
        mul_le_mul_of_nonneg_left (by linarith) hP0
      have h3 : (0 : ℝ) ≤ (k : ℝ) * d := by positivity
      have h4 : (0 : ℝ) ≤ 2 * (k : ℝ) * L ^ 3 := by positivity
      nlinarith
  · -- `i` lies in a hole
    have hicent : i ∈ (cent d n : Set (Site d)) := by
      intro l
      have hx' : |x l| ≤ (n : ℤ) := le_trans (pub_abs_le_mnorm x l) hx
      exact pub_macro_coord_le k hk2 n (by omega) (x l) hx'
    obtain ⟨hfin, hcard⟩ := S.hhole n hn0 i hicent hiC
    have hr : (componentIn Cinfᶜ i).ncard ≤ ρ := by
      have : ((componentIn Cinfᶜ i).ncard : ℝ) ≤ (ρ : ℝ) := le_trans hcard.le hρ1
      exact_mod_cast this
    set B1 : ℝ := T1 + P * (Z + (mnorm x : ℝ) + d + 10 * ρ) with hB1
    have hB10 : 0 ≤ B1 := by
      have : (0 : ℝ) ≤ (mnorm x : ℝ) := by exact_mod_cast pub_mnorm_nonneg x
      positivity
    set τ' : ℕ := Nat.ceil B1 with hτ'
    have hcov' : ∀ b ∈ Cinf, mnorm (b - i) ≤ (ρ : ℤ) →
        ∀ u ∈ cube d k, 0 < wave η N (0 : Site d) τ' (u + (k : ℤ) • b) := by
      intro b hb hbd
      obtain ⟨τb, hcovb, hτb⟩ := pub_cinf_cover S z0 hz0 T1 hT1 n hn0 hn1c hn3 hroom b hb
      have h1 : mnorm (z0 - b) ≤ mnorm (z0 - i) + mnorm (i - b) := pub_mnorm_sub_le z0 i b
      have h2 : mnorm (i - b) = mnorm (b - i) := pub_mnorm_sub_comm i b
      have h3 : (mnorm (z0 - b) : ℝ) ≤ Z + (mnorm x : ℝ) + d + ρ := by
        have h4 : mnorm (z0 - b) ≤ Z + mnorm x + d + ρ := by rw [h2] at h1; linarith
        exact_mod_cast h4
      have h5 : (τb : ℝ) ≤ B1 := by
        refine le_trans hτb ?_
        have : P * ((mnorm (z0 - b) : ℝ) + 9 * ρ) ≤ P * (Z + (mnorm x : ℝ) + d + 10 * ρ) :=
          mul_le_mul_of_nonneg_left (by linarith) hP0
        linarith
      have h6 : τb ≤ τ' := by
        have : (τb : ℝ) ≤ (τ' : ℝ) := le_trans h5 (Nat.le_ceil B1)
        exact_mod_cast this
      exact pub_cover_mono η hlow0 hd0 N k 0 b h6 hcovb
    have hlit := pub_hole_lit S.hd η S.hlow N S.hN k hk1 Cinf x hiC hfin ρ hr τ' hcov'
    refine ⟨τ' + k * (d + ρ) + 1, by omega, hlit, ?_⟩
    have hceil := Nat.ceil_lt_add_one hB10
    push_cast
    have h1 : P * (10 * (ρ : ℝ)) ≤ P * (20 * L ^ 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hP0
    have h2 : (k : ℝ) * ρ ≤ (k : ℝ) * (2 * L ^ 3) :=
      mul_le_mul_of_nonneg_left hρ2L (by positivity)
    have h3 : (0 : ℝ) ≤ (k : ℝ) * d := by positivity
    nlinarith

end Exploding
