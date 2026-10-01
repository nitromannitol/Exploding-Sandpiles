/-
Support for the far Lipschitz bound of Proposition 3.1 (`eq:lastwave_lipschitz`, second bound),
packet LIP.  Two ingredients that carry a lit good cube of the infinite cluster to a distant site:

* the macroscopic index is `1`-Lipschitz up to an additive constant;
* a lit good cube `Q_k(z0)` of the cluster, with `z0` at macroscopic distance `D` from the cube of
  a site `x`, lights `x` after a time `T1 + k^d C_r (D + 10 ρ) + k (d + ρ) + 2`, where
  `ρ = ⌈(log n)^{5/2}⌉` (a copy of the second half of `pub_core` with the first cube `z0` and the
  distance `D = |z0 - [x]|` as parameters rather than the distance to the origin).
-/
import Exploding.Support.PUBProofF
import Exploding.Support.PCloseProofFinal

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### The macroscopic index is Lipschitz -/

/-- One coordinate of the macroscopic index moves by at most one more than the coordinate. -/
theorem lwcl_macro_sub_abs (k : ℕ) (hk : 1 ≤ k) (x y : Site d) (l : Fin d) :
    |Exploding.macroIdx k x l - Exploding.macroIdx k y l| ≤ |x l - y l| + 1 := by
  obtain ⟨h1, h2⟩ := pclose_macro_bounds k hk x l
  obtain ⟨h3, h4⟩ := pclose_macro_bounds k hk y l
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  set u := Exploding.macroIdx k x l with hu
  set v := Exploding.macroIdx k y l with hv
  set δ := |x l - y l| with hδ
  have hδ0 : 0 ≤ δ := abs_nonneg _
  have hle : x l - y l ≤ δ := le_abs_self _
  have hge : -δ ≤ x l - y l := neg_abs_le _
  rw [abs_le]
  constructor
  · by_contra hcon
    push Not at hcon
    have h5 : (k : ℤ) * (v - u) ≥ (k : ℤ) * (δ + 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    nlinarith
  · by_contra hcon
    push Not at hcon
    have h5 : (k : ℤ) * (u - v) ≥ (k : ℤ) * (δ + 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    nlinarith

/-- The macroscopic indices of two sites are within the distance of the sites plus `d`. -/
theorem lwcl_mnorm_macro_sub_le (k : ℕ) (hk : 1 ≤ k) (x y : Site d) :
    mnorm (Exploding.macroIdx k x - Exploding.macroIdx k y) ≤ mnorm (x - y) + d := by
  unfold mnorm
  calc ∑ l, |(Exploding.macroIdx k x - Exploding.macroIdx k y) l|
      ≤ ∑ l : Fin d, (|(x - y) l| + 1) := Finset.sum_le_sum fun l _ => by
        simpa using lwcl_macro_sub_abs k hk x y l
    _ = ∑ l, |(x - y) l| + d := by
        rw [Finset.sum_add_distrib]; simp

/-! ### A lit cube of the cluster lights every site, at a cost linear in the distance -/

/-- **A lit cube of the infinite cluster lights a site.**  If `Q_k(z0)`, `z0 ∈ C_∞`, is lit at
time `T1`, then every site `x` with `|x| ≤ n` is lit at some time at most
`T1 + k^d C_r (|z0 - [x]| + 10 ρ) + k (d + ρ) + 2`, where `ρ = ⌈(log n)^{5/2}⌉`, provided the
scale `n` leaves room around `z0`.  The site's macroscopic cube is either in the cluster, hence lit
along the chemical path from `z0`, or lies in a hole, which is filled once the cubes of the
cluster around it are lit. -/
theorem lwcl_light_site {η : Site d → ℤ} {N k : ℕ} {Cinf : Set (Site d)} {n0h n0c : ℕ} {Cr : ℝ}
    (S : pub_Setup d η N k Cinf n0h n0c Cr) (z0 : Site d) (hz0 : z0 ∈ Cinf) (T1 : ℕ)
    (hT1 : ∀ u ∈ cube d k, 0 < wave η N (0 : Site d) T1 (u + (k : ℤ) • z0))
    (n : ℕ) (hn0 : n0h ≤ n) (hn1c : n0c ≤ n) (hn3 : 3 ≤ n)
    (hroom : mnorm z0 + 4 * ((Nat.ceil (Real.log n ^ ((5 : ℝ) / 2)) : ℕ) : ℤ) ≤ (n : ℤ))
    (x : Site d) (hx : mnorm x ≤ (n : ℤ)) :
    ∃ τ : ℕ, 1 ≤ τ ∧ 0 < wave η N (0 : Site d) τ x ∧
      (τ : ℝ) ≤ T1 + (k : ℝ) ^ d * Cr * ((mnorm (z0 - Exploding.macroIdx k x) : ℝ) +
        10 * ((Nat.ceil (Real.log n ^ ((5 : ℝ) / 2)) : ℕ) : ℝ)) +
        (k : ℝ) * ((d : ℝ) + ((Nat.ceil (Real.log n ^ ((5 : ℝ) / 2)) : ℕ) : ℝ)) + 2 := by
  classical
  have hd := S.hd
  have hk2 := S.hk
  have hk1 : 1 ≤ k := by omega
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [S.hlow x]
  set L : ℝ := Real.log n with hL
  set ρ : ℕ := Nat.ceil (L ^ ((5 : ℝ) / 2)) with hρdef
  have hL1 : 1 ≤ L := pub_log_ge_one n hn3
  have hρ1 : L ^ ((5 : ℝ) / 2) ≤ (ρ : ℝ) := Nat.le_ceil _
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
  set P : ℝ := (k : ℝ) ^ d * Cr with hP
  have hP0 : 0 ≤ P := by have := S.hCr; positivity
  set i : Site d := Exploding.macroIdx k x with hi
  have hcx : x - (k : ℤ) • i ∈ cube d k := mem_cube_of_macroIdx k hk1 x
  have hxd : ∀ τ : ℕ, (∀ u ∈ cube d k, 0 < wave η N (0 : Site d) τ (u + (k : ℤ) • i)) →
      0 < wave η N (0 : Site d) τ x := by
    intro τ h
    have := h _ hcx
    rwa [sub_add_cancel] at this
  set D : ℝ := (mnorm (z0 - i) : ℝ) with hD
  have hD0 : 0 ≤ D := by rw [hD]; exact_mod_cast pub_mnorm_nonneg (z0 - i)
  have hkd : (0 : ℝ) ≤ (k : ℝ) * ((d : ℝ) + ρ) := by positivity
  by_cases hiC : i ∈ Cinf
  · obtain ⟨τ0, hcov, hτ0⟩ := pub_cinf_cover S z0 hz0 T1 hT1 n hn0 hn1c hn3 hroom i hiC
    refine ⟨τ0 + 1, by omega, ?_, ?_⟩
    · exact lt_of_lt_of_le (hxd τ0 hcov)
        (wave_mono_time η hlow0 hd0 N 0 (Nat.le_succ τ0) x)
    · push_cast
      have h1 : P * (D + 9 * (ρ : ℝ)) ≤ P * (D + 10 * (ρ : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hP0
      have h2 : (τ0 : ℝ) ≤ T1 + P * (D + 9 * (ρ : ℝ)) := hτ0
      nlinarith
  · have hicent : i ∈ (cent d n : Set (Site d)) := by
      intro l
      have hx' : |x l| ≤ (n : ℤ) := le_trans (pub_abs_le_mnorm x l) hx
      exact pub_macro_coord_le k hk2 n (by omega) (x l) hx'
    obtain ⟨hfin, hcard⟩ := S.hhole n hn0 i hicent hiC
    have hr : (componentIn Cinfᶜ i).ncard ≤ ρ := by
      have : ((componentIn Cinfᶜ i).ncard : ℝ) ≤ (ρ : ℝ) := le_trans hcard.le hρ1
      exact_mod_cast this
    set B1 : ℝ := T1 + P * (D + 10 * ρ) with hB1
    have hB10 : 0 ≤ B1 := by positivity
    set τ' : ℕ := Nat.ceil B1 with hτ'
    have hcov' : ∀ b ∈ Cinf, mnorm (b - i) ≤ (ρ : ℤ) →
        ∀ u ∈ cube d k, 0 < wave η N (0 : Site d) τ' (u + (k : ℤ) • b) := by
      intro b hb hbd
      obtain ⟨τb, hcovb, hτb⟩ := pub_cinf_cover S z0 hz0 T1 hT1 n hn0 hn1c hn3 hroom b hb
      have h1 : mnorm (z0 - b) ≤ mnorm (z0 - i) + mnorm (i - b) := pub_mnorm_sub_le z0 i b
      have h2 : mnorm (i - b) = mnorm (b - i) := pub_mnorm_sub_comm i b
      have h3 : (mnorm (z0 - b) : ℝ) ≤ D + ρ := by
        have h4 : mnorm (z0 - b) ≤ mnorm (z0 - i) + ρ := by rw [h2] at h1; linarith
        rw [hD]
        exact_mod_cast h4
      have h5 : (τb : ℝ) ≤ B1 := by
        refine le_trans hτb ?_
        have : P * ((mnorm (z0 - b) : ℝ) + 9 * ρ) ≤ P * (D + 10 * ρ) :=
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
    linarith

end Exploding
