/-
Proposition 5.1 of the paper (generalized last wave): the first bound of
`eq:generalized_lipschitz`, `T̃(x) ≤ C |x| + (log n)^γ`.

The last wave lights a tile `j*` of the cluster at a finite time `τ0` (`glws_first_lit`); from it
the penultimate cluster of every `x ∈ [-n,n]^d` is lit within `A |j* - ν(x)| + B Z^d` more steps
(`glws_cluster_lit`), which is at most `A |x| + (log n)^γ` for `n` large.
-/
import Exploding.Support.GLWSec3Z

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

theorem glws_mnorm_nonneg (x : Site d) : 0 ≤ mnorm x := by
  unfold mnorm; exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- A site of `cent d n` has norm at most `d n`. -/
theorem glws_mnorm_cent {n : ℕ} {x : Site d} (hx : x ∈ cent d n) : mnorm x ≤ (d : ℤ) * n :=
  glws_mnorm_le_coord x n hx

/-- The macroscopic site of a site of `cent d n` has norm at most `d (n + 1)`. -/
theorem glws_mnorm_nu_le (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) {n : ℕ} {x : Site d}
    (hx : x ∈ cent d n) : mnorm (glws_nu k x) ≤ (d : ℤ) * (n + 1) := by
  apply glws_mnorm_le_coord
  intro m
  have h1 := glws_nu_abs k hk x m
  have h2 := hx m
  linarith

/-- The macroscopic site of a site has norm at most the norm of the site plus `d`. -/
theorem glws_mnorm_nu_le' (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (x : Site d) :
    mnorm (glws_nu k x) ≤ mnorm x + d := by
  unfold mnorm
  calc ∑ m, |glws_nu k x m| ≤ ∑ m, (|x m| + 1) :=
        Finset.sum_le_sum fun m _ => glws_nu_abs k hk x m
    _ = ∑ m, |x m| + d := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp

/-- **The first bound.** -/
theorem glws_first_bound {η : Site d → ℤ} {k : Fin d → ℕ} {Cinf : Set (Site d)} {γp Cch : ℝ}
    (S : glws_Cl d η k Cinf γp Cch) (γE cT : ℝ) (n1 : ℕ) (hγE : 0 < γE)
    (hE : ∀ n : ℕ, n1 ≤ n → 3 ≤ n ∧ (1 : ℝ) ≤ Real.log n ∧
      ((glws_E γp Cch k n : ℕ) : ℝ) ≤ cT * Real.log n ^ γE) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), ∃ a : ℕ,
      clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧
        (a : ℝ) ≤ ((glws_LA Cch k : ℝ) + 1) * (mnorm x : ℝ) + Real.log n ^ (γE + 1) := by
  classical
  obtain ⟨n0h, hole⟩ := S.hole
  obtain ⟨j, hj, τ0, hfired0⟩ := glws_first_lit S.hd η S.hlow S.hhigh k S.hk Cinf S.hinf S.hgood
    S.hconn n0h hole γp S.hγp S.hpf
  obtain ⟨n0s, hcl⟩ := glws_cluster_lit S
  set kmax : ℕ := ∑ i, k i with hkmax
  set J : ℕ := (mnorm j).toNat with hJ
  set cη : ℕ := τ0 + glws_LA Cch k * (J + d) + 1 with hcη
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨nL, hnL⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop ((cη : ℝ) + cT + 1))
  refine ⟨max (max (max n0s n1) (max nL J)) 3, fun n hn x hx => ?_⟩
  have hn0s : n0s ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hn
  have hn1 : n1 ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hn
  have hnL' : nL ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_left _ _)) hn
  have hnJ : J ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_left _ _)) hn
  obtain ⟨hn3, hL1, hEn⟩ := hE n hn1
  have hdpos : 0 < d := by have := S.hd; omega
  -- the scale
  obtain ⟨n'', hn''⟩ : ∃ n'' : ℕ, n'' = glws_Ns d kmax n := ⟨_, rfl⟩
  have hnn'' : n ≤ n'' := by
    rw [hn'']; unfold glws_Ns
    have : n ≤ 3 * n + kmax + 1 := by omega
    exact le_trans this (Nat.le_mul_of_pos_left _ hdpos)
  have hxn : mnorm x ≤ (d : ℤ) * n := glws_mnorm_cent hx
  have hνn : mnorm (glws_nu k x) ≤ (n'' : ℤ) := by
    have h1 := glws_mnorm_nu_le k S.hk hx
    have h2 : (d : ℤ) * (n + 1) ≤ (n'' : ℤ) := by
      rw [hn'']; unfold glws_Ns
      push_cast
      have : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
      have : (0 : ℤ) ≤ (kmax : ℤ) := Int.natCast_nonneg kmax
      nlinarith
    linarith
  have hjn : mnorm j ≤ (n'' : ℤ) := by
    have h1 : mnorm j ≤ (n : ℤ) := by
      have e : (J : ℤ) = mnorm j := Int.toNat_of_nonneg (glws_mnorm_nonneg j)
      have : (J : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnJ
      linarith
    have h2 : (n : ℤ) ≤ (n'' : ℤ) := by exact_mod_cast hnn''
    linarith
  obtain ⟨a, ha, hab⟩ := hcl n hn0s n'' hnn'' (le_trans hn0s hnn'') x hx j hj hjn hνn τ0 hfired0
  refine ⟨a, ha, ?_⟩
  -- the distance from `j` to `ν x`
  have hdist : mnorm (j - glws_nu k x) ≤ mnorm j + mnorm (glws_nu k x) := glw2_mnorm_sub_le _ _
  have hnuc := glws_mnorm_nu_le' k S.hk x
  have hjJ : (J : ℤ) = mnorm j := Int.toNat_of_nonneg (glws_mnorm_nonneg j)
  have hdistnn : 0 ≤ mnorm (j - glws_nu k x) := glws_mnorm_nonneg _
  set A : ℕ := (mnorm (j - glws_nu k x)).toNat with hA
  have hAz : (A : ℤ) = mnorm (j - glws_nu k x) := Int.toNat_of_nonneg hdistnn
  have hAR : (A : ℝ) ≤ (J : ℝ) + (mnorm x : ℝ) + d := by
    have : (A : ℤ) ≤ (J : ℤ) + mnorm x + d := by linarith
    exact_mod_cast this
  -- the time bound
  have habR : (a : ℝ) ≤ (τ0 : ℝ) + (glws_LA Cch k : ℝ) * (A : ℝ) +
      (glws_LB Cch k : ℝ) * ((glws_Zn γp n'' : ℕ) : ℝ) ^ d + 1 := by exact_mod_cast hab
  have hLB : (glws_LB Cch k : ℝ) * ((glws_Zn γp n'' : ℕ) : ℝ) ^ d ≤ (glws_E γp Cch k n : ℝ) := by
    have : glws_LB Cch k * (glws_Zn γp n'') ^ d ≤ glws_E γp Cch k n := by
      unfold glws_E
      rw [← hkmax, ← hn'']
      exact Nat.le_add_left _ _
    exact_mod_cast this
  have hLA0 : (0 : ℝ) ≤ (glws_LA Cch k : ℝ) := Nat.cast_nonneg _
  have hx0 : (0 : ℝ) ≤ (mnorm x : ℝ) := by exact_mod_cast glws_mnorm_nonneg x
  have hLA := mul_le_mul_of_nonneg_left hAR hLA0
  have hnL'' := hnL n hnL'
  have hLγ : (1 : ℝ) ≤ Real.log n ^ γE := Real.one_le_rpow hL1 hγE.le
  have hpow : Real.log n ^ (γE + 1) = Real.log n ^ γE * Real.log n := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have hcηR : (cη : ℝ) = (τ0 : ℝ) + (glws_LA Cch k : ℝ) * ((J : ℝ) + d) + 1 := by
    rw [hcη]; push_cast; ring
  have hcη0 : (0 : ℝ) ≤ (cη : ℝ) := Nat.cast_nonneg _
  nlinarith [habR, hLB, hLA, hEn, hnL'', hLγ, hpow, hcηR, hx0, hcη0]

end Exploding
