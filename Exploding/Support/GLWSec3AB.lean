/-
Proposition 5.1 of the paper (generalized last wave): the second bound of
`eq:generalized_lipschitz`, `T̃(x') ≤ T̃(x) + C |x - x'| + (log n)^γ`, and the local bound from the
origin in the form `glws_Loc0`.

When `P(x)` is lit at time `a = T̃(x)`, the site `x` is lit, so (for `|x|` at least the polylogarithmic
path length) a tile of the cluster near `ν(x)` is lit at time `a + Pn^d + ∏ k`
(`glws_tail_tile`); the lighting from that tile reaches the penultimate cluster of `x'` within
`A |j - ν(x')| + B Z^d` more steps (`glws_cluster_lit`).  For `|x|` below the path length the first
bound for `x'` suffices.
-/
import Exploding.Support.GLWSec3AA

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

theorem glws_mnorm_sub_comm (x y : Site d) : mnorm (x - y) = mnorm (y - x) := by
  unfold mnorm
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  exact abs_sub_comm _ _

/-- The triangle inequality for the Manhattan norm of differences. -/
theorem glws_mnorm_tri (a b c : Site d) : mnorm (a - c) ≤ mnorm (a - b) + mnorm (b - c) := by
  unfold mnorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.sub_apply]
  have := abs_sub_le (a i) (b i) (c i)
  exact this

/-- The Manhattan norm of a site is the norm of its difference from the origin. -/
theorem glws_mnorm_sub_zero (a : Site d) : mnorm (a - 0) = mnorm a := by simp

/-- **The second bound** (with the first bound as input for the sites near the origin). -/
theorem glws_second_bound {η : Site d → ℤ} {k : Fin d → ℕ} {Cinf : Set (Site d)} {γp Cch : ℝ}
    (S : glws_Cl d η k Cinf γp Cch) (γE cT : ℝ) (n1 : ℕ)
    (hE : ∀ n : ℕ, n1 ≤ n → 3 ≤ n ∧ (1 : ℝ) ≤ Real.log n ∧
      ((glws_E γp Cch k n : ℕ) : ℝ) ≤ cT * Real.log n ^ γE)
    (nf : ℕ) (hfb : ∀ n : ℕ, nf ≤ n → ∀ x ∈ (cent d n : Set (Site d)), ∃ a : ℕ,
      clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧
        (a : ℝ) ≤ ((glws_LA Cch k : ℝ) + 1) * (mnorm x : ℝ) + Real.log n ^ (γE + 1)) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), ∀ a : ℕ,
      clusterArrival η (0 : Site d) x = (a : ℕ∞) → ∀ x' ∈ (cent d n : Set (Site d)), ∃ b : ℕ,
        clusterArrival η (0 : Site d) x' = (b : ℕ∞) ∧
        (b : ℝ) ≤ (a : ℝ) + ((glws_LA Cch k : ℝ) + 1) * (mnorm (x - x') : ℝ) +
          (((glws_LA Cch k : ℝ) + 1) * (glws_Pn γp (∑ i, k i) d n : ℝ) +
            Real.log n ^ (γE + 1)) := by
  classical
  obtain ⟨n0h, hole⟩ := S.hole
  have hγp : 0 < γp := S.hγp
  obtain ⟨n0t, htail⟩ := glws_tail_tile S.hd η S.hlow S.hhigh k S.hk Cinf S.hgood n0h hole γp
    S.hγp S.hpf
  obtain ⟨n0s, hcl⟩ := glws_cluster_lit S
  have hlast := glws_finite_exploding S.hd η S.hlow S.hhigh k S.hk Cinf S.hinf S.hgood S.hconn
    (0 : Site d)
  have hne : {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)}.Nonempty := hlast
  have hN1 : 1 ≤ waveThreshold η (0 : Site d) := (Nat.sInf_mem hne).1
  set kmax : ℕ := ∑ i, k i with hkmax
  obtain ⟨nP, hnP⟩ := glws_asymp_Pn γp hγp kmax d
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨nL, hnL⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop cT)
  refine ⟨max (max (max n0t n0s) (max n1 nf)) (max nP nL), fun n hn x hx a ha x' hx' => ?_⟩
  have hn0t : n0t ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hn
  have hn0s : n0s ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hn
  have hn1 : n1 ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_left _ _)) hn
  have hnf : nf ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_left _ _)) hn
  have hnP' : nP ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnL' : nL ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hn3, hL1, hEn⟩ := hE n hn1
  obtain ⟨_, hPn⟩ := hnP n hnP'
  have hdpos : 0 < d := by have := S.hd; omega
  have hcTn : cT ≤ Real.log n := hnL n hnL'
  have hLA0 : (0 : ℝ) ≤ (glws_LA Cch k : ℝ) := Nat.cast_nonneg _
  have hx0 : (0 : ℝ) ≤ (mnorm (x - x') : ℝ) := by exact_mod_cast glws_mnorm_nonneg (x - x')
  have hPn0 : (0 : ℝ) ≤ (glws_Pn γp kmax d n : ℝ) := Nat.cast_nonneg _
  by_cases hsmall : (mnorm x).toNat < glws_Pn γp kmax d n
  · -- the first bound for `x'`
    obtain ⟨b, hb, hbb⟩ := hfb n hnf x' hx'
    refine ⟨b, hb, ?_⟩
    have h1 : mnorm x' ≤ mnorm x + mnorm (x - x') := by
      have := glw2_mnorm_sub_le x (x - x')
      have e : x - (x - x') = x' := by abel
      rw [e] at this
      have h2 : mnorm (x - x') = mnorm (x' - x) := glws_mnorm_sub_comm _ _
      linarith [glw2_mnorm_sub_le x' x, glws_mnorm_nonneg (x - x'), h2, this]
    have h1' : (mnorm x' : ℝ) ≤ (mnorm x : ℝ) + (mnorm (x - x') : ℝ) := by exact_mod_cast h1
    have h2 : (mnorm x : ℝ) ≤ (glws_Pn γp kmax d n : ℝ) := by
      have e : (((mnorm x).toNat : ℕ) : ℤ) = mnorm x := Int.toNat_of_nonneg (glws_mnorm_nonneg x)
      have : mnorm x ≤ ((glws_Pn γp kmax d n : ℕ) : ℤ) := by omega
      exact_mod_cast this
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    have hLA1 : (0 : ℝ) ≤ (glws_LA Cch k : ℝ) + 1 := by linarith
    nlinarith [hbb, h1', h2, mul_le_mul_of_nonneg_left h1' hLA1, mul_le_mul_of_nonneg_left h2 hLA1]
  · rw [not_lt] at hsmall
    obtain ⟨m, hm, hmw, hae⟩ := clusterArrival_exists η 0 x (by rw [ha]; exact ENat.coe_ne_top a)
    have hma : m = a := by
      have := hae.symm.trans ha
      exact_mod_cast this
    subst hma
    have hxlit : 0 < wave η (waveThreshold η (0 : Site d)) (0 : Site d) m x :=
      hmw x (centre_mem_penultimateCluster η x)
    obtain ⟨j, hj, hfired, hjν⟩ := htail n hn0t _ hN1 x hx hsmall m hxlit
    -- the scale
    obtain ⟨n'', hn''⟩ : ∃ n'' : ℕ, n'' = glws_Ns d kmax n := ⟨_, rfl⟩
    have hnn'' : n ≤ n'' := by
      rw [hn'']; unfold glws_Ns
      have : n ≤ 3 * n + kmax + 1 := by omega
      exact le_trans this (Nat.le_mul_of_pos_left _ hdpos)
    have hPnn : (glws_Pn γp kmax d n : ℤ) ≤ n := by exact_mod_cast hPn
    have hνx' : mnorm (glws_nu k x') ≤ (d : ℤ) * (n + 1) := glws_mnorm_nu_le k S.hk hx'
    have hνx : mnorm (glws_nu k x) ≤ (d : ℤ) * (n + 1) := glws_mnorm_nu_le k S.hk hx
    have hdn : (d : ℤ) * (n + 1) ≤ (n'' : ℤ) := by
      rw [hn'']; unfold glws_Ns; push_cast
      have : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
      have : (0 : ℤ) ≤ (kmax : ℤ) := Int.natCast_nonneg kmax
      nlinarith
    have hjn : mnorm j ≤ (n'' : ℤ) := by
      have h1 := glws_mnorm_tri j (glws_nu k x) 0
      simp only [glws_mnorm_sub_zero] at h1
      have : mnorm j ≤ (d : ℤ) * (2 * (glws_Pn γp kmax d n : ℤ) + (kmax : ℤ)) + (d : ℤ) * (n + 1) := by
        linarith
      have h4 : (d : ℤ) * (2 * (glws_Pn γp kmax d n : ℤ) + (kmax : ℤ)) + (d : ℤ) * (n + 1) ≤ (n'' : ℤ) := by
        rw [hn'']; unfold glws_Ns; push_cast
        have : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
        nlinarith
      linarith
    have hνn' : mnorm (glws_nu k x') ≤ (n'' : ℤ) := by linarith
    obtain ⟨b, hb, hbb⟩ := hcl n hn0s n'' hnn'' (le_trans hn0s hnn'') x' hx' j hj hjn hνn' _
      hfired
    refine ⟨b, hb, ?_⟩
    -- the distance from `j` to `ν x'`
    have hdist : mnorm (j - glws_nu k x') ≤
        (d : ℤ) * (2 * (glws_Pn γp kmax d n : ℤ) + (kmax : ℤ)) + mnorm (x - x') := by
      have h1 := glws_mnorm_tri j (glws_nu k x) (glws_nu k x')
      have h2 := glws_mnorm_nu_lip k S.hk x x'
      linarith
    set Pn : ℕ := glws_Pn γp kmax d n with hPn_def
    set A'' : ℕ := (mnorm (x - x')).toNat with hA''
    have hA''z : (A'' : ℤ) = mnorm (x - x') := Int.toNat_of_nonneg (glws_mnorm_nonneg _)
    have hdistN : (mnorm (j - glws_nu k x')).toNat ≤ d * (2 * Pn + kmax) + A'' := by
      apply Int.toNat_le.mpr
      push_cast
      linarith
    obtain ⟨A', hA'⟩ : ∃ A' : ℕ, A' = (mnorm (j - glws_nu k x')).toNat := ⟨_, rfl⟩
    rw [← hA'] at hbb hdistN
    have hEn' : glws_E γp Cch k n = Pn ^ d + ∏ l, k l +
        glws_LA Cch k * (d * (2 * Pn + kmax)) + 1 +
        glws_LB Cch k * (glws_Zn γp n'') ^ d := by
      unfold glws_E
      rw [← hkmax, ← hn'']
    have hbN : b ≤ m + glws_E γp Cch k n + glws_LA Cch k * A'' := by
      have h1 := Nat.mul_le_mul_left (glws_LA Cch k) hdistN
      have h2 := Nat.mul_add (glws_LA Cch k) (d * (2 * Pn + kmax)) A''
      rw [hEn']
      linarith [hbb, h1, h2]
    have hbR : (b : ℝ) ≤ (m : ℝ) + (glws_E γp Cch k n : ℝ) + (glws_LA Cch k : ℝ) * (A'' : ℝ) := by
      exact_mod_cast hbN
    have hAR : (A'' : ℝ) = (mnorm (x - x') : ℝ) := by exact_mod_cast hA''z
    rw [hAR] at hbR
    have hLγ : cT * Real.log n ^ γE ≤ Real.log n ^ (γE + 1) := by
      have : Real.log n ^ (γE + 1) = Real.log n ^ γE * Real.log n := by
        rw [Real.rpow_add (by linarith), Real.rpow_one]
      rw [this]
      have h0 : (0 : ℝ) ≤ Real.log n ^ γE := Real.rpow_nonneg (by linarith) _
      nlinarith
    have hPnR : (0 : ℝ) ≤ ((glws_LA Cch k : ℝ) + 1) * (Pn : ℝ) := by positivity
    have hXX : (glws_LA Cch k : ℝ) * (mnorm (x - x') : ℝ) ≤
        ((glws_LA Cch k : ℝ) + 1) * (mnorm (x - x') : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hx0
    linarith [hbR, hEn, hLγ, hPnR, hXX]

/-- **The local bound from the origin on a background carrying the cluster.**  The exponent and the
constant depend only on the side lengths `k`, the path-filling exponent `γp` and the chemical-distance
constant `Cch`, not on the background. -/
theorem glws_loc0_of_cl (hd : 2 ≤ d) (k : Fin d → ℕ) (γp Cch : ℝ) (hγp : 0 < γp) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ (η : Site d → ℤ) (Cinf : Set (Site d)),
      glws_Cl d η k Cinf γp Cch → glws_Loc0 d γ C η := by
  classical
  have hd0 : 0 < d := by omega
  obtain ⟨γE, cT, n1, hγE, hcT, hE⟩ := glws_E_bound γp Cch hγp hd0 k
  set kmax : ℕ := ∑ i, k i with hkmax
  set LA : ℝ := (glws_LA Cch k : ℝ) with hLA
  set cP : ℝ := ((kmax : ℝ) * ((2 : ℝ) ^ ((5 : ℝ) / 2) + 3)) ^ d + (2 : ℝ) ^ γp + 1 with hcP
  set eP : ℝ := (5 : ℝ) / 2 * d + γp with heP
  set eM : ℝ := max (γE + 1) eP with heM
  have hLA0 : (0 : ℝ) ≤ LA := Nat.cast_nonneg _
  have hcP0 : 0 ≤ cP := by rw [hcP]; positivity
  have heP0 : 0 < eP := by rw [heP]; positivity
  refine ⟨eM + 1, LA + 1, by have := le_max_right (γE + 1) eP; linarith, by linarith, ?_⟩
  intro η Cinf S
  obtain ⟨nf, hfb⟩ := glws_first_bound S γE cT n1 hγE hE
  obtain ⟨ns, hsb⟩ := glws_second_bound S γE cT n1 hE nf hfb
  have habs := glws_absorb ((LA + 1) * cP + 1) eM (eM + 1) (by linarith)
  obtain ⟨nA, hnA⟩ := eventually_atTop.mp habs
  refine ⟨fun y => glws_finite_exploding S.hd η S.hlow S.hhigh k S.hk Cinf S.hinf S.hgood S.hconn y,
    max (max nf ns) (max nA n1), fun n hn x hx => ?_⟩
  have hnf : nf ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hns : ns ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnA' : nA ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn1 : n1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hn3, hL1, _⟩ := hE n hn1
  have hL0 : 0 < Real.log n := by linarith
  have hγE1 : γE + 1 ≤ eM := le_max_left _ _
  have heP1 : eP ≤ eM := le_max_right _ _
  have hlA : Real.log n ^ (γE + 1) ≤ Real.log n ^ eM := Real.rpow_le_rpow_of_exponent_le hL1 hγE1
  have hlP : Real.log n ^ eP ≤ Real.log n ^ eM := Real.rpow_le_rpow_of_exponent_le hL1 heP1
  have hlM : Real.log n ^ eM ≤ Real.log n ^ (eM + 1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hab := hnA n hnA'
  have hPn := glws_Pn_le γp hγp kmax d n hn3 hL1
  rw [← hcP, ← heP] at hPn
  -- the polylogarithmic error is at most `(log n)^(eM+1)`
  have hR : (LA + 1) * (glws_Pn γp kmax d n : ℝ) + Real.log n ^ (γE + 1) ≤ Real.log n ^ (eM + 1) := by
    have h1 : (LA + 1) * (glws_Pn γp kmax d n : ℝ) ≤ (LA + 1) * (cP * Real.log n ^ eP) :=
      mul_le_mul_of_nonneg_left hPn (by linarith)
    have h2 : (LA + 1) * (cP * Real.log n ^ eP) ≤ (LA + 1) * cP * Real.log n ^ eM := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hlP (by positivity)
    have h3 : 0 ≤ Real.log n ^ eM := Real.rpow_nonneg hL0.le _
    nlinarith [h1, h2, hlA, hab, h3]
  obtain ⟨a, ha, hax⟩ := hfb n hnf x hx
  refine ⟨a, ha, by linarith, fun x' hx' => ?_⟩
  obtain ⟨b, hb, hbb⟩ := hsb n hns x hx a ha x' hx'
  exact ⟨b, hb, by linarith⟩

end Exploding
