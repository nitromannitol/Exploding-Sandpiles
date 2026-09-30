/-
Support for Lemma 3.6 of `paper/exploding.tex` (packet PUB): the logarithmic bookkeeping and the
time to light a cube of the infinite cluster, through the chemical distance of Proposition 2.2.
-/
import Exploding.Support.PUBProofC

namespace Exploding

open LatticeProb Filter

variable {d : ℕ}

/-! ### Logarithms -/

theorem pub_log_ge_one (n : ℕ) (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  have h1 : Real.exp 1 ≤ (n : ℝ) := by
    have h2 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have := Real.exp_one_lt_d9
    linarith
  have := Real.log_le_log (Real.exp_pos 1) h1
  rwa [Real.log_exp] at this

theorem pub_log_sq_le (L : ℝ) (hL : 1 ≤ L) : L ^ (2 : ℕ) ≤ L ^ ((5 : ℝ) / 2) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

theorem pub_log_pow_le (L : ℝ) (hL : 1 ≤ L) : L ^ ((5 : ℝ) / 2) ≤ L ^ (3 : ℕ) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

/-- Eventually a polylogarithm fits below `n`. -/
theorem pub_eventually_room (K : ℝ) (hK : 0 ≤ K) :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → K * Real.log n ^ 3 + K ≤ n := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 3)).def (c := 1 / (2 * K + 2)) (by positivity)
  rw [Filter.eventually_atTop] at h
  obtain ⟨X, hX⟩ := h
  refine ⟨max (Nat.ceil X) (Nat.ceil (2 * K) + 1), fun n hn => ?_⟩
  have hnX : X ≤ (n : ℝ) := le_trans (Nat.le_ceil X) (by exact_mod_cast le_trans (le_max_left _ _) hn)
  have hnK : 2 * K ≤ (n : ℝ) := by
    have : Nat.ceil (2 * K) + 1 ≤ n := le_trans (le_max_right _ _) hn
    have h1 : 2 * K ≤ (Nat.ceil (2 * K) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (2 * K) : ℝ) + 1 ≤ n := by exact_mod_cast this
    linarith
  have h3 := hX (n : ℝ) hnX
  simp only [id, Real.norm_eq_abs] at h3
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_of_nonneg hn0] at h3
  have hpow : Real.log n ^ 3 ≤ (1 / (2 * K + 2)) * n := by
    refine le_trans (le_abs_self _) h3
  have hK2 : K * ((1 / (2 * K + 2)) * n) ≤ n / 2 := by
    rw [show K * ((1 / (2 * K + 2)) * n) = (K / (2 * K + 2)) * n by ring]
    have : K / (2 * K + 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hpow hK]

/-- Eventually the fourth power of the logarithm beats a polylogarithmic bound. -/
theorem pub_eventually_final (K : ℝ) (hK : 0 ≤ K) :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → K + K * Real.log n ^ 3 ≤ Real.log n ^ (4 : ℕ) := by
  refine ⟨Nat.ceil (Real.exp (2 * K + 1)), fun n hn => ?_⟩
  have h1 : Real.exp (2 * K + 1) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have h2 : 2 * K + 1 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hL1 : 1 ≤ Real.log n := by linarith
  have hL3 : 1 ≤ Real.log n ^ 3 := one_le_pow₀ hL1
  have h3 : K ≤ K * Real.log n ^ 3 := by nlinarith
  have h4 : 2 * K * Real.log n ^ 3 ≤ Real.log n * Real.log n ^ 3 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc K + K * Real.log n ^ 3 ≤ 2 * K * Real.log n ^ 3 := by nlinarith
    _ ≤ Real.log n * Real.log n ^ 3 := h4
    _ = Real.log n ^ (4 : ℕ) := by ring

/-! ### The setting -/

/-- The data of the almost sure event of Proposition 2.2, together with a non-stabilizing wave. -/
structure pub_Setup (d : ℕ) (η : Site d → ℤ) (N k : ℕ) (Cinf : Set (Site d)) (n0h n0c : ℕ)
    (Cr : ℝ) : Prop where
  hd : 2 ≤ d
  hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x
  hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1
  hN : 1 ≤ N
  hns : ¬ WaveStabilizable η N (0 : Site d)
  hk : 2 ≤ k
  hCinf : IsInfiniteConnectedGoodSet η k Cinf
  hhole : ∀ n : ℕ, n0h ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
    (componentIn Cinfᶜ x).Finite ∧
      ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)
  hCr : 0 < Cr
  hchem : ∀ n : ℕ, n0c ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf, mnorm x ≤ (n : ℤ) →
    Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
      ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧ (m : ℝ) ≤ Cr * (mnorm (x - y) : ℝ)

/-- **One leg of the chemical distance.**  A lit cube of the cluster lights a far cube of the
cluster after `k^d` steps per edge of a shortest path. -/
theorem pub_cover_chem {η : Site d → ℤ} {N k : ℕ} {Cinf : Set (Site d)} {n0h n0c : ℕ} {Cr : ℝ}
    (S : pub_Setup d η N k Cinf n0h n0c Cr) (x y : Site d) (hx : x ∈ Cinf) (hy : y ∈ Cinf)
    (n : ℕ) (hn : n0c ≤ n) (hxn : mnorm x ≤ (n : ℤ))
    (hfar : Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ)) (t : ℕ)
    (ht : ∀ u ∈ cube d k, 0 < wave η N (0 : Site d) t (u + (k : ℤ) • x)) :
    ∃ m : ℕ, (m : ℝ) ≤ Cr * (mnorm (x - y) : ℝ) ∧
      ∀ u ∈ cube d k, 0 < wave η N (0 : Site d) (t + m * k ^ d) (u + (k : ℤ) • y) := by
  obtain ⟨m, hm, hbound⟩ := S.hchem n hn x hx y hy hxn hfar
  obtain ⟨hx', hy', p, hp⟩ := pub_walk_of_chemDist Cinf x y m hm
  have hlow0 : ∀ z, 0 ≤ η z := fun z => by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast S.hd
    linarith [S.hlow z]
  refine ⟨m, hbound, ?_⟩
  have := pub_cover_walk S.hd η hlow0 S.hhigh N k (by have := S.hk; omega) S.hN 0 Cinf
    S.hCinf.2.1 p t ht
  rw [hp] at this
  exact this

/-- **Every cube of the infinite cluster is lit soon.**  From a lit cube `Q_k(z0)` of the cluster,
a cube `Q_k(b)` of the cluster is lit after `k^d` steps per edge of a chemical path.  A cube within
`(log n)^2` of `z0` is reached through a cube of the cluster found at distance between `3ρ` and
`4ρ` from `z0` on a coordinate ray, where `ρ = ⌈(log n)^{5/2}⌉`. -/
theorem pub_cinf_cover {η : Site d → ℤ} {N k : ℕ} {Cinf : Set (Site d)} {n0h n0c : ℕ} {Cr : ℝ}
    (S : pub_Setup d η N k Cinf n0h n0c Cr) (z0 : Site d) (hz0 : z0 ∈ Cinf) (T1 : ℕ)
    (hT1 : ∀ u ∈ cube d k, 0 < wave η N (0 : Site d) T1 (u + (k : ℤ) • z0))
    (n : ℕ) (hn0 : n0h ≤ n) (hn1 : n0c ≤ n) (hn3 : 3 ≤ n)
    (hroom : mnorm z0 + 4 * ((Nat.ceil (Real.log n ^ ((5 : ℝ) / 2)) : ℕ) : ℤ) ≤ (n : ℤ))
    (b : Site d) (hb : b ∈ Cinf) :
    ∃ τ : ℕ, (∀ u ∈ cube d k, 0 < wave η N (0 : Site d) τ (u + (k : ℤ) • b)) ∧
      (τ : ℝ) ≤ T1 + (k : ℝ) ^ d * Cr * ((mnorm (z0 - b) : ℝ) +
        9 * ((Nat.ceil (Real.log n ^ ((5 : ℝ) / 2)) : ℕ) : ℝ)) := by
  set L : ℝ := Real.log n with hLdef
  set ρ : ℕ := Nat.ceil (L ^ ((5 : ℝ) / 2)) with hρdef
  have hL1 : 1 ≤ L := pub_log_ge_one n hn3
  have hρ1 : L ^ ((5 : ℝ) / 2) ≤ (ρ : ℝ) := Nat.le_ceil _
  have hρ2 : L ^ (2 : ℕ) ≤ (ρ : ℝ) := le_trans (pub_log_sq_le L hL1) hρ1
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
  have hzn : mnorm z0 ≤ (n : ℤ) := by
    have : (0 : ℤ) ≤ 4 * (ρ : ℤ) := by positivity
    linarith
  have hkd : (0 : ℝ) ≤ (k : ℝ) ^ d * Cr := by
    have := S.hCr
    positivity
  have hnorm0 : (0 : ℝ) ≤ (mnorm (z0 - b) : ℝ) := by exact_mod_cast pub_mnorm_nonneg (z0 - b)
  by_cases hfar : L ^ (2 : ℕ) ≤ (mnorm (z0 - b) : ℝ)
  · obtain ⟨m, hm, hcov⟩ := pub_cover_chem S z0 b hz0 hb n hn1 hzn hfar T1 hT1
    refine ⟨T1 + m * k ^ d, hcov, ?_⟩
    push_cast
    have : (m : ℝ) * (k : ℝ) ^ d ≤ Cr * (mnorm (z0 - b) : ℝ) * (k : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    nlinarith
  · push Not at hfar
    have hd0 : 0 < d := by have := S.hd; omega
    set i0 : Fin d := ⟨0, hd0⟩ with hi0
    obtain ⟨v, hva, hvb, hvM⟩ := aux_penultimate_overlap_line_meets_cinf Cinf n0h S.hhole n hn0
      z0 i0 (z0 i0 + 3 * (ρ : ℤ)) (z0 i0 + 4 * (ρ : ℤ))
      (by
        have : ((z0 i0 + 4 * (ρ : ℤ) - (z0 i0 + 3 * (ρ : ℤ)) : ℤ) : ℝ) = (ρ : ℝ) := by
          push_cast; ring
        rw [this]
        exact hρ1)
      (fun v hv hv' l => by
        by_cases hl : l = i0
        · simp only [hl, if_true]
          have h1 := pub_abs_le_mnorm z0 i0
          have h2 : (0 : ℤ) ≤ (ρ : ℤ) := Nat.cast_nonneg ρ
          have h3 := abs_le.mp (le_refl |z0 i0|)
          rw [abs_le]
          constructor <;> linarith [neg_abs_le (z0 i0), le_abs_self (z0 i0)]
        · simp only [hl, if_false]
          exact le_trans (pub_abs_le_mnorm z0 l) hzn)
    set M : Site d := fun j => if j = i0 then v else z0 j with hMdef
    have hMn : mnorm (M - z0) = |v - z0 i0| := pub_mnorm_update_sub z0 i0 v
    have hMn' : 3 * (ρ : ℤ) ≤ mnorm (M - z0) ∧ mnorm (M - z0) ≤ 4 * (ρ : ℤ) := by
      rw [hMn, abs_of_nonneg (by linarith)]
      constructor <;> linarith
    have hMnR : 3 * (ρ : ℝ) ≤ (mnorm (M - z0) : ℝ) ∧ (mnorm (M - z0) : ℝ) ≤ 4 * (ρ : ℝ) := by
      constructor
      · exact_mod_cast hMn'.1
      · exact_mod_cast hMn'.2
    have hMn2 : mnorm (z0 - M) = mnorm (M - z0) := pub_mnorm_sub_comm z0 M
    -- first leg
    have hfar1 : L ^ (2 : ℕ) ≤ (mnorm (z0 - M) : ℝ) := by
      rw [hMn2]; linarith [hMnR.1]
    obtain ⟨m1, hm1, hcov1⟩ := pub_cover_chem S z0 M hz0 hvM n hn1 hzn hfar1 T1 hT1
    -- second leg
    have hMnorm : mnorm M ≤ (n : ℤ) := by
      have := pub_mnorm_add_le z0 (M - z0)
      rw [show z0 + (M - z0) = M by abel] at this
      linarith [hMn'.2]
    have hb1 := pub_mnorm_sub_le M b z0
    have hb2 : mnorm (b - z0) = mnorm (z0 - b) := pub_mnorm_sub_comm b z0
    have hb1R : (mnorm (M - z0) : ℝ) ≤ (mnorm (M - b) : ℝ) + (mnorm (z0 - b) : ℝ) := by
      rw [hb2] at hb1
      exact_mod_cast hb1
    have hfar2 : L ^ (2 : ℕ) ≤ (mnorm (M - b) : ℝ) := by
      linarith [hMnR.1]
    obtain ⟨m2, hm2, hcov2⟩ := pub_cover_chem S M b hvM hb n hn1 hMnorm hfar2
      (T1 + m1 * k ^ d) hcov1
    refine ⟨T1 + m1 * k ^ d + m2 * k ^ d, hcov2, ?_⟩
    have hb3 := pub_mnorm_sub_le M z0 b
    have hb3R : (mnorm (M - b) : ℝ) ≤ (mnorm (M - z0) : ℝ) + (mnorm (z0 - b) : ℝ) := by
      exact_mod_cast hb3
    have hm1' : (m1 : ℝ) ≤ Cr * (4 * (ρ : ℝ)) := by
      rw [hMn2] at hm1
      exact le_trans hm1 (mul_le_mul_of_nonneg_left hMnR.2 S.hCr.le)
    have hm2' : (m2 : ℝ) ≤ Cr * (5 * (ρ : ℝ)) := by
      refine le_trans hm2 (mul_le_mul_of_nonneg_left ?_ S.hCr.le)
      linarith [hMnR.2]
    push_cast
    have hkpos : (0 : ℝ) ≤ (k : ℝ) ^ d := by positivity
    have e1 : (m1 : ℝ) * (k : ℝ) ^ d ≤ Cr * (4 * (ρ : ℝ)) * (k : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right hm1' hkpos
    have e2 : (m2 : ℝ) * (k : ℝ) ^ d ≤ Cr * (5 * (ρ : ℝ)) * (k : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right hm2' hkpos
    nlinarith

end Exploding
