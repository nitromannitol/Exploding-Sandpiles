/-
Proposition 5.1 (generalized last wave), closeness of the arrival times, part F:
a lit site lights its penultimate cluster polylogarithmically later.

The data of the closeness estimate on a fixed background `η`: `0 ≤ η ≤ 2d - 1`, path-filling with
exponent `γp`, and an infinite connected set `C_∞` of strongly box-crossing tiles with small holes and
linear chemical distance.  If the last wave is positive at a site `x` far from the origin at time `a`,
the long lit path to `x` lights a tile of `C_∞` near `x`, and the tile lights the penultimate cluster
of `x` (`s3k_far`); near the origin, the first lit tile of the cluster does the lighting (`s3k_near`).
-/
import Exploding.Support.S3CloseE

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- The data of the closeness estimate on a background. -/
structure S3kData (d : ℕ) (η : Site d → ℤ) (k : Fin d → ℕ) (Cinf : Set (Site d))
    (γp Cch : ℝ) : Type where
  hd : 2 ≤ d
  hlow : ∀ x, 0 ≤ η x
  hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1
  hk : ∀ i, 0 < k i
  hinf : Cinf.Infinite
  hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j
  hconn : ∀ x ∈ Cinf, ∀ y ∈ Cinf, y ∈ componentIn Cinf x
  n0h : ℕ
  hole : ∀ n : ℕ, n0h ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
    (componentIn Cinfᶜ x).Finite ∧ ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)
  hCch : 0 ≤ Cch
  n0c : ℕ
  hchem : ∀ n : ℕ, n0c ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf, mnorm x ≤ (n : ℤ) →
    Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
    ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧ (m : ℝ) ≤ Cch * (mnorm (x - y) : ℝ)
  hγp : 0 < γp
  hpf : glws_PF d γp η

theorem s3k_ev_Zge (γp : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.log n ^ (γp + 4) ≤ (glws_Zn γp n : ℝ) := by
  filter_upwards [s3k_ev_log_ge 1] with n hL
  unfold glws_Zn
  refine le_trans ?_ (Nat.le_ceil _)
  exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)

theorem s3k_ev_Z2ge (γp : ℝ) (hγp : 0 < γp) :
    ∀ᶠ n : ℕ in atTop, Real.log n ^ (γp + 4) ≤ (glws_Zn γp (2 * n) : ℝ) := by
  filter_upwards [s3k_ev_log_ge 1, eventually_ge_atTop 1] with n hL hn
  unfold glws_Zn
  refine le_trans ?_ (Nat.le_ceil _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log n ≤ Real.log ((2 * n : ℕ) : ℝ) :=
    Real.log_le_log hn0 (by push_cast; linarith)
  calc Real.log n ^ (γp + 4) ≤ Real.log n ^ (γp + 5) :=
        Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    _ ≤ Real.log ((2 * n : ℕ) : ℝ) ^ (γp + 5) := Real.rpow_le_rpow (by linarith) h1 (by linarith)

/-- **Near the origin.**  The first lit tile of `C_∞` lights the penultimate cluster of every site
`x` with `mnorm x ≤ R`, for `R + d ≤ n`, by time `τ0 + A (J + R + d) + B Z^d`. -/
theorem s3k_near {k : Fin d → ℕ} {Cinf : Set (Site d)} {γp Cch : ℝ} {η : Site d → ℤ}
    (D : S3kData d η k Cinf γp Cch) :
    ∃ τ0 J A B n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ (x : Site d) (R : ℕ), mnorm x ≤ (R : ℤ) →
      R + d ≤ n → ∀ w ∈ penultimateCluster η x,
        0 < lastWave η (0 : Site d) (τ0 + A * (J + R + d) + B * glws_Zn γp n ^ d) w := by
  classical
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast D.hd
    linarith
  obtain ⟨j0, hj0, τ0, hfired⟩ := glws_first_lit D.hd η D.hlow D.hhigh k D.hk Cinf D.hinf D.hgood
    D.hconn D.n0h D.hole γp D.hγp D.hpf
  have hlast := glws_finite_exploding D.hd η D.hlow D.hhigh k D.hk Cinf D.hinf D.hgood D.hconn
    (0 : Site d)
  have hne : {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)}.Nonempty := hlast
  have hN : 1 ≤ waveThreshold η (0 : Site d) :=
    (Nat.sInf_mem hne : 1 ≤ waveThreshold η (0 : Site d) ∧ _).1
  obtain ⟨n0L, hL⟩ := glws_light_near D.hd η D.hlow D.hhigh k D.hk Cinf D.hgood D.n0h D.hole
    Cch D.hCch D.n0c D.hchem γp D.hγp D.hpf
  set A : ℕ := glws_LA Cch k with hA
  set B : ℕ := glws_LB Cch k with hB
  obtain ⟨n0pen, hpen⟩ := glws_penultimate_small D.hd η D.hlow D.hhigh k D.hk Cinf D.hinf D.hgood
    D.hconn D.n0h D.hole γp D.hγp D.hpf
  obtain ⟨n0z, hz⟩ := eventually_atTop.mp (s3k_ev_Zge γp)
  set J : ℕ := (mnorm j0).toNat with hJ
  refine ⟨τ0, J, A, B, max (max n0L n0pen) (max n0z J), ?_⟩
  intro n hn x R hxR hRn w hw
  have hn0L : n0L ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn0pen : n0pen ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0z : n0z ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hJn : J ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hxn : mnorm x ≤ (n : ℤ) := by
    have : (R : ℤ) ≤ (n : ℤ) := by exact_mod_cast (by omega : R ≤ n)
    linarith
  have hxc : x ∈ (cent d n : Set (Site d)) := fun i =>
    le_trans (pclose_abs_coord_le x i) hxn
  have hνn : mnorm (s3k_nu k x) ≤ (n : ℤ) := by
    have h1 := s3k_mnorm_nu_le k D.hk x
    have : (R : ℤ) + (d : ℤ) ≤ (n : ℤ) := by exact_mod_cast hRn
    linarith
  have hj0n : mnorm j0 ≤ (n : ℤ) := by
    have h1 : mnorm j0 ≤ (J : ℤ) := by
      rw [hJ]; exact Int.self_le_toNat _
    have : (J : ℤ) ≤ (n : ℤ) := by exact_mod_cast hJn
    linarith
  have hy : ∀ y ∈ penultimateCluster η x, ∀ m,
      (k m : ℤ) * (s3k_nu k x m - (glws_Zn γp n : ℤ)) + 1 ≤ y m ∧
        y m ≤ (k m : ℤ) * (s3k_nu k x m + (glws_Zn γp n : ℤ) + 1) := by
    intro y hy m
    refine s3k_region k D.hk x y (glws_Zn γp n : ℤ) (fun i => ?_) m
    have h1 := hpen n hn0pen x hxc y hy i
    have h2 := hz n hn0z
    have h3 : (((|y i - x i| : ℤ)) : ℝ) ≤ ((glws_Zn γp n : ℕ) : ℝ) := le_trans h1 h2
    exact_mod_cast h3
  have hres := hL n hn0L (waveThreshold η (0 : Site d)) hN (0 : Site d) τ0 j0 hj0 hj0n hfired
    (s3k_nu k x) hνn w (hy w hw)
  -- the time bound
  have hjν : (mnorm (j0 - s3k_nu k x)).toNat ≤ J + R + d := by
    have h1 := glw2_mnorm_sub_le j0 (s3k_nu k x)
    have h2 := s3k_mnorm_nu_le k D.hk x
    have h3 : mnorm j0 ≤ (J : ℤ) := by rw [hJ]; exact Int.self_le_toNat _
    have h4 : mnorm (j0 - s3k_nu k x) ≤ ((J + R + d : ℕ) : ℤ) := by
      push_cast; linarith
    omega
  have hle : τ0 + A * (mnorm (j0 - s3k_nu k x)).toNat + B * glws_Zn γp n ^ d ≤
      τ0 + A * (J + R + d) + B * glws_Zn γp n ^ d := by
    have := Nat.mul_le_mul_left A hjν
    omega
  exact pclose_pos_mono hd0 η D.hlow _ (0 : Site d) hle hres

end Exploding
