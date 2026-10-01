/-
Proposition 5.1 (generalized last wave), closeness of the arrival times, part G:
a lit site far from the origin lights its penultimate cluster polylogarithmically later.

If the last wave is positive at `x` at time `a`, the last stretch of the path from the origin to `x`
is a long lit path; it lights a tile of `C_∞` within a polylogarithmic distance of `x` at time
`a + Pn^d + ∏ k` (`glws_path_to_tile`), and that tile lights the tiles around the macroscopic site of
`x`, which contain the penultimate cluster of `x`, within a further polylogarithmic time
(`glws_light_near`).
-/
import Exploding.Support.S3CloseF

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- **Far from the origin.** -/
theorem s3k_far {k : Fin d → ℕ} {Cinf : Set (Site d)} {γp Cch : ℝ} {η : Site d → ℤ}
    (D : S3kData d η k Cinf γp Cch) :
    ∃ A B n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ (x : Site d) (a : ℕ), mnorm x ≤ (n : ℤ) →
      (∃ l, ((glws_Pn γp (∑ i, k i) d n : ℕ) : ℤ) ≤ |x l|) →
      0 < lastWave η (0 : Site d) a x → ∀ w ∈ penultimateCluster η x,
        0 < lastWave η (0 : Site d) (a + s3k_Tfar γp (∑ i, k i) d (∏ l, k l) A B n) w := by
  classical
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast D.hd
    linarith
  have hdpos : 0 < d := by have := D.hd; omega
  set kmax : ℕ := ∑ i, k i with hkmax
  set K : ℕ := ∏ l, k l with hK
  have hkmax1 : 1 ≤ kmax :=
    le_trans (D.hk ⟨0, hdpos⟩)
      (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  obtain ⟨n0L, hL⟩ := glws_light_near D.hd η D.hlow D.hhigh k D.hk Cinf D.hgood D.n0h D.hole
    Cch D.hCch D.n0c D.hchem γp D.hγp D.hpf
  set A : ℕ := glws_LA Cch k with hA
  set B : ℕ := glws_LB Cch k with hB
  obtain ⟨n0pen, hpen⟩ := glws_penultimate_small D.hd η D.hlow D.hhigh k D.hk Cinf D.hinf D.hgood
    D.hconn D.n0h D.hole γp D.hγp D.hpf
  obtain ⟨n0pt, hpt⟩ := glws_path_to_tile D.hd η D.hlow D.hhigh k D.hk Cinf D.hgood D.n0h D.hole
    γp D.hpf
  obtain ⟨n1, hn1⟩ := glws_asymp_Pn γp D.hγp kmax d
  obtain ⟨n0z, hz⟩ := eventually_atTop.mp (s3k_ev_Z2ge γp D.hγp)
  -- the lit path and the tiles stay in the box: `d * Pn + 2 d kmax + d ≤ n`
  have hPL := s3k_PL_Pn γp D.hγp kmax d
  obtain ⟨n0b, hb⟩ := eventually_atTop.mp
    ((s3k_PL_le_n hPL (2 * (d : ℝ)) (by positivity)).and
      (eventually_ge_atTop (4 * d * kmax + 2 * d + 1)))
  refine ⟨A, B, max (max (max n0L n0pen) (max n0pt n1)) (max n0z n0b), ?_⟩
  intro n hn x a hxn hfar hax w hw
  have hn0L : n0L ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hn
  have hn0pen : n0pen ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hn
  have hn0pt : n0pt ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_left _ _)) hn
  have hn1' : n1 ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_left _ _)) hn
  have hn0z : n0z ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn0b : n0b ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hn3, hPn⟩ := hn1 n hn1'
  obtain ⟨hbig1, hbig2⟩ := hb n hn0b
  set Pn : ℕ := glws_Pn γp kmax d n with hPndef
  set r : ℕ := glws_r2 n with hr
  have hPn1 : 1 ≤ Pn := by
    have : 1 ≤ (kmax * (r + 2)) ^ d := Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (by omega))
    have h2 : (kmax * (r + 2)) ^ d ≤ Pn := Nat.le_add_right _ _
    omega
  -- `d * Pn + 2 d kmax + d ≤ n`
  have hbound : d * Pn + 2 * d * kmax + d ≤ n := by
    have h1 : (2 * (d : ℝ)) * (Pn : ℝ) ≤ (n : ℝ) := hbig1
    have h2 : (2 * d * Pn : ℕ) ≤ n := by exact_mod_cast h1
    have h3 : (4 * d * kmax + 2 * d + 1 : ℕ) ≤ n := hbig2
    nlinarith
  -- the path from the origin to `x`
  have hN : 1 ≤ waveThreshold η (0 : Site d) := by
    have hax' : 0 < wave η (waveThreshold η (0 : Site d)) (0 : Site d) a x := hax
    exact pclose_mass_pos η D.hhigh hd0 _ (0 : Site d) a x hax'
  obtain ⟨m, z, hz0, hzm, hadj, hinj, hlit⟩ := glws_path_extract η D.hlow D.hhigh hd0
    (waveThreshold η (0 : Site d)) (0 : Site d) a x hax
  obtain ⟨l, hl⟩ := hfar
  have hml : Pn ≤ m := by
    have h1 := glws_path_coord z hadj l m le_rfl
    rw [hzm, hz0] at h1
    simp only [Pi.zero_apply, sub_zero] at h1
    have h2 : (Pn : ℤ) ≤ (m : ℤ) := le_trans hl h1
    exact_mod_cast h2
  set p : ℕ := Pn - 1 with hp
  have hpm : p ≤ m := by omega
  have hpP : p + 1 = Pn := by omega
  obtain ⟨zr, hzr0, hradj, hrinj, hrlit, hrdist⟩ := s3k_path_back η (waveThreshold η (0 : Site d))
    a m z hadj hinj hlit p hpm
  have hzrx : zr 0 = x := by rw [hzr0, hzm]
  have hcent : ∀ i, i ≤ p → zr i ∈ cent d (2 * n) := by
    intro i hi l'
    have h1 := hrdist i hi l'
    have h2 : |zr i l'| ≤ |x l'| + (i : ℤ) := by
      have := abs_sub_abs_le_abs_sub (zr i l') (z m l')
      rw [hzm] at this h1
      linarith
    have h3 : |x l'| ≤ (n : ℤ) := le_trans (pclose_abs_coord_le x l') hxn
    have h4 : (i : ℤ) ≤ (n : ℤ) := by
      have : i ≤ n := by omega
      exact_mod_cast this
    have : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
    rw [this]
    linarith
  have hlenR : Real.log ((2 * n : ℕ) : ℝ) ^ γp ≤ ((p + 1 : ℕ) : ℝ) := by
    have h1 : Real.log ((2 * n : ℕ) : ℝ) ^ γp ≤ ((⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ ≤ Pn := Nat.le_add_left _ _
    rw [hpP]
    exact le_trans h1 (by exact_mod_cast h2)
  have hS : (kmax * (r + 2)) ^ d ≤ p + 1 := by
    have h2 : (kmax * (r + 2)) ^ d ≤ Pn := Nat.le_add_right _ _
    omega
  obtain ⟨j, hj, hfired, hjtile⟩ := hpt (2 * n) (by omega) r (Nat.le_ceil _)
    (waveThreshold η (0 : Site d)) hN (0 : Site d) a p zr hcent hrinj hradj hrlit hlenR hS
  -- the macroscopic geometry
  have hjν : ∀ m', |j m' - s3k_nu k x m'| ≤ (p : ℤ) + 2 * (kmax : ℤ) := by
    intro m'
    have h1 := s3k_tile_close k D.hk x j ((p : ℤ) + kmax) (fun y hy m'' => by
      have := hjtile y hy m''
      rwa [hzrx] at this) m'
    have h2 : (k m' : ℤ) ≤ (kmax : ℤ) := by
      have : k m' ≤ kmax :=
        Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m')
      exact_mod_cast this
    linarith
  have hjνn : mnorm (j - s3k_nu k x) ≤ (d : ℤ) * ((p : ℤ) + 2 * (kmax : ℤ)) :=
    glws_mnorm_le_coord _ _ hjν
  have hjνnat : (mnorm (j - s3k_nu k x)).toNat ≤ d * (Pn + 2 * kmax) := by
    have h1 : mnorm (j - s3k_nu k x) ≤ ((d * (Pn + 2 * kmax) : ℕ) : ℤ) := by
      have : (p : ℤ) + 2 * (kmax : ℤ) ≤ (Pn : ℤ) + 2 * (kmax : ℤ) := by
        have : p ≤ Pn := by omega
        exact_mod_cast (by omega : p + 2 * kmax ≤ Pn + 2 * kmax)
      push_cast
      calc mnorm (j - s3k_nu k x) ≤ (d : ℤ) * ((p : ℤ) + 2 * (kmax : ℤ)) := hjνn
        _ ≤ (d : ℤ) * ((Pn : ℤ) + 2 * (kmax : ℤ)) :=
            mul_le_mul_of_nonneg_left this (Int.natCast_nonneg d)
    omega
  have hνn : mnorm (s3k_nu k x) ≤ ((2 * n : ℕ) : ℤ) := by
    have h1 := s3k_mnorm_nu_le k D.hk x
    have : (d : ℤ) ≤ (n : ℤ) := by exact_mod_cast (by omega : d ≤ n)
    push_cast; linarith
  have hjn : mnorm j ≤ ((2 * n : ℕ) : ℤ) := by
    have h1 : mnorm j ≤ mnorm (s3k_nu k x) + mnorm (j - s3k_nu k x) := by
      have := glw2_mnorm_add_le (s3k_nu k x) (j - s3k_nu k x)
      simpa using this
    have h2 := s3k_mnorm_nu_le k D.hk x
    have h3 : ((d * (Pn + 2 * kmax) : ℕ) : ℤ) + (d : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast (by nlinarith : d * (Pn + 2 * kmax) + d ≤ n)
    have h4 : mnorm (j - s3k_nu k x) ≤ ((d * (Pn + 2 * kmax) : ℕ) : ℤ) := by
      have := hjνnat
      omega
    push_cast at h3 h4 ⊢
    linarith
  have hy : ∀ y ∈ penultimateCluster η x, ∀ m',
      (k m' : ℤ) * (s3k_nu k x m' - (glws_Zn γp (2 * n) : ℤ)) + 1 ≤ y m' ∧
        y m' ≤ (k m' : ℤ) * (s3k_nu k x m' + (glws_Zn γp (2 * n) : ℤ) + 1) := by
    intro y hy m'
    have hxc : x ∈ (cent d n : Set (Site d)) := fun i => le_trans (pclose_abs_coord_le x i) hxn
    refine s3k_region k D.hk x y (glws_Zn γp (2 * n) : ℤ) (fun i => ?_) m'
    have h1 := hpen n hn0pen x hxc y hy i
    have h2 := hz n hn0z
    have h3 : (((|y i - x i| : ℤ)) : ℝ) ≤ ((glws_Zn γp (2 * n) : ℕ) : ℝ) := le_trans h1 h2
    exact_mod_cast h3
  have hres := hL (2 * n) (by omega) (waveThreshold η (0 : Site d)) hN (0 : Site d)
    (a + (p + 1) ^ d + K) j hj hjn hfired (s3k_nu k x) hνn w (hy w hw)
  have hle : a + (p + 1) ^ d + K + A * (mnorm (j - s3k_nu k x)).toNat +
      B * glws_Zn γp (2 * n) ^ d ≤ a + s3k_Tfar γp kmax d K A B n := by
    unfold s3k_Tfar
    have := Nat.mul_le_mul_left A hjνnat
    rw [hpP]
    linarith
  exact pclose_pos_mono hd0 η D.hlow _ (0 : Site d) hle hres

end Exploding
