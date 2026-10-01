/-
Proposition 5.1 of the paper (generalized last wave): the polylogarithmic error of the lighting.

`glws_E` is the total polylogarithmic time (in `n`) that the lighting of the penultimate cluster of a
site costs once a tile of the infinite cluster near the site is lit: the time `Pn^d + ∏ k` to light
a tile from a long path, the time `A · d (2 Pn + ∑ k)` to carry the lighting from that tile to the
macroscopic site of the target, and the time `B Z^d` of the lighting itself.  It is bounded by a
constant times a power of `log n`.
-/
import Exploding.Support.GLWSec3X

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- The macroscopic scale at which the lighting is run for a target in `[-n,n]^d`. -/
def glws_Ns (d kmax n : ℕ) : ℕ := d * (3 * n + kmax + 1)

/-- The polylogarithmic error of the lighting. -/
noncomputable def glws_E (γp Cch : ℝ) (k : Fin d → ℕ) (n : ℕ) : ℕ :=
  (glws_Pn γp (∑ i, k i) d n) ^ d + ∏ l, k l +
    glws_LA Cch k * (d * (2 * glws_Pn γp (∑ i, k i) d n + ∑ i, k i)) + 1 +
    glws_LB Cch k * (glws_Zn γp (glws_Ns d (∑ i, k i) n)) ^ d

/-- A power of the logarithm is eventually at least any constant multiple of a smaller power. -/
theorem glws_absorb (c a b : ℝ) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, c * Real.log n ^ a ≤ Real.log n ^ b := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ => Real.log n ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hlog
  filter_upwards [h.eventually_ge_atTop c, hlog.eventually_ge_atTop 1] with n h1 h2
  have hL0 : 0 < Real.log n := by linarith
  have e : Real.log n ^ b = Real.log n ^ a * Real.log n ^ (b - a) := by
    rw [← Real.rpow_add hL0]; ring_nf
  have hLa : 0 ≤ Real.log n ^ a := Real.rpow_nonneg hL0.le _
  rw [e]
  nlinarith

/-- `(L^a)^d = L^(a d)`. -/
theorem glws_rpow_pow (L a : ℝ) (hL : 0 < L) (d : ℕ) : (L ^ a) ^ d = L ^ (a * d) := by
  rw [← Real.rpow_natCast (L ^ a) d, ← Real.rpow_mul hL.le]

theorem glws_Ns_sq (d kmax n : ℕ) (hn : 3 * d + d * (kmax + 1) + 3 ≤ n) :
    glws_Ns d kmax n ≤ n ^ 2 := by
  unfold glws_Ns
  have h1 : n * (3 * d + d * (kmax + 1)) ≤ n * n := Nat.mul_le_mul_left n (by omega)
  have h2 : d * (kmax + 1) ≤ d * (kmax + 1) * n := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

/-- The macroscopic radius at a scale `N ≤ n²` is polylogarithmic in `n`. -/
theorem glws_Zn_le (γp : ℝ) (hγp : 0 < γp) (N n : ℕ) (hN : N ≤ n ^ 2) (hN0 : 0 < N)
    (hL1 : 1 ≤ Real.log n) :
    (glws_Zn γp N : ℝ) ≤ (2 : ℝ) ^ (γp + 6) * Real.log n ^ (γp + 5) := by
  have hL0 : 0 < Real.log n := by linarith
  have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hle : (N : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hN
  have hNs' : Real.log (N : ℝ) ≤ 2 * Real.log n := by
    calc Real.log (N : ℝ) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hpos hle
      _ = 2 * Real.log n := by rw [Real.log_pow]; push_cast; ring
  have hNs0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg _
  have e1 : (glws_Zn γp N : ℝ) ≤ Real.log (N : ℝ) ^ (γp + 5) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have e2 : Real.log (N : ℝ) ^ (γp + 5) ≤ (2 * Real.log n) ^ (γp + 5) :=
    Real.rpow_le_rpow hNs0 hNs' (by linarith)
  have e3 : (2 * Real.log n) ^ (γp + 5) = 2 ^ (γp + 5) * Real.log n ^ (γp + 5) :=
    Real.mul_rpow (by norm_num) hL0.le
  have e4 : (1 : ℝ) ≤ Real.log n ^ (γp + 5) := Real.one_le_rpow hL1 (by linarith)
  have e5 : (2 : ℝ) ^ (γp + 6) = 2 * 2 ^ (γp + 5) := by
    rw [show γp + 6 = (γp + 5) + 1 by ring, Real.rpow_add (by norm_num)]
    simp [mul_comm]
  have e6 : (1 : ℝ) ≤ 2 ^ (γp + 5) := Real.one_le_rpow (by norm_num) (by linarith)
  rw [e5]
  nlinarith [e1, e2, e3, e4, e6]

/-- The number of sites of the lit paths is at most a constant times a power of the logarithm. -/
theorem glws_Pn_le (γp : ℝ) (hγp : 0 < γp) (kmax d n : ℕ) (hn3 : 3 ≤ n) (hL1 : 1 ≤ Real.log n) :
    (glws_Pn γp kmax d n : ℝ) ≤
      (((kmax : ℝ) * ((2 : ℝ) ^ ((5 : ℝ) / 2) + 3)) ^ d + (2 : ℝ) ^ γp + 1) *
        Real.log n ^ ((5 : ℝ) / 2 * d + γp) := by
  have h := glws_Pn_poly γp hγp kmax d n hn3 hL1
  set L := Real.log n with hL
  have heP0 : (0 : ℝ) ≤ (5 : ℝ) / 2 * d := by positivity
  have a1 : L ^ ((5 : ℝ) / 2 * d) ≤ L ^ ((5 : ℝ) / 2 * d + γp) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have a2 : L ^ γp ≤ L ^ ((5 : ℝ) / 2 * d + γp) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have a3 : (1 : ℝ) ≤ L ^ ((5 : ℝ) / 2 * d + γp) := Real.one_le_rpow hL1 (by linarith)
  have hc1n : 0 ≤ ((kmax : ℝ) * ((2 : ℝ) ^ ((5 : ℝ) / 2) + 3)) ^ d := by positivity
  have hc2n : 0 ≤ (2 : ℝ) ^ γp := by positivity
  have b1 := mul_le_mul_of_nonneg_left a1 hc1n
  have b2 := mul_le_mul_of_nonneg_left a2 hc2n
  nlinarith [h, b1, b2, a3]

/-- The polylogarithmic error is at most a constant times a power of the logarithm. -/
theorem glws_E_bound (γp Cch : ℝ) (hγp : 0 < γp) (hd : 0 < d) (k : Fin d → ℕ) :
    ∃ (γ cT : ℝ) (n1 : ℕ), 0 < γ ∧ 0 ≤ cT ∧ ∀ n : ℕ, n1 ≤ n →
      3 ≤ n ∧ (1 : ℝ) ≤ Real.log n ∧ ((glws_E γp Cch k n : ℕ) : ℝ) ≤ cT * Real.log n ^ γ := by
  set kmax : ℕ := ∑ i, k i with hkmax
  set K : ℕ := ∏ l, k l with hK
  set cP : ℝ := ((kmax : ℝ) * ((2 : ℝ) ^ ((5 : ℝ) / 2) + 3)) ^ d + (2 : ℝ) ^ γp + 1 with hcP
  set eP : ℝ := (5 : ℝ) / 2 * d + γp with heP
  set cZ : ℝ := (2 : ℝ) ^ (γp + 6) with hcZ
  set eE : ℝ := (d : ℝ) * (eP + γp + 5) with heE
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcPn : 0 ≤ cP := by rw [hcP]; positivity
  have hcZ0 : 0 ≤ cZ := by rw [hcZ]; positivity
  have heP0 : 0 < eP := by rw [heP]; positivity
  have heE0 : 0 < eE := by rw [heE]; positivity
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp ((hlog.eventually_ge_atTop 1).and
    (eventually_ge_atTop (3 * d + d * (kmax + 1) + 3)))
  refine ⟨eE, (cP ^ d + K + (glws_LA Cch k : ℝ) * ((d : ℝ) * (2 * cP + kmax)) + 1 +
    (glws_LB Cch k : ℝ) * cZ ^ d), n1, heE0, by positivity, fun n hn => ?_⟩
  obtain ⟨hL1, hnn⟩ := hn1 n hn
  have hn3 : 3 ≤ n := by omega
  refine ⟨hn3, hL1, ?_⟩
  set L := Real.log n with hL
  have hL0 : 0 < L := by linarith
  have hePE : eP ≤ eE := by rw [heE]; nlinarith
  have hePdE : eP * d ≤ eE := by rw [heE]; nlinarith
  have hZE : (γp + 5) * d ≤ eE := by rw [heE]; nlinarith
  have hLE : ∀ a, a ≤ eE → L ^ a ≤ L ^ eE := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hL1 ha
  have hLE1 : (1 : ℝ) ≤ L ^ eE := Real.one_le_rpow hL1 heE0.le
  have hNs := glws_Ns_sq d kmax n hnn
  have hNs0 : 0 < glws_Ns d kmax n := by
    unfold glws_Ns; exact Nat.mul_pos hd (by omega)
  have hZ := glws_Zn_le γp hγp _ n hNs hNs0 hL1
  have hP := glws_Pn_le γp hγp kmax d n hn3 hL1
  set Pn : ℕ := glws_Pn γp kmax d n with hPn
  set Zn : ℕ := glws_Zn γp (glws_Ns d kmax n) with hZn
  have hPn0 : (0 : ℝ) ≤ Pn := Nat.cast_nonneg _
  have hZn0 : (0 : ℝ) ≤ Zn := Nat.cast_nonneg _
  have t1 : ((Pn : ℝ)) ^ d ≤ cP ^ d * L ^ eE := by
    calc (Pn : ℝ) ^ d ≤ (cP * L ^ eP) ^ d := pow_le_pow_left₀ hPn0 hP d
      _ = cP ^ d * (L ^ eP) ^ d := mul_pow _ _ _
      _ = cP ^ d * L ^ (eP * d) := by rw [glws_rpow_pow L eP hL0]
      _ ≤ cP ^ d * L ^ eE := mul_le_mul_of_nonneg_left (hLE _ hePdE) (by positivity)
  have t2 : (K : ℝ) ≤ K * L ^ eE := by
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    calc (K : ℝ) = K * 1 := (mul_one _).symm
      _ ≤ K * L ^ eE := mul_le_mul_of_nonneg_left hLE1 hK0
  have t3 : (2 * (Pn : ℝ) + kmax) ≤ (2 * cP + kmax) * L ^ eE := by
    have h1 : cP * L ^ eP ≤ cP * L ^ eE := mul_le_mul_of_nonneg_left (hLE _ hePE) hcPn
    have h2 : (kmax : ℝ) * 1 ≤ kmax * L ^ eE :=
      mul_le_mul_of_nonneg_left hLE1 (Nat.cast_nonneg _)
    nlinarith
  have t5 : ((Zn : ℝ)) ^ d ≤ cZ ^ d * L ^ eE := by
    calc (Zn : ℝ) ^ d ≤ (cZ * L ^ (γp + 5)) ^ d := pow_le_pow_left₀ hZn0 hZ d
      _ = cZ ^ d * (L ^ (γp + 5)) ^ d := mul_pow _ _ _
      _ = cZ ^ d * L ^ ((γp + 5) * d) := by rw [glws_rpow_pow L _ hL0]
      _ ≤ cZ ^ d * L ^ eE := mul_le_mul_of_nonneg_left (hLE _ hZE) (by positivity)
  unfold glws_E
  rw [← hkmax, ← hK, ← hPn, ← hZn]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
  have hLA : (0 : ℝ) ≤ (glws_LA Cch k : ℝ) := Nat.cast_nonneg _
  have hLB : (0 : ℝ) ≤ (glws_LB Cch k : ℝ) := Nat.cast_nonneg _
  have u3 : (glws_LA Cch k : ℝ) * ((d : ℝ) * (2 * (Pn : ℝ) + kmax)) ≤
      (glws_LA Cch k : ℝ) * ((d : ℝ) * ((2 * cP + kmax) * L ^ eE)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left t3 (by positivity)) hLA
  have u5 : (glws_LB Cch k : ℝ) * (Zn : ℝ) ^ d ≤ (glws_LB Cch k : ℝ) * (cZ ^ d * L ^ eE) :=
    mul_le_mul_of_nonneg_left t5 hLB
  have hsum : (cP ^ d + K + (glws_LA Cch k : ℝ) * ((d : ℝ) * (2 * cP + kmax)) + 1 +
      (glws_LB Cch k : ℝ) * cZ ^ d) * L ^ eE =
      cP ^ d * L ^ eE + K * L ^ eE + (glws_LA Cch k : ℝ) * ((d : ℝ) * ((2 * cP + kmax) * L ^ eE)) +
      1 * L ^ eE + (glws_LB Cch k : ℝ) * (cZ ^ d * L ^ eE) := by ring
  rw [hsum]
  linarith [t1, t2, u3, u5, hLE1]

end Exploding
