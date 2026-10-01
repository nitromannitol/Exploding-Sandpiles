/-
Proposition 5.1 of the paper (generalized last wave): the scales of the lighting from a lit tile.

For `n` large the macroscopic radius `Z = ⌈(log n)^{γ_p + 5}⌉`, the row length `r = ⌈(log 2n)^{5/2}⌉`
and the offset `Λ = Z + 1 + r` are polylogarithmic, so all the walks of the lighting stay in the box
of radius `2n`, and the chemical-distance and path-filling thresholds are met.
-/
import Exploding.Support.GLWSec3P

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

/-- The macroscopic radius of the lighting. -/
noncomputable def glws_Zn (γp : ℝ) (n : ℕ) : ℕ := ⌈Real.log n ^ (γp + 5)⌉₊

/-- The length of the rows of macroscopic sites searched for the cluster. -/
noncomputable def glws_rn (n : ℕ) : ℕ := ⌈Real.log ((2 * n : ℕ) : ℝ) ^ ((5 : ℝ) / 2)⌉₊

/-- The scale estimates of the lighting from a lit tile hold for `n` large. -/
theorem glws_asymp_ln (γp : ℝ) (hγp : 0 < γp) (kmax Cn d : ℕ) :
    ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n →
      2 ≤ n ∧ 1 ≤ glws_Zn γp n ∧ glws_rn n ≤ glws_Zn γp n ∧
      Real.log ((2 * n : ℕ) : ℝ) ^ (2 : ℕ) ≤ (glws_Zn γp n : ℝ) + 1 ∧
      (1 + 2 * Cn) * d * (glws_Zn γp n + 1 + glws_rn n) ≤ n ∧
      Real.log ((kmax * (2 * n + 1) : ℕ) : ℝ) ^ γp ≤ 2 * (glws_Zn γp n : ℝ) + 3 := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n := hlog.eventually_ge_atTop 1
  -- `(2L)^{5/2} + 1 ≤ L^{γp+5}`
  have hev2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((5 : ℝ) / 2) + 1 ≤ Real.log n ^ (γp + 5 / 2) := by
    have h : Tendsto (fun n : ℕ => Real.log n ^ (γp + 5 / 2)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp hlog
    exact h.eventually_ge_atTop _
  have hev3 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ Real.log n ^ (γp + 3) := by
    have h : Tendsto (fun n : ℕ => Real.log n ^ (γp + 3)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp hlog
    exact h.eventually_ge_atTop _
  have hev4 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ γp ≤ Real.log n ^ (5 : ℝ) := by
    have h : Tendsto (fun n : ℕ => Real.log n ^ (5 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp hlog
    exact h.eventually_ge_atTop _
  -- the polylogarithm is small against `n`
  have hev5 : ∀ᶠ n : ℕ in atTop,
      ((1 + 2 * Cn : ℝ) * d) * (3 * Real.log n ^ (γp + 5) + 2) ≤ n := by
    have h := lwc_transfer_4 (γp + 5) 1 one_pos
    simp only [Nat.cast_one, one_mul] at h
    have hc : (0 : ℝ) < ((1 + 2 * Cn : ℝ) * d * 3 + 1) := by positivity
    have := h.eventually_le_const (show (0 : ℝ) < 1 / (((1 + 2 * Cn : ℝ) * d * 3 + 1) * 2) by
      positivity)
    filter_upwards [this, eventually_ge_atTop 1, hev1] with n hn hn1 hL1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [div_le_iff₀ hnpos] at hn
    have hLp : (1 : ℝ) ≤ Real.log n ^ (γp + 5) := Real.one_le_rpow hL1 (by linarith)
    have hA : (0 : ℝ) ≤ ((1 + 2 * Cn : ℝ) * d) := by positivity
    have hB : ((1 + 2 * Cn : ℝ) * d) * (3 * Real.log n ^ (γp + 5) + 2) ≤
        (((1 + 2 * Cn : ℝ) * d * 3 + 1)) * Real.log n ^ (γp + 5) * 2 := by
      have := mul_le_mul_of_nonneg_left (show 3 * Real.log n ^ (γp + 5) + 2 ≤
        (3 + 2) * Real.log n ^ (γp + 5) by linarith) hA
      nlinarith [this, hLp, hA]
    have hC : (((1 + 2 * Cn : ℝ) * d * 3 + 1)) * Real.log n ^ (γp + 5) * 2 ≤ n := by
      have h0 : (0 : ℝ) < (((1 + 2 * Cn : ℝ) * d * 3 + 1) * 2) := by positivity
      rw [show (1 : ℝ) / (((1 + 2 * Cn : ℝ) * d * 3 + 1) * 2) * n =
        n / (((1 + 2 * Cn : ℝ) * d * 3 + 1) * 2) by ring] at hn
      rw [le_div_iff₀ h0] at hn
      linarith
    linarith
  have hev6 : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ kmax * (2 * n + 1) ≤ n ^ 2 := by
    filter_upwards [eventually_ge_atTop (3 * kmax + 2)] with n hn
    refine ⟨by omega, ?_⟩
    nlinarith
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp (hev1.and (hev2.and (hev3.and (hev4.and
    (hev5.and hev6)))))
  refine ⟨n1, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hn1 n hn
  set L := Real.log n with hL
  have hL0 : 0 < L := by linarith
  have hZ : L ^ (γp + 5) ≤ (glws_Zn γp n : ℝ) := Nat.le_ceil _
  have hZ' : (glws_Zn γp n : ℝ) < L ^ (γp + 5) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hLp : (1 : ℝ) ≤ L ^ (γp + 5) := Real.one_le_rpow h1 (by linarith)
  -- `log (2 n) ≤ 2 L`
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h6
  have hlog2n : Real.log ((2 * n : ℕ) : ℝ) ≤ 2 * L := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hlog2n0 : 0 ≤ Real.log ((2 * n : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hrZ : (glws_rn n : ℝ) ≤ L ^ (γp + 5) := by
    have h1' : (glws_rn n : ℝ) ≤ Real.log ((2 * n : ℕ) : ℝ) ^ ((5 : ℝ) / 2) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have h2' : Real.log ((2 * n : ℕ) : ℝ) ^ ((5 : ℝ) / 2) ≤ (2 * L) ^ ((5 : ℝ) / 2) :=
      Real.rpow_le_rpow hlog2n0 hlog2n (by norm_num)
    have e1 : (2 * L) ^ ((5 : ℝ) / 2) = 2 ^ ((5 : ℝ) / 2) * L ^ ((5 : ℝ) / 2) :=
      Real.mul_rpow (by norm_num) hL0.le
    have e2 : L ^ (γp + 5) = L ^ ((5 : ℝ) / 2) * L ^ (γp + 5 / 2) := by
      rw [← Real.rpow_add hL0]; ring_nf
    have hLq : (1 : ℝ) ≤ L ^ ((5 : ℝ) / 2) := Real.one_le_rpow h1 (by norm_num)
    rw [e1] at h2'
    rw [e2]
    nlinarith [h2', h1', h2, hLq]
  refine ⟨h6, ?_, ?_, ?_, ?_, ?_⟩
  · have : (1 : ℝ) ≤ (glws_Zn γp n : ℝ) := le_trans hLp hZ
    exact_mod_cast this
  · have : (glws_rn n : ℝ) ≤ (glws_Zn γp n : ℝ) := le_trans hrZ hZ
    exact_mod_cast this
  · have e : L ^ (γp + 5) = L ^ (γp + 3) * L ^ (2 : ℕ) := by
      rw [show (γp + 5 : ℝ) = (γp + 3) + 2 by ring, Real.rpow_add hL0]
      congr 1
      exact_mod_cast Real.rpow_natCast L 2
    have hsq : Real.log ((2 * n : ℕ) : ℝ) ^ (2 : ℕ) ≤ (2 * L) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hlog2n0 hlog2n 2
    have hL2 : 0 ≤ L ^ (2 : ℕ) := by positivity
    nlinarith [hsq, h3, hZ, e, hL2]
  · have hZZ : ((glws_Zn γp n : ℝ) + 1 + glws_rn n) ≤ 3 * L ^ (γp + 5) + 2 := by linarith
    have hcast : (((1 + 2 * Cn) * d * (glws_Zn γp n + 1 + glws_rn n) : ℕ) : ℝ) =
        ((1 + 2 * Cn : ℝ) * d) * ((glws_Zn γp n : ℝ) + 1 + glws_rn n) := by push_cast; ring
    have : (((1 + 2 * Cn) * d * (glws_Zn γp n + 1 + glws_rn n) : ℕ) : ℝ) ≤ n := by
      rw [hcast]
      have hA : (0 : ℝ) ≤ ((1 + 2 * Cn : ℝ) * d) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hZZ hA, h5]
    exact_mod_cast this
  · -- the polylogarithmic path-filling threshold
    have hnm : ((kmax * (2 * n + 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast h7
    have hnm0 : (0 : ℝ) < ((kmax * (2 * n + 1) : ℕ) : ℝ) ∨ kmax = 0 := by
      rcases Nat.eq_zero_or_pos kmax with h | h
      · exact Or.inr h
      · left; positivity
    rcases hnm0 with hpos | hk0
    · have hlog_le : Real.log ((kmax * (2 * n + 1) : ℕ) : ℝ) ≤ 2 * L := by
        calc Real.log ((kmax * (2 * n + 1) : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
              Real.log_le_log hpos hnm
          _ = 2 * L := by rw [Real.log_pow]; push_cast; ring
      have hlog0 : 0 ≤ Real.log ((kmax * (2 * n + 1) : ℕ) : ℝ) := Real.log_natCast_nonneg _
      have h1' : Real.log ((kmax * (2 * n + 1) : ℕ) : ℝ) ^ γp ≤ (2 * L) ^ γp :=
        Real.rpow_le_rpow hlog0 hlog_le hγp.le
      have e1 : (2 * L) ^ γp = 2 ^ γp * L ^ γp := Real.mul_rpow (by norm_num) hL0.le
      have e2 : L ^ (γp + 5) = L ^ γp * L ^ (5 : ℝ) := Real.rpow_add hL0 _ _
      have hLg : (0 : ℝ) ≤ L ^ γp := by positivity
      have : (2 * L) ^ γp ≤ L ^ (γp + 5) := by
        rw [e1, e2]
        calc 2 ^ γp * L ^ γp ≤ L ^ (5 : ℝ) * L ^ γp := mul_le_mul_of_nonneg_right h4 hLg
          _ = L ^ γp * L ^ (5 : ℝ) := by ring
      linarith
    · subst hk0
      simp only [zero_mul, Nat.cast_zero, Real.log_zero]
      rw [Real.zero_rpow hγp.ne']
      have : (0 : ℝ) ≤ (glws_Zn γp n : ℝ) := Nat.cast_nonneg _
      linarith

end Exploding
