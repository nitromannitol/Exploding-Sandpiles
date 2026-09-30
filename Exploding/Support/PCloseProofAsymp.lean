/-
The asymptotic bookkeeping for the second inequality of Lemma 3.7: the scale `Z` built
from `log (2 n)` is at most a constant times a power of `log n`, so any fixed power of
`Z` is at most a slightly larger power of `log n`, and a power of `log n` is eventually
smaller than `n`.
-/
import Mathlib

namespace Exploding

/-- The scale: a fixed power of `log (2 n)`, rounded up, plus a constant. -/
noncomputable def pcloseZ (e0 : ℝ) (K0 n : ℕ) : ℕ :=
  ⌈Real.log (2 * (n : ℝ)) ^ e0⌉₊ + K0

/-- A power of the logarithm is eventually at most a fifth of `n`. -/
theorem pclose_log_pow_le (γ : ℝ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → 5 * Real.log (n : ℝ) ^ γ ≤ (n : ℝ) := by
  have h := isLittleO_log_rpow_rpow_atTop γ (zero_lt_one : (0 : ℝ) < 1)
  have h5 := h.def (by norm_num : (0 : ℝ) < 1 / 5)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 h5
  refine ⟨⌈max X 1⌉₊, fun n hn => ?_⟩
  have hnX : max X 1 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have h1 : (1 : ℝ) ≤ (n : ℝ) := le_trans (le_max_right _ _) hnX
  have h2 := hX (n : ℝ) (le_trans (le_max_left _ _) hnX)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg h1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog γ),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) 1), Real.rpow_one] at h2
  linarith

/-- The scale is at most a constant times the power `e0` of `log n`. -/
theorem pclose_Z_le (e0 : ℝ) (he0 : 5 / 2 ≤ e0) (K0 n : ℕ) (hn : 2 ≤ n)
    (hl : 1 ≤ Real.log (n : ℝ)) :
    (pcloseZ e0 K0 n : ℝ) ≤ (2 ^ e0 + 1 + K0) * Real.log (n : ℝ) ^ e0 := by
  have he0' : (0 : ℝ) ≤ e0 := by linarith
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog2 : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
  have hℓ0 : (0 : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hℓ2 : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith
  have hℓ20 : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have h1 : Real.log (2 * (n : ℝ)) ^ e0 ≤ (2 * Real.log (n : ℝ)) ^ e0 :=
    Real.rpow_le_rpow hℓ20 hℓ2 he0'
  have h2 : (2 * Real.log (n : ℝ)) ^ e0 = 2 ^ e0 * Real.log (n : ℝ) ^ e0 :=
    Real.mul_rpow (by norm_num) hℓ0
  have h3 : (1 : ℝ) ≤ Real.log (n : ℝ) ^ e0 := Real.one_le_rpow hl he0'
  have h4 : (⌈Real.log (2 * (n : ℝ)) ^ e0⌉₊ : ℝ) ≤ Real.log (2 * (n : ℝ)) ^ e0 + 1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg hℓ20 e0)).le
  unfold pcloseZ
  push_cast
  have hK0 : (0 : ℝ) ≤ (K0 : ℝ) := Nat.cast_nonneg K0
  nlinarith [h1, h2, h3, h4, hK0]

/-- **Eventually, every fixed power of the scale is at most a slightly larger power of `log n`,
and at most a fifth of `n`.** -/
theorem pclose_eventually (e0 : ℝ) (he0 : 5 / 2 ≤ e0) (K0 E1 : ℕ) :
    ∃ n_ : ℕ, ∀ n : ℕ, n_ ≤ n → 2 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧
      (pcloseZ e0 K0 n : ℝ) ^ E1 ≤ Real.log (n : ℝ) ^ (e0 * E1 + 1) ∧
      5 * (pcloseZ e0 K0 n) ^ E1 ≤ n := by
  set K1 : ℝ := 2 ^ e0 + 1 + K0 with hK1
  have hK10 : 0 ≤ K1 := by positivity
  obtain ⟨n1, hn1⟩ := pclose_log_pow_le (e0 * E1 + 1)
  have htend : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨n2, hn2⟩ := Filter.eventually_atTop.1
    (htend.eventually (Filter.eventually_atTop.2 ⟨max 1 (K1 ^ E1), fun b hb => hb⟩))
  refine ⟨max n1 (max n2 3), fun n hn => ?_⟩
  have hn1' : n1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2' : n2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : 3 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hℓ : max 1 (K1 ^ E1) ≤ Real.log (n : ℝ) := hn2 n hn2'
  have hℓ1 : (1 : ℝ) ≤ Real.log (n : ℝ) := le_trans (le_max_left _ _) hℓ
  have hℓK : K1 ^ E1 ≤ Real.log (n : ℝ) := le_trans (le_max_right _ _) hℓ
  have hℓ0 : (0 : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hZ := pclose_Z_le e0 he0 K0 n (by omega) hℓ1
  have hZ0 : (0 : ℝ) ≤ (pcloseZ e0 K0 n : ℝ) := Nat.cast_nonneg _
  have hpow : (pcloseZ e0 K0 n : ℝ) ^ E1 ≤ Real.log (n : ℝ) ^ (e0 * E1 + 1) := by
    calc (pcloseZ e0 K0 n : ℝ) ^ E1 ≤ (K1 * Real.log (n : ℝ) ^ e0) ^ E1 :=
          pow_le_pow_left₀ hZ0 hZ E1
      _ = K1 ^ E1 * Real.log (n : ℝ) ^ (e0 * E1) := by
          rw [mul_pow, ← Real.rpow_natCast (Real.log (n : ℝ) ^ e0) E1, ← Real.rpow_mul hℓ0]
      _ ≤ Real.log (n : ℝ) * Real.log (n : ℝ) ^ (e0 * E1) :=
          mul_le_mul_of_nonneg_right hℓK (Real.rpow_nonneg hℓ0 _)
      _ = Real.log (n : ℝ) ^ (e0 * E1 + 1) := by
          rw [Real.rpow_add_one (by linarith), mul_comm]
  refine ⟨by omega, hℓ1, hpow, ?_⟩
  have h5 := hn1 n hn1'
  have : (5 : ℝ) * (pcloseZ e0 K0 n : ℝ) ^ E1 ≤ (n : ℝ) := by
    calc (5 : ℝ) * (pcloseZ e0 K0 n : ℝ) ^ E1 ≤ 5 * Real.log (n : ℝ) ^ (e0 * E1 + 1) := by
          linarith
      _ ≤ (n : ℝ) := h5
  exact_mod_cast this

end Exploding
