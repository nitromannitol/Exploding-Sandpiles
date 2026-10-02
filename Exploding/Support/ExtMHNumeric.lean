/-
The numeric comparison behind the hole-volume bound: a natural number whose square dominates
`(log n)^{5/2}` dominates `⌊log₂ n⌋`, because `(k log 2)^{5/2}` exceeds `k - 1` for every
natural `k`.  This is where the exponent `5/2` of Mathieu's lemma is used.
-/
import Mathlib
import Exploding.Support.ExtMHProof8

namespace Exploding

/-- `(k - 1)^4 < (k · log 2)^5` for every natural `k ≥ 1`. -/
theorem xmn_poly (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) - 1) ^ 4 < ((k : ℝ) * Real.log 2) ^ 5 := by
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hstep : ((k : ℝ) * 0.6931471803) ^ 5 ≤ ((k : ℝ) * Real.log 2) ^ 5 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left hlog.le (by positivity)
  refine lt_of_lt_of_le ?_ hstep
  rcases le_or_gt 7 k with h7 | h7
  · have h7' : (7 : ℝ) ≤ k := by exact_mod_cast h7
    have hk4 : ((k : ℝ) - 1) ^ 4 ≤ (k : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 4
    have hk4pos : (0 : ℝ) < (k : ℝ) ^ 4 := by positivity
    have hc5 : (0.1599 : ℝ) ≤ 0.6931471803 ^ 5 := by norm_num
    have hprod : (0.1599 : ℝ) * 7 ≤ 0.6931471803 ^ 5 * k :=
      mul_le_mul hc5 h7' (by norm_num) (by positivity)
    calc ((k : ℝ) - 1) ^ 4 ≤ (k : ℝ) ^ 4 := hk4
      _ = 1 * (k : ℝ) ^ 4 := by ring
      _ < (0.6931471803 ^ 5 * (k : ℝ)) * (k : ℝ) ^ 4 := by
          apply mul_lt_mul_of_pos_right _ hk4pos
          linarith
      _ = ((k : ℝ) * 0.6931471803) ^ 5 := by ring
  · interval_cases k <;> norm_num

/-- A natural `N ≥ 1` with `xmh3_V n ≤ N^2` satisfies `xmh4_m n ≤ N`. -/
theorem xmn_m_le_of_sq (n N : ℕ) (hN : 1 ≤ N) (h : xmh3_V n ≤ (N : ℝ) ^ 2) :
    xmh4_m n ≤ N := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hlog : Nat.log 2 n = 0 := by
      interval_cases n <;> simp
    simp [xmh4_m, hlog, hN]
  · set k := Nat.log 2 n with hk
    have hn0 : n ≠ 0 := by omega
    have hk1 : 1 ≤ k := by
      rw [hk]
      exact (Nat.le_log_iff_pow_le (by norm_num) hn0).mpr (by simpa using hn)
    have hm : xmh4_m n = k := by
      show max 1 (Nat.log 2 n) = k
      rw [← hk]
      exact max_eq_right hk1
    rw [hm]
    have hpow : 2 ^ k ≤ n := Nat.pow_log_le_self 2 hn0
    have hpowR : (2 : ℝ) ^ k ≤ (n : ℝ) := by exact_mod_cast hpow
    have hlogle : (k : ℝ) * Real.log 2 ≤ Real.log n := by
      have := Real.log_le_log (by positivity) hpowR
      rwa [Real.log_pow] at this
    have hkl0 : (0 : ℝ) ≤ (k : ℝ) * Real.log 2 :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
    have hV : ((k : ℝ) * Real.log 2) ^ ((5 : ℝ) / 2) ≤ xmh3_V n := by
      unfold xmh3_V
      exact Real.rpow_le_rpow hkl0 hlogle (by norm_num)
    have hsq : ((k : ℝ) * Real.log 2) ^ 5 ≤ (N : ℝ) ^ 4 := by
      have h1 : (((k : ℝ) * Real.log 2) ^ ((5 : ℝ) / 2)) ^ 2 ≤ ((N : ℝ) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hkl0 _) (hV.trans h) 2
      have h2 : (((k : ℝ) * Real.log 2) ^ ((5 : ℝ) / 2)) ^ 2
          = ((k : ℝ) * Real.log 2) ^ 5 := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hkl0,
          show ((5 : ℝ) / 2) * ((2 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
      rw [h2] at h1
      calc ((k : ℝ) * Real.log 2) ^ 5 ≤ ((N : ℝ) ^ 2) ^ 2 := h1
        _ = (N : ℝ) ^ 4 := by ring
    have hlt : ((k : ℝ) - 1) ^ 4 < (N : ℝ) ^ 4 := lt_of_lt_of_le (xmn_poly k hk1) hsq
    have hkN : (k : ℝ) - 1 < N := lt_of_pow_lt_pow_left₀ 4 (by positivity) hlt
    have hkN' : k < N + 1 := by exact_mod_cast (by linarith : (k : ℝ) < (N : ℝ) + 1)
    omega

end Exploding
