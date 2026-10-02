/-
The density threshold of Mathieu's hole bound: above `1 - 1 / (2 · 6^d (K + 1))`, where `K` is
the star-count constant, the Peierls bounds of the enlarged bad event are summable, and so
are those of the original event.
-/
import Exploding.Support.ExtMHProof10

namespace Exploding

open scoped ENNReal

/-- The density threshold. -/
noncomputable def xmt_q₀ (d : ℕ) : ℝ := 1 - 1 / (2 * 6 ^ d * ((xmh6_K d : ℝ) + 1))

/-- The denominator of the threshold is positive. -/
theorem xmt_A_pos (d : ℕ) : (0 : ℝ) < 2 * 6 ^ d * ((xmh6_K d : ℝ) + 1) := by positivity

/-- The denominator of the threshold is at least one. -/
theorem xmt_one_le_A (d : ℕ) : (1 : ℝ) ≤ 2 * 6 ^ d * ((xmh6_K d : ℝ) + 1) := by
  have h1 : (1 : ℝ) ≤ 6 ^ d := one_le_pow₀ (by norm_num)
  have h2 : (0 : ℝ) ≤ (xmh6_K d : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem xmt_q₀_lt_one (d : ℕ) : xmt_q₀ d < 1 := by
  unfold xmt_q₀
  have : (0 : ℝ) < 1 / (2 * 6 ^ d * ((xmh6_K d : ℝ) + 1)) := by positivity
  linarith

/-- The real form of the summability condition above the threshold. -/
theorem xmt_real_bound {d : ℕ} {q : ℝ} (hq : xmt_q₀ d < q) :
    6 ^ d * ((xmh6_K d : ℝ) * (1 - q)) * 2 < 1 := by
  have hApos := xmt_A_pos d
  have hlt : 1 - q < 1 / (2 * 6 ^ d * ((xmh6_K d : ℝ) + 1)) := by
    unfold xmt_q₀ at hq
    linarith
  have hK : (0 : ℝ) ≤ xmh6_K d := Nat.cast_nonneg _
  have hK1 : (xmh6_K d : ℝ) + 1 ≠ 0 := by positivity
  have h6ne : (6 : ℝ) ^ d ≠ 0 := by positivity
  calc 6 ^ d * ((xmh6_K d : ℝ) * (1 - q)) * 2
      = (2 * 6 ^ d * (xmh6_K d : ℝ)) * (1 - q) := by ring
    _ ≤ (2 * 6 ^ d * (xmh6_K d : ℝ)) * (1 / (2 * 6 ^ d * ((xmh6_K d : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hlt.le (by positivity)
    _ = (xmh6_K d : ℝ) / ((xmh6_K d : ℝ) + 1) := by
        field_simp
    _ < 1 := by
        rw [div_lt_one (by positivity)]
        linarith

/-- Above the threshold, the enlarged Peierls bounds are summable. -/
theorem xmt_summability {d : ℕ} {q : ℝ} (hq : xmt_q₀ d < q) (hq1 : q ≤ 1) :
    0 ≤ q ∧ q ≤ 1 ∧
      ((6 : ENNReal) ^ d * ((xmh6_K d : ENNReal) * ENNReal.ofReal (1 - q))) * 2 < 1 := by
  have hA1 := xmt_one_le_A d
  have hApos := xmt_A_pos d
  refine ⟨?_, hq1, ?_⟩
  · have h1 : 1 / (2 * 6 ^ d * ((xmh6_K d : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one hApos]
      exact hA1
    unfold xmt_q₀ at hq
    linarith
  · have hreal := xmt_real_bound hq
    have hnn : 0 ≤ 1 - q := by linarith
    have hK : (0 : ℝ) ≤ xmh6_K d := Nat.cast_nonneg _
    have h6 : (0 : ℝ) ≤ 6 ^ d := by positivity
    have hcast : ((6 : ENNReal) ^ d * ((xmh6_K d : ENNReal) * ENNReal.ofReal (1 - q))) * 2
        = ENNReal.ofReal (6 ^ d * ((xmh6_K d : ℝ) * (1 - q)) * 2) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul h6, ENNReal.ofReal_mul hK,
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast]
      norm_num
    rw [hcast]
    exact ENNReal.ofReal_lt_one.mpr hreal

/-- The enlarged summability condition implies the original one. -/
theorem xmt_xmh6_of {d : ℕ} {q : ℝ}
    (h : 0 ≤ q ∧ q ≤ 1 ∧
      ((6 : ENNReal) ^ d * ((xmh6_K d : ENNReal) * ENNReal.ofReal (1 - q))) * 2 < 1) :
    xmh6_Summability d q := by
  refine ⟨h.1, h.2.1, lt_of_le_of_lt ?_ h.2.2⟩
  gcongr
  norm_num

end Exploding
