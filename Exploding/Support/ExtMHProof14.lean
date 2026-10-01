/-
Discharge the summability threshold of Mathieu's hole-volume bound and assemble the final
statement: above a density `q₀ < 1` close to one, the Peierls summability condition holds, so
the bound reduces to the localisation of the hole boundary and its isoperimetric size.
-/
import Exploding.Support.ExtMHProof13

namespace Exploding

open LatticeProb MeasureTheory Filter
open scoped BigOperators

variable {d : ℕ}
variable {q : ℝ}

/-- The density threshold above which the summability condition holds. -/
noncomputable def xmh10_q0 (d : ℕ) : ℝ :=
  1 - 1 / (((2 : ℝ) ^ (d + 1)) * (xmh6_K d) + 1)

theorem xmh10_q0_den_pos (d : ℕ) : (0 : ℝ) < ((2 : ℝ) ^ (d + 1)) * (xmh6_K d) + 1 := by
  positivity

theorem xmh10_q0_nonneg (d : ℕ) : 0 ≤ xmh10_q0 d := by
  rw [xmh10_q0]
  have hden := xmh10_q0_den_pos d
  have h1 : 1 / (((2 : ℝ) ^ (d + 1)) * (xmh6_K d) + 1) ≤ 1 := by
    rw [div_le_one hden]
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ (d + 1)) * (xmh6_K d) := by positivity
    linarith
  linarith

theorem xmh10_q0_lt_one (d : ℕ) : xmh10_q0 d < 1 := by
  rw [xmh10_q0]
  have : 0 < 1 / (((2 : ℝ) ^ (d + 1)) * (xmh6_K d) + 1) := by positivity
  linarith

/-- Above `xmh10_q0 d` the summability condition of `xmh6_Summability` holds. -/
theorem xmh10_q0_good (d : ℕ) : ∀ q : ℝ, xmh10_q0 d < q → q ≤ 1 → xmh6_Summability d q := by
  intro q hq h1
  have hden := xmh10_q0_den_pos d
  have hlt : 1 - q < 1 / (((2 : ℝ) ^ (d + 1)) * (xmh6_K d) + 1) := by
    rw [xmh10_q0] at hq; linarith
  refine ⟨(lt_of_le_of_lt (xmh10_q0_nonneg d) hq).le, h1, ?_⟩
  have hreal : ((2 : ℝ) ^ (d + 1)) * (xmh6_K d) * (1 - q) < 1 := by
    by_cases hq0 : (0 : ℝ) ≤ 1 - q
    · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ ((2 : ℝ) ^ (d + 1)) * (xmh6_K d) by positivity)
        with h0 | h0
      · rw [← h0, zero_mul]; norm_num
      · refine (mul_lt_mul_of_pos_left hlt h0).trans_le ?_
        rw [mul_one_div, div_le_one hden]
        nlinarith [show (0 : ℝ) < (2 : ℝ) ^ (d + 1) by positivity,
          show (0 : ℝ) ≤ (xmh6_K d) by positivity]
    · have hlt0 : 1 - q < 0 := not_le.mp hq0
      have hnn : (0 : ℝ) ≤ ((2 : ℝ) ^ (d + 1)) * (xmh6_K d) := by positivity
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hnn hlt0.le]
  have heq : ((2 : ENNReal) ^ d * ((xmh6_K d : ENNReal) * ENNReal.ofReal (1 - q))) * 2
      = ENNReal.ofReal (((2 : ℝ) ^ (d + 1)) * (xmh6_K d) * (1 - q)) := by
    by_cases hq0 : (0 : ℝ) ≤ 1 - q
    · rw [show (2 : ENNReal) ^ d = ENNReal.ofReal ((2 : ℝ) ^ d) by
          rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat],
        show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by rw [ENNReal.ofReal_ofNat],
        show (xmh6_K d : ENNReal) = ENNReal.ofReal (xmh6_K d) by rw [ENNReal.ofReal_natCast]]
      have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ d := by positivity
      have hK : (0 : ℝ) ≤ (xmh6_K d) := by positivity
      have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ d * ((xmh6_K d) * (1 - q)) :=
        mul_nonneg h2d (mul_nonneg hK hq0)
      rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul h2d, ← ENNReal.ofReal_mul h3]
      congr 1
      ring
    · have hlt0 : 1 - q ≤ 0 := (not_le.mp hq0).le
      rw [ENNReal.ofReal_of_nonpos hlt0, mul_zero, mul_zero, zero_mul]
      rw [ENNReal.ofReal_of_nonpos]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlt0
  rw [heq, ENNReal.ofReal_lt_one]
  exact hreal

/-- **Mathieu's hole-volume bound**, with the summability threshold discharged. -/
theorem xmh10_proved
    (hsize : ∀ (d : ℕ) (_hd : 2 ≤ d) (q : ℝ), 0 < q → q ≤ 1 → xmh7_Size d q)
    (hloc : ∀ (d : ℕ) (_hd : 2 ≤ d) (q : ℝ), 0 < q → q ≤ 1 → xmh7_Localized d q) :
    External.MathieuHoleVolume :=
  xmh9_proved (fun d _ => xmh10_q0 d) (fun d _ => xmh10_q0_lt_one d) (fun d _ q h1 h2 => xmh10_q0_good d q h1 h2)
    (fun d hd q h1 h2 => hloc d hd q (lt_of_le_of_lt (xmh10_q0_nonneg d) h1) h2)
    (fun d hd q h1 h2 => hsize d hd q (lt_of_le_of_lt (xmh10_q0_nonneg d) h1) h2)

end Exploding

namespace Exploding

open LatticeProb MeasureTheory Filter

variable {d : ℕ}
variable {q : ℝ}

/-- The isoperimetric size of the hole boundary follows from the edge-isoperimetric
inequality and the arithmetic comparison of the threshold. -/
theorem xmh10_Size (hd : 2 ≤ d) (h : xmh4_edgeIso d)
    (harith : ∀ n : ℕ, (xmh4_m n : ℝ) ≤ (xmh3_V n) ^ (((d : ℝ) - 1) / d) / d)
    (huniq : xmh8_UniqueOpen d q) : xmh7_Size d q := by
  filter_upwards [huniq] with ω huniq C hC n x hx hxC hvol
  set B := componentIn Cᶜ x with hBdef
  have hxcompl : x ∈ Cᶜ := by simpa using hxC
  have hBfin : B.Finite := huniq C hC x hxC
  have hxB : x ∈ B := ⟨hxcompl, hxcompl, SimpleGraph.Reachable.refl _⟩
  have htofin : hBfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]; exact ⟨x, hxB⟩
  have hiso := xmh4_innerBoundary_iso hd h hBfin.toFinset htofin
  have hbnd_eq : innerBoundary B = innerBoundary (hBfin.toFinset : Set (Site d)) := by
    rw [hBfin.coe_toFinset]
  have hcard : (hBfin.toFinset.card : ℝ) = (B.ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card B hBfin]
  rw [hbnd_eq]
  have hnonneg : (0 : ℝ) ≤ xmh3_V n := by rw [xmh3_V]; positivity
  have he : (0 : ℝ) ≤ ((d : ℝ) - 1) / d := by
    apply div_nonneg
    · have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
      linarith
    · positivity
  have h1 : (xmh3_V n) ^ (((d : ℝ) - 1) / d) ≤ (B.ncard : ℝ) ^ (((d : ℝ) - 1) / d) :=
    Real.rpow_le_rpow hnonneg hvol he
  have hreal : (xmh4_m n : ℝ) ≤ ((innerBoundary (hBfin.toFinset : Set (Site d))).ncard : ℝ) := by
    calc (xmh4_m n : ℝ) ≤ (xmh3_V n) ^ (((d : ℝ) - 1) / d) / d := harith n
      _ ≤ (B.ncard : ℝ) ^ (((d : ℝ) - 1) / d) / d := by
          apply div_le_div_of_nonneg_right h1; positivity
      _ = (hBfin.toFinset.card : ℝ) ^ (((d : ℝ) - 1) / d) / d := by rw [hcard]
      _ ≤ ((innerBoundary (hBfin.toFinset : Set (Site d))).ncard : ℝ) := by exact_mod_cast hiso
  exact_mod_cast hreal

end Exploding
