/-
Continuation of `MKingman3.lean`.

The induced-system route of `MKingman2`/`MKingman3` studies a subadditive cocycle
through the first-return map `mk2_inducedMap` to a set of positive measure, the
normalised restriction `mk3_normalizedRestrict` and the cumulative return sequence
`mk2_returnSeq`.  This file contributes the limit arithmetic of that route:
convergence of the induced cocycle `G k = g (r_k)` divided by `k`, together with
Birkhoff's theorem for the cumulative return time `r_k`, gives convergence of
`g (r_k) / r_k`.
-/
import Exploding.Support.MKingman3
import Mathlib.Dynamics.Ergodic.Function

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory

namespace Exploding

variable {Ω : Type}

/-- The cumulative return sequence is the sum of the successive first-return
times along the induced orbit: `r k = ∑_{j<k} r_1(T_A^j x)`. -/
theorem mk4_returnSeq_eq_sum [MeasurableSpace Ω] (T : Ω → Ω) (A : Set Ω) (x : Ω) (k : ℕ) :
    mk2_returnSeq T A x k
      = ∑ j ∈ Finset.range k, mk2_returnTime T A ((mk2_inducedMap T A)^[j] x) := by
  induction k with
  | zero => simp [mk2_returnSeq]
  | succ k ih =>
      rw [mk2_returnSeq, ih, Finset.sum_range_succ]

/-- The cumulative return sequence is nondecreasing, being a sum of nonnegative
terms. -/
theorem mk4_returnSeq_mono [MeasurableSpace Ω] (T : Ω → Ω) (A : Set Ω) (x : Ω) :
    Monotone (mk2_returnSeq T A x) := by
  intro j k hjk
  rw [mk4_returnSeq_eq_sum, mk4_returnSeq_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hjk)
    (fun i _ _ => Nat.zero_le _)

/-- **Arithmetic core of the identification of the limit.**  If `G k / k → L` and
the cumulative return time satisfies `r k / k → ρ` with `ρ > 0`, then
`G k / r k → L / ρ`. -/
theorem mk4_tendsto_div_of_div (G r : ℕ → ℝ) (L ρ : ℝ) (hρ : 0 < ρ)
    (hG : Tendsto (fun k : ℕ => G k / (k : ℝ)) atTop (nhds L))
    (hr : Tendsto (fun k : ℕ => r k / (k : ℝ)) atTop (nhds ρ)) :
    Tendsto (fun k : ℕ => G k / r k) atTop (nhds (L / ρ)) := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hdiv : Tendsto (fun k : ℕ => (G k / (k : ℝ)) / (r k / (k : ℝ))) atTop (nhds (L / ρ)) :=
    hG.div hr hρne
  refine hdiv.congr' ?_
  filter_upwards [hr.eventually_ne hρne, eventually_gt_atTop 0] with k hrk hk
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrkne : r k ≠ 0 := fun h => hrk (by rw [h, zero_div])
  field_simp

/-- **Identification of the limit along the return times.**  If the induced
cocycle `G k = g (r_k)` has normalised limit `L` and the cumulative return time
has normalised limit `ρ > 0`, then `g (r_k) / r_k` converges to `L / ρ` on the
induced space.  With Birkhoff's theorem for the return time, `ρ` is the mean
return time `∫ r_1 dμ_A = 1 / μ(A)`, and the limit is `L · μ(A)`. -/
theorem mk4_return_limit [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω → Ω) (g : ℕ → Ω → ℝ) (A : Set Ω) (L ρ : ℝ) (hρ : 0 < ρ)
    (hG : ∀ᵐ x ∂(mk3_normalizedRestrict μ A),
      Tendsto (fun k : ℕ => g (mk2_returnSeq T A x k) x / (k : ℝ)) atTop (nhds L))
    (hr : ∀ᵐ x ∂(mk3_normalizedRestrict μ A),
      Tendsto (fun k : ℕ => (mk2_returnSeq T A x k : ℝ) / (k : ℝ)) atTop (nhds ρ)) :
    ∀ᵐ x ∂(mk3_normalizedRestrict μ A),
      Tendsto (fun k : ℕ => g (mk2_returnSeq T A x k) x / (mk2_returnSeq T A x k : ℝ))
        atTop (nhds (L / ρ)) := by
  filter_upwards [hG, hr] with x hGx hrx
  exact mk4_tendsto_div_of_div _ _ L ρ hρ hGx hrx

end Exploding
