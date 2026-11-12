/-
Continuation of `MKingman4.lean`.

Kingman's theorem for a subadditive process `h` that is bounded below by a linear
function `-c n` and bounded above by a constant `M`.  The shifted process
`g n = h n + c n` is nonnegative, bounded above by `c n + M`, and `g 1` is bounded
hence integrable, so `mk_kingman_linear_uniform` applies.
-/
import Exploding.Support.MKingman4
import Mathlib.Dynamics.Ergodic.Function

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory

namespace Exploding

variable {Ω : Type}

/-- **Kingman's theorem for a uniformly bounded subadditive process.**  If `h` is
subadditive, bounded below by `-c n` and bounded above by the *constant* `M`,
then `h n / n` converges a.s.: shift to the nonnegative process
`g n = h n + c n`, whose first term is bounded (hence integrable) and which is
dominated by `c n + M`, and apply `mk_kingman_linear_uniform`. -/
theorem mk5_boundedAbove_uniform [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (herg : Ergodic T μ)
    (h : ℕ → Ω → ℝ) (hsub : ∀ m n x, h (m + n) x ≤ h m x + h n (T^[m] x))
    (hlow : ∃ c : ℝ, ∀ n x, -c * n ≤ h n x) (hgm : ∀ n, Measurable (h n))
    (M : ℝ) (hM : ∀ n x, h n x ≤ M) :
    ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => h n x / (n : ℝ)) atTop (nhds L) := by
  obtain ⟨c, hc⟩ := hlow
  set g : ℕ → Ω → ℝ := fun n x => h n x + c * n with hg
  have hsubg : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x) := by
    intro m n x
    have := hsub m n x
    simp only [hg]
    push_cast
    linarith
  have hg0 : ∀ n x, 0 ≤ g n x := by
    intro n x
    have := hc n x
    simp only [hg]
    linarith
  have hgm : ∀ n, Measurable (g n) := fun n => (hgm n).add measurable_const
  have hbound : ∀ᵐ x ∂μ, ∀ n : ℕ, g n x ≤ c * n + M := by
    filter_upwards with x n
    have := hM n x
    simp only [hg]
    linarith
  obtain ⟨L, hL⟩ := mk_kingman_linear_uniform μ T hT herg g hsubg hg0 hgm c M hbound
  refine ⟨L - c, ?_⟩
  filter_upwards [hL] with x hx
  have hx' : Tendsto (fun n : ℕ => g n x / (n : ℝ) - c) atTop (nhds (L - c)) :=
    hx.sub tendsto_const_nhds
  refine hx'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [hg]
  field_simp
  ring

end Exploding
