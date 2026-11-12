/-
Kingman's subadditive ergodic theorem for a nonnegative cocycle with a uniform linear
upper bound `g n ≤ C n + K`.  The bound supplies the integrability of `g 1` that
`LatticeProb.ae_tendsto_div` needs; ergodicity makes the limit constant.
-/
import Exploding.Support.GLWProof2
import LatticeProb.Prob.Kingman
import Mathlib.Dynamics.Ergodic.Function

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory

namespace Exploding

/-- **Kingman's theorem under a uniform linear bound.**  A nonnegative subadditive
cocycle over a measure-preserving ergodic map with `g n ≤ C n + K` almost surely,
for constants `C` and `K`, has an almost-sure limit `g n / n → L`.  The bound makes
`g 1` integrable; the limit comes from `LatticeProb.ae_tendsto_gLow` and the
ergodicity of `T`, which makes the a.e.-invariant limit `gLow` almost surely
constant. -/
theorem mk_kingman_linear_uniform {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (herg : Ergodic T μ)
    (g : ℕ → Ω → ℝ) (hsub : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x))
    (hg : ∀ n x, 0 ≤ g n x) (hgm : ∀ n, Measurable (g n))
    (C K : ℝ) (hbound : ∀ᵐ x ∂μ, ∀ n : ℕ, g n x ≤ C * n + K) :
    ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (nhds L) := by
  have hg1 : Integrable (g 1) μ := by
    refine Integrable.of_bound (hgm 1).aestronglyMeasurable (max (C + K) 0) ?_
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hg 1 x)]
    have h1 : g 1 x ≤ C + K := by simpa using hx 1
    exact le_trans h1 (le_max_left _ _)
  have hg' : ∀ n y, 1 ≤ n → 0 ≤ g n y := fun n y _ => hg n y
  have hlow : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (nhds (gLow g x)) :=
    LatticeProb.ae_tendsto_gLow hT hsub hg' hgm hg1
  have hinv : gLow g ∘ T =ᵐ[μ] gLow g := LatticeProb.ae_gLow_comp hT hsub hg' hgm hg1
  obtain ⟨c, hc⟩ :=
    herg.ae_eq_const_of_ae_eq_comp₀ (LatticeProb.measurable_gLow hgm).nullMeasurable hinv
  refine ⟨c, ?_⟩
  filter_upwards [hlow, hc] with x hx hxc
  simpa [hxc] using hx


end Exploding
