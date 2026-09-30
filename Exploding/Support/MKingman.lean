/-
A moment-free Kingman subadditive ergodic theorem, shared by the generalized
last-wave node (`glw2_KingmanCore`) and the toy-law last-wave node (the first
conjunct of `Exploding.Frozen.convergence_of_the_last_wave`).

`LatticeProb.ae_tendsto_div` requires `Integrable (g 1)`, which neither use case
supplies.  The statement below keeps only a pointwise eventual linear upper
bound `g n ≤ C n + K(ω)`; the repair of the paper is to induce on the
positive-measure set `{∀ n, g n ≤ C n + K}` and use Kac's lemma.  Here the
uniform-bound case is proved outright, the general case is isolated as the
single proposition `mk_kingman_linear`, and `glw2_KingmanCore` is derived from
it.
-/
import Exploding.Support.GLWProof2
import LatticeProb.Prob.Kingman
import Mathlib.Dynamics.Ergodic.Function

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory

namespace Exploding

/-- **Moment-free Kingman theorem** (the form both frozen nodes need).  A
nonnegative subadditive cocycle over a measure-preserving ergodic map, with an
almost-sure eventual linear upper bound `g n ≤ C n + K(ω)`, has an almost-sure
limit `g n / n → L`. -/
def mk_kingman_linear : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω), MeasurePreserving T μ μ → Ergodic T μ →
    ∀ (g : ℕ → Ω → ℝ), (∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x)) →
    (∀ n x, 0 ≤ g n x) → (∀ n, Measurable (g n)) →
    (∃ C : ℝ, ∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K) →
    ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => g n x / (n : ℝ)) atTop (nhds L)

/-- The uniform-bound case of `mk_kingman_linear`, proved from
`LatticeProb.ae_tendsto_gLow` and the ergodicity of `T` (which makes the
a.e.-invariant limit `gLow` almost surely constant). -/
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

/-- `glw2_KingmanCore` is an immediate specialization of `mk_kingman_linear`. -/
theorem glw2_KingmanCore_of_mk (h : mk_kingman_linear) : glw2_KingmanCore := by
  intro Ω _ μ _ T hT herg g hsub hg hgm C hlin K _hA _hApos
  exact h (μ := μ) (T := T) hT herg g hsub hg hgm ⟨C, hlin⟩

end Exploding
