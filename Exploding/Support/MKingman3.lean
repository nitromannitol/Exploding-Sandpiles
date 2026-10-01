/-
Continuation of `MKingman2.lean`: the measure-theoretic package for the
induced (first-return) system, and the Kingman step on the induced cocycle.

`MKingman2.lean` built the first-return map `mk2_inducedMap` on `A` and the
induced cocycle `G k y = g (r_k y) y`.  This file adds the normalised restricted
measure `μ_A = μ(A)⁻¹ • μ|A`, records the Kac/ergodicity package as
`mk3_kac`, and derives convergence along return times from it.  The remaining
transfer from return times to all `n` is the open step.
-/
import Exploding.Support.MKingman2
import Mathlib.Dynamics.Ergodic.Function

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory

namespace Exploding

variable {Ω : Type}

/-- The normalised restriction of `μ` to `A`, `μ_A = μ(A)⁻¹ • μ|A`. -/
noncomputable def mk3_normalizedRestrict [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) : Measure Ω :=
  (μ A)⁻¹ • μ.restrict A

/-- `μ_A` is a probability measure whenever `A` is measurable of positive
measure (and `μ` is a probability measure, so `μ A < ∞`). -/
theorem mk3_normalizedRestrict_isProbability [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) (hA0 : μ A ≠ 0) :
    IsProbabilityMeasure (mk3_normalizedRestrict μ A) := by
  refine ⟨?_⟩
  rw [mk3_normalizedRestrict, Measure.smul_apply, Measure.restrict_apply' hA, Set.univ_inter]
  exact ENNReal.inv_mul_cancel hA0 (measure_ne_top μ A)

/-- The Kac/ergodicity package for the induced system on `A`: `A` is measurable
of positive measure, `mk2_inducedMap` preserves the normalised restriction
`μ_A`, is ergodic for it, and the first return time is `μ_A`-integrable.  This
is the paper's "the successive return times to `A` form a subadditive process for
the induced transformation, and the first term is integrable by Kac's lemma". -/
def mk3_kac [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (A : Set Ω) : Prop :=
  MeasurableSet A ∧ 0 < μ A ∧
  MeasurePreserving (mk2_inducedMap T A) (mk3_normalizedRestrict μ A)
    (mk3_normalizedRestrict μ A) ∧
  Ergodic (mk2_inducedMap T A) (mk3_normalizedRestrict μ A) ∧
  Integrable (fun x => (mk2_returnTime T A x : ℝ)) (mk3_normalizedRestrict μ A)

/-- **Kingman on the induced cocycle**: under the Kac package, the induced
cocycle `G k y = g (r_k y) y` has an almost-sure limit along the return times.
This is the genuine subadditive-ergodic step of the route; the hypotheses
`hGmeas`/`hG1` are the (true) measurability and integrability of `G 1`, which
follow from the measurability of `g`, the return time and its Kac
integrability. -/
theorem mk3_return_convergence [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (g : ℕ → Ω → ℝ) (A : Set Ω)
    (hkac : mk3_kac μ T A)
    (hsub : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x))
    (hg : ∀ n x, 0 ≤ g n x) (_hgm : ∀ n, Measurable (g n))
    (hGmeas : ∀ k, Measurable (fun x => g (mk2_returnSeq T A x k) x))
    (hG1 : Integrable (fun x => g (mk2_returnSeq T A x 1) x)
      (mk3_normalizedRestrict μ A)) :
    ∃ L : ℝ, ∀ᵐ x ∂(mk3_normalizedRestrict μ A),
      Tendsto (fun k : ℕ => g (mk2_returnSeq T A x k) x / (k : ℝ)) atTop (nhds L) := by
  have hprob := mk3_normalizedRestrict_isProbability μ hkac.1 (ne_of_gt hkac.2.1)
  haveI := hprob
  set G : ℕ → Ω → ℝ := fun k x => g (mk2_returnSeq T A x k) x with hG
  have hGsub : SubadditiveAlong (mk2_inducedMap T A) G := by
    intro m n x
    exact mk2_return_cocycle_subadditive T A g hsub x m n
  have hGnonneg : ∀ k y, 1 ≤ k → 0 ≤ G k y := fun k y _ => hg _ _
  have hlow : ∀ᵐ x ∂(mk3_normalizedRestrict μ A),
      Tendsto (fun k : ℕ => G k x / (k : ℝ)) atTop (nhds (gLow G x)) :=
    LatticeProb.ae_tendsto_gLow hkac.2.2.1 hGsub hGnonneg hGmeas hG1
  have hinv : gLow G ∘ (mk2_inducedMap T A) =ᵐ[mk3_normalizedRestrict μ A] gLow G :=
    LatticeProb.ae_gLow_comp hkac.2.2.1 hGsub hGnonneg hGmeas hG1
  obtain ⟨c, hc⟩ := hkac.2.2.2.1.ae_eq_const_of_ae_eq_comp₀
    (LatticeProb.measurable_gLow hGmeas).nullMeasurable hinv
  refine ⟨c, ?_⟩
  filter_upwards [hlow, hc] with x hx hxc
  simpa [hxc, hG] using hx

end Exploding
