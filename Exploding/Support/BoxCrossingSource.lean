import Exploding.Support.Hypotheses

/-!
# Uniform box-crossing probabilities

The box-crossing hypotheses give a uniform lower bound over all translated
boxes, as in the source formulation.
-/

namespace Exploding

open LatticeProb MeasureTheory

/-- Box-crossing probabilities have a uniform strict lower bound over translates. -/
def UniformBoxCrossingHyp (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ k : Fin d → ℕ, (∀ i, 0 < k i) ∧
    ∃ r : ℝ, 1 - δ < r ∧ ∀ j : Site d, r ≤ (P {η | BoxCrossed η k j}).toReal

/-- Strong box-crossing probabilities have a uniform strict lower bound over translates. -/
def UniformStronglyBoxCrossingHyp (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ k : Fin d → ℕ, (∀ i, 0 < k i) ∧
    ∃ r : ℝ, 1 - δ < r ∧ ∀ j : Site d, r ≤ (P {η | StronglyBoxCrossed η k j}).toReal

private theorem pointwise_iff_uniform {α β : Type*} (valid : α → Prop)
    (p : α → β → ENNReal) (hfin : ∀ a b, p a b ≠ ⊤) :
    (∀ δ : ℝ, 0 < δ → ∃ a, valid a ∧ ∀ b, ENNReal.ofReal (1 - δ) < p a b) ↔
    (∀ δ : ℝ, 0 < δ → ∃ a, valid a ∧ ∃ r : ℝ, 1 - δ < r ∧
      ∀ b, r ≤ (p a b).toReal) := by
  constructor
  · intro h δ hδ
    let ε := min δ 1 / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεδ : ε < δ := by dsimp [ε]; have := min_le_left δ (1 : ℝ); linarith
    have hε1 : ε ≤ 1 := by dsimp [ε]; have := min_le_right δ (1 : ℝ); linarith
    obtain ⟨a, ha, hp⟩ := h ε hε
    refine ⟨a, ha, 1 - ε, by linarith, fun b => ?_⟩
    exact le_of_lt ((ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (hfin a b)).mp (hp b))
  · intro h δ hδ
    let ε := min δ 1 / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεδ : ε ≤ δ := by dsimp [ε]; have := min_le_left δ (1 : ℝ); linarith
    have hε1 : ε ≤ 1 := by dsimp [ε]; have := min_le_right δ (1 : ℝ); linarith
    obtain ⟨a, ha, r, hr, hp⟩ := h ε hε
    refine ⟨a, ha, fun b => ?_⟩
    apply lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (show 1 - δ ≤ 1 - ε by linarith))
    exact (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (hfin a b)).mpr
      (lt_of_lt_of_le hr (hp b))

/-- The pointwise box-crossing hypothesis is equivalent to its uniform form. -/
theorem boxCrossingHyp_iff_uniform (d : ℕ) (P : Measure (Site d → ℤ))
    [IsProbabilityMeasure P] : BoxCrossingHyp d P ↔ UniformBoxCrossingHyp d P := by
  exact pointwise_iff_uniform _ _ (fun _ _ => measure_ne_top _ _)

/-- The pointwise strong box-crossing hypothesis is equivalent to its uniform form. -/
theorem stronglyBoxCrossingHyp_iff_uniform (d : ℕ) (P : Measure (Site d → ℤ))
    [IsProbabilityMeasure P] :
    StronglyBoxCrossingHyp d P ↔ UniformStronglyBoxCrossingHyp d P := by
  exact pointwise_iff_uniform _ _ (fun _ _ => measure_ne_top _ _)

end Exploding
