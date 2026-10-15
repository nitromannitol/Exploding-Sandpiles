import Exploding.Support.ArxivCrossingTerminal

/-!
# Crossing bounds for the terminal and deadline event

The actual toy law has a large-scale crossing bound for the corrected-source
event requiring terminal value one and a positive volume deadline. No extra
measurability or background assumptions are imposed on that event.
-/

namespace Exploding

open LatticeProb MeasureTheory

/-- The corrected-source crossing bound for the event with terminal value one and its positive
volume-bounded crossing deadline, under the actual toy law for the full range `0 < p ≤ 1`. -/
theorem crossing_time_terminal_bound (d : ℕ) (hd : 2 ≤ d)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧
      ENNReal.ofReal (1 - δ) ≤ toyLaw d p
        {η : Site d → ℤ |
          ∀ (i : Fin d) (z : Site d), z ∈ closureN (cube d k) →
            (∀ x ∈ cube d k, ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
              crossOdo η k i z t x = 1) ∧
            (∃ n : ℕ, 1 ≤ n ∧ n ≤ k ^ d ∧
              ∀ x ∈ cube d k, crossOdo η k i z n x = 1)
        } := by
  let terminalEvent (k : ℕ) : Set (Site d → ℤ) :=
    {η |
      ∀ (i : Fin d) (z : Site d), z ∈ closureN (cube d k) →
        (∀ x ∈ cube d k, ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
          crossOdo η k i z t x = 1) ∧
        (∃ n : ℕ, 1 ≤ n ∧ n ≤ k ^ d ∧
          ∀ x ∈ cube d k, crossOdo η k i z n x = 1)}
  rcases lt_or_eq_of_le hp1 with hp_lt | hp_eq
  · obtain ⟨k, hk, hgood⟩ := aux_ct_assemble d hd p hp hp_lt δ hδ
    refine ⟨k, hk, ?_⟩
    have hsets : {η | GoodCube η k} =ᵐ[toyLaw d p] terminalEvent k := by
      filter_upwards [toyLaw_ae_goodCube_terminal_iff d hd p hp hp1] with η hη
      exact propext (hη k)
    calc
      ENNReal.ofReal (1 - δ) ≤ toyLaw d p {η | GoodCube η k} := hgood
      _ = toyLaw d p (terminalEvent k) := measure_congr hsets
  · subst p
    obtain ⟨k, hk, hgood⟩ := crossing_time_p1 d hd δ hδ
    refine ⟨k, hk, ?_⟩
    have hsets : {η | GoodCube η k} =ᵐ[toyLaw d (1 : ℝ)] terminalEvent k := by
      filter_upwards [toyLaw_ae_goodCube_terminal_iff d hd 1 hp hp1] with η hη
      exact propext (hη k)
    calc
      ENNReal.ofReal (1 - δ) ≤ toyLaw d (1 : ℝ) {η | GoodCube η k} := hgood
      _ = toyLaw d (1 : ℝ) (terminalEvent k) := measure_congr hsets

end Exploding
