/-
Closedness of the domination order on finite fields of bits, an ingredient of the
compactness route to the global coupling.
-/
import Exploding.Support.ExtLSSProofGlobal2
import Exploding.Support.RNProofStrassen

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Exploding

attribute [local instance] Classical.propDecidable

variable {S : Type}

/-- The coordinatewise domination order on a finite product of bits is closed. -/
theorem xlss10_order_isClosed {I : Type*} [Fintype I] :
    IsClosed {z : (I → Bool) × (I → Bool) | ∀ i, z.1 i = true → z.2 i = true} := by
  rw [show {z : (I → Bool) × (I → Bool) | ∀ i, z.1 i = true → z.2 i = true} =
      ⋂ i, ({z : (I → Bool) × (I → Bool) | z.1 i = false} ∪ {z | z.2 i = true}) from by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union]
    constructor
    · intro h i
      by_cases hz : z.1 i = true
      · exact Or.inr (h i hz)
      · exact Or.inl (by simpa using hz)
    · intro h i hz
      rcases h i with h' | h'
      · exact absurd hz (by simpa using h')
      · exact h']
  exact isClosed_iInter fun i => (isClosed_discrete _).union (isClosed_discrete _)

/-- On a finite set of coordinates the finite-coordinate domination yields a coupling of the
product law below the given law. -/
theorem xlss10_finite_coupling [Countable S] (I : Finset S) (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ] (ρ γ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hthin : ∀ T : Finset S, ∃ w, XlssThin μ ρ γ T w) :
    ∃ π : Measure ((I → Bool) × (I → Bool)),
      IsProbabilityMeasure π ∧
      π.map Prod.fst = Measure.pi (fun _ : I => bitLaw ρ) ∧
      π.map Prod.snd = μ.map I.restrict ∧
      π {z | ¬ (∀ i, z.1 i = true → z.2 i = true)} = 0 := by
  classical
  haveI hbit : IsProbabilityMeasure (bitLaw ρ) := xlss6_bitLaw_isProb hρ0 hρ1
  haveI hpi : IsProbabilityMeasure (Measure.pi (fun _ : I => bitLaw ρ)) := by
    rw [← Measure.infinitePi_eq_pi]
    infer_instance
  haveI hmapμ : IsProbabilityMeasure (μ.map I.restrict) :=
    Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable I.restrict μ)
  refine rn_strassen (fun x y : I → Bool => ∀ i, x i = true → y i = true)
    (fun _ _ => id) (fun _ _ _ hxy hyz i hi => hyz i (hxy i hi))
    (xlss10_order_isClosed) _ _ ?_
  intro A hA hinc
  obtain ⟨w, hw⟩ := hthin I
  have hmap : (bernoulliProduct S ρ).map I.restrict = Measure.pi (fun _ : I => bitLaw ρ) := by
    change (Measure.infinitePi (fun _ : S => bitLaw ρ)).map I.restrict = _
    rw [Measure.infinitePi_map_restrict]
  have hν : Measure.pi (fun _ : I => bitLaw ρ) A = bernoulliProduct S ρ (I.restrict ⁻¹' A) := by
    rw [← hmap, Measure.map_apply (by fun_prop) hA]
  have hμ : (μ.map I.restrict) A = μ (I.restrict ⁻¹' A) := Measure.map_apply (by fun_prop) hA
  rw [hν, hμ]
  exact xlss7_dom_fin μ ρ γ hρ0 hρ1 I w hw (I.restrict ⁻¹' A) (hA.preimage (by fun_prop))
    (fun x y hxA' hxy => hinc (I.restrict x) (I.restrict y) (fun i hi => hxy i hi) hxA')
    (fun x y hxy => by
      have hres : I.restrict x = I.restrict y := by
        funext i
        exact hxy i i.2
      rw [Set.mem_preimage, Set.mem_preimage, hres])

end Exploding
