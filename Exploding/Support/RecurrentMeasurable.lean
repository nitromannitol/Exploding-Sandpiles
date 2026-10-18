/-
Measurability of the recurrence events of `RecurrentOn` and `Recurrent`
(`Exploding.Support.Vocab`), and the source-facing consumer of `RecurrentLaw` on the
Section-5 state space `Ω = {η // InOmega d ηmin η}`
(`paper/corrected-arxiv/exploding-corrected-arxiv.tex`, lines 1231–1248 and 2377–2384).

Each frozen odometer `η ↦ fodo (Vᶜ) η w₀ t x` is measurable in the background
(`bc_fodo_measurable`), so the equality events `{fodo … = 1}` are measurable.
`RecurrentOn η V` is a countable intersection of guarded such events over times `t` and sites
`x`, and `Recurrent η` a countable intersection of those over finite domains `V`.
Nothing beyond the definitions is assumed.
-/
import Exploding.Support.BCProofAux

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The level set `{η | fodo S η w₀ t x = 1}` of the frozen odometer is measurable: it is the
preimage of `{1}` under the measurable map of `bc_fodo_measurable`. -/
theorem measurableSet_fodo_eq_one (S : Set (Site d)) (w0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    MeasurableSet {η : Site d → ℤ | fodo S η w0 t x = 1} :=
  bc_fodo_measurable S w0 t x (measurableSet_singleton 1)

open scoped Classical in
/-- `{η | RecurrentOn η V}` is measurable: a countable intersection, over times `t` and sites
`x`, of guarded equality events of the frozen odometer, which are measurable by
`measurableSet_fodo_eq_one`. -/
theorem measurableSet_recurrentOn (V : Finset (Site d)) :
    MeasurableSet {η : Site d → ℤ | RecurrentOn η V} := by
  have hset : {η : Site d → ℤ | RecurrentOn η V} =
      ⋂ t : ℕ, ⋂ x : Site d, {η : Site d → ℤ | (V.card ≤ t ∧ x ∈ V) →
        fodo ((↑V : Set (Site d))ᶜ) η
          (fun y => if y ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0) t x = 1} := by
    ext η
    simp only [RecurrentOn, Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h t x hc => h t hc.1 x hc.2, fun h t hc x hx => h t x ⟨hc, hx⟩⟩
  rw [hset]
  exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun x =>
    (MeasurableSet.const (V.card ≤ t ∧ x ∈ V)).imp (measurableSet_fodo_eq_one _ _ t x)

/-- `{η | Recurrent η}` is measurable: a countable intersection over finite domains `V` of the
measurable events `{η | RecurrentOn η V}`. -/
theorem measurableSet_recurrent : MeasurableSet {η : Site d → ℤ | Recurrent η} := by
  have hset : {η : Site d → ℤ | Recurrent η} =
      ⋂ V : Finset (Site d), {η : Site d → ℤ | RecurrentOn η V} := by
    ext η
    simp only [Recurrent, Set.mem_setOf_eq, Set.mem_iInter, iff_self]
  rw [hset]
  exact MeasurableSet.iInter fun V => measurableSet_recurrentOn V

/-- For a probability measure on the background space, `RecurrentLaw` is probability one of the
recurrent event. -/
theorem recurrentLaw_iff_measure_recurrent (P : Measure (Site d → ℤ)) [IsProbabilityMeasure P] :
    RecurrentLaw d P ↔ P {η | Recurrent η} = 1 := by
  unfold RecurrentLaw
  rw [ae_iff]
  exact prob_compl_eq_zero_iff measurableSet_recurrent

/-- On the Section-5 state space `Ω = {η // InOmega d ηmin η}`, the recurrent event is the
preimage of the ambient recurrent event under the inclusion, hence measurable. -/
theorem measurableSet_recurrent_subtype (ηmin : ℤ) :
    MeasurableSet {ω : {η : Site d → ℤ // InOmega d ηmin η} | Recurrent ω.val} :=
  measurable_subtype_coe measurableSet_recurrent

/-- Source-facing recurrence consumer: for every probability measure `Q` on the Section-5 state
space `Ω`, the pushed law `Q.map Subtype.val` satisfies `RecurrentLaw` exactly when `Q` gives the
recurrent event `{ω | Recurrent ω.val}` probability one. -/
theorem recurrentLaw_map_val_iff (ηmin : ℤ)
    (Q : Measure {η : Site d → ℤ // InOmega d ηmin η}) [IsProbabilityMeasure Q] :
    RecurrentLaw d (Q.map Subtype.val) ↔ Q {ω | Recurrent ω.val} = 1 := by
  haveI : IsProbabilityMeasure (Q.map Subtype.val) :=
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  have hmap : (Q.map Subtype.val) {η | Recurrent η} = Q {ω | Recurrent ω.val} :=
    Measure.map_apply measurable_subtype_coe measurableSet_recurrent
  rw [recurrentLaw_iff_measure_recurrent, hmap]

end Exploding
