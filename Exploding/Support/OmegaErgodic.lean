/-
The state space `Ω = {η | InOmega d ηmin η}` of Section 5 of the corrected source
`paper/corrected-arxiv/exploding-corrected-arxiv.tex` (`\section{A generalization}`, lines
1231-1248), its invariance under translations, and ergodicity for the events of `Ω`.

The source's σ-field on `Ω` is the coordinate σ-field. Its identification with the trace of the
product σ-field on `Site d → ℤ` is not formalized in this file. `OmegaErgodicOn` quantifies over
the measurable sets `E ⊆ Ω` of the ambient product σ-field. Under
`hsupp : ∀ᵐ η ∂P, InOmega d ηmin η` it is equivalent to `MeasurableErgodicOn`.
-/
import Exploding.Support.Hypotheses

namespace Exploding

open LatticeProb MeasureTheory

/-- Ergodicity on the state space `Ω`: every measurable event `E ⊆ Ω` that is invariant
under the translations `τ_y η = (z ↦ η (y + z))`, for `y ∈ L`, has probability `0` or `1`. -/
def OmegaErgodicOn (d : ℕ) (ηmin : ℤ) (L : AddSubgroup (Site d))
    (P : Measure (Site d → ℤ)) : Prop :=
  ∀ E : Set (Site d → ℤ), MeasurableSet E → E ⊆ {η | InOmega d ηmin η} →
    E = ⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (y + z)) '' E →
      P E = 0 ∨ P E = 1

/-- `Ω` is measurable: it is a countable intersection of coordinate cylinders. -/
theorem measurableSet_inOmega (d : ℕ) (ηmin : ℤ) :
    MeasurableSet {η : Site d → ℤ | InOmega d ηmin η} := by
  have hZ : ∀ s : Set ℤ, MeasurableSet s := fun s => MeasurableSpace.measurableSet_top
  have hset : {η : Site d → ℤ | InOmega d ηmin η} =
      ⋂ x : Site d, (fun η : Site d → ℤ => η x) ⁻¹'
        {n : ℤ | ηmin ≤ n ∧ n ≤ 2 * (d : ℤ) - 1} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, InOmega, iff_self]
  rw [hset]
  exact MeasurableSet.iInter fun x => measurable_pi_apply x (hZ _)

/-- Each translation `τ_y` maps `Ω` onto itself. -/
theorem translate_image_inOmega (d : ℕ) (ηmin : ℤ) (y : Site d) :
    (fun η : Site d → ℤ => fun z => η (y + z)) '' {η | InOmega d ηmin η}
      = {η | InOmega d ηmin η} := by
  ext ξ
  constructor
  · rintro ⟨η, hη, rfl⟩
    have hη' : ∀ u : Site d, ηmin ≤ η u ∧ η u ≤ 2 * (d : ℤ) - 1 := hη
    intro u
    exact hη' (y + u)
  · intro hξ
    have hξ' : ∀ u : Site d, ηmin ≤ ξ u ∧ ξ u ≤ 2 * (d : ℤ) - 1 := hξ
    refine ⟨fun z => ξ (-y + z), ?_, ?_⟩
    · intro u
      exact hξ' (-y + u)
    · funext z
      have hz : -y + (y + z) = z := by abel
      exact congrArg ξ hz

/-- Under `hsupp`, a set has the same measure as its intersection with `Ω`. -/
theorem measure_eq_inter_inOmega {d : ℕ} {ηmin : ℤ} {P : Measure (Site d → ℤ)}
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η) {A : Set (Site d → ℤ)} :
    P A = P (A ∩ {η | InOmega d ηmin η}) := by
  have hnull : P {η : Site d → ℤ | ¬InOmega d ηmin η} = 0 :=
    MeasureTheory.ae_iff.mp hsupp
  have hsub : A \ {η | InOmega d ηmin η} ⊆ {η : Site d → ℤ | ¬InOmega d ηmin η} :=
    fun η hη => hη.2
  have hdiff : P (A \ {η | InOmega d ηmin η}) = 0 :=
    MeasureTheory.measure_mono_null hsub hnull
  have hsplit : P (A ∩ {η | InOmega d ηmin η}) + P (A \ {η | InOmega d ηmin η}) = P A :=
    MeasureTheory.measure_inter_add_sdiff A (measurableSet_inOmega d ηmin)
  rw [hdiff, add_zero] at hsplit
  exact hsplit.symm

/-- An `L`-invariant set stays `L`-invariant after intersection with `Ω`. -/
theorem invariant_inter_inOmega {d : ℕ} {ηmin : ℤ} {L : AddSubgroup (Site d)}
    {A : Set (Site d → ℤ)}
    (hA : A = ⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (y + z)) '' A) :
    A ∩ {η | InOmega d ηmin η} = ⋂ y ∈ (L : Set (Site d)),
      (fun η : Site d → ℤ => fun z => η (y + z)) '' (A ∩ {η | InOmega d ηmin η}) := by
  ext x
  constructor
  · rintro ⟨hxA, hxΩ⟩
    rw [Set.mem_iInter₂]
    intro y hy
    have hxΩ' : ∀ u : Site d, ηmin ≤ x u ∧ x u ≤ 2 * (d : ℤ) - 1 := hxΩ
    have hxS : x ∈ (fun η : Site d → ℤ => fun z => η (y + z)) '' A := by
      rw [hA] at hxA
      exact Set.mem_iInter₂.mp hxA y hy
    obtain ⟨a, haA, hax⟩ := hxS
    refine ⟨a, ⟨haA, ?_⟩, hax⟩
    show ∀ w : Site d, ηmin ≤ a w ∧ a w ≤ 2 * (d : ℤ) - 1
    intro w
    have h1 : y + (w - y) = w := by abel
    have hkey : a w = x (w - y) := by
      have h2 : a (y + (w - y)) = x (w - y) := by rw [← hax]
      rwa [h1] at h2
    rw [hkey]
    exact hxΩ' (w - y)
  · intro hx
    obtain ⟨a, ⟨haA, haΩ⟩, hax⟩ := Set.mem_iInter₂.mp hx 0 L.zero_mem
    have hxa : x = a := by
      rw [← hax]
      funext z
      simp
    rw [hxa]
    exact ⟨haA, haΩ⟩

/-- Measurable ergodicity of `P` gives ergodicity of `P` on the events of `Ω`. -/
theorem omegaErgodicOn_of_measurableErgodicOn (d : ℕ) (ηmin : ℤ) {L : AddSubgroup (Site d)}
    {P : Measure (Site d → ℤ)} (h : MeasurableErgodicOn d L P) :
    OmegaErgodicOn d ηmin L P := by
  intro E hE _ hEq
  exact h E hE hEq

/-- Under `hsupp`, ergodicity on the events of `Ω` gives measurable ergodicity of `P`. -/
theorem measurableErgodicOn_of_omegaErgodicOn {d : ℕ} {ηmin : ℤ} {L : AddSubgroup (Site d)}
    {P : Measure (Site d → ℤ)} (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (h : OmegaErgodicOn d ηmin L P) : MeasurableErgodicOn d L P := by
  intro A hA hAinv
  have hEΩ : MeasurableSet (A ∩ {η | InOmega d ηmin η}) :=
    hA.inter (measurableSet_inOmega d ηmin)
  have hE := h (A ∩ {η | InOmega d ηmin η}) hEΩ Set.inter_subset_right
    (invariant_inter_inOmega hAinv)
  rw [← measure_eq_inter_inOmega hsupp] at hE
  exact hE

/-- Under `hsupp`, measurable ergodicity is equivalent to ergodicity on the events of `Ω`. -/
theorem measurableErgodicOn_iff_omegaErgodicOn {d : ℕ} {ηmin : ℤ} {L : AddSubgroup (Site d)}
    {P : Measure (Site d → ℤ)} (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η) :
    MeasurableErgodicOn d L P ↔ OmegaErgodicOn d ηmin L P :=
  ⟨omegaErgodicOn_of_measurableErgodicOn d ηmin,
    measurableErgodicOn_of_omegaErgodicOn hsupp⟩

end Exploding
