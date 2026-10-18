/-
The source carrier `Ω = {η : Site d → ℤ // InOmega d ηmin η}` of Section 5 of the corrected
source (`paper/corrected-arxiv/exploding-corrected-arxiv.tex`, `\section{A generalization}`,
lines 1231–1248), with its inherited measurable space.

It defines the translation action `T_y` on `Ω` by the coordinates `z ↦ ω(y + z)`, the literal
image-stationarity formula of the source, and its transfer to the ambient pushforward
`Q.map Subtype.val` of a law `Q` on `Ω`.
-/
import Exploding.Support.Hypotheses

namespace Exploding
namespace OmegaStationary

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The source carrier `Ω`: backgrounds with `ηmin ≤ η ≤ 2d - 1`, with the inherited
measurable space of the subtype. -/
abbrev OmegaCarrier (d : ℕ) (ηmin : ℤ) : Type := {η : Site d → ℤ // InOmega d ηmin η}

/-- The translate `T_y ω` of a background `ω ∈ Ω`, with coordinates `z ↦ ω(y + z)`. -/
def carrierShift (ηmin : ℤ) (y : Site d) (ω : OmegaCarrier d ηmin) : OmegaCarrier d ηmin :=
  ⟨fun z => ω.val (y + z), fun x => ω.property (y + x)⟩

/-! ### Translations are measurable bijections -/

theorem carrierShift_neg_shift (ηmin : ℤ) (y : Site d) (ω : OmegaCarrier d ηmin) :
    carrierShift ηmin (-y) (carrierShift ηmin y ω) = ω := by
  refine Subtype.ext (funext fun z => ?_)
  show ω.val (y + (-y + z)) = ω.val z
  simp

theorem carrierShift_shift_neg (ηmin : ℤ) (y : Site d) (ω : OmegaCarrier d ηmin) :
    carrierShift ηmin y (carrierShift ηmin (-y) ω) = ω := by
  refine Subtype.ext (funext fun z => ?_)
  show ω.val (-y + (y + z)) = ω.val z
  simp

theorem measurable_carrierShift (ηmin : ℤ) (y : Site d) :
    Measurable (carrierShift ηmin y) := by
  unfold carrierShift
  refine Measurable.subtype_mk ?_
  refine measurable_pi_lambda _ fun z => ?_
  exact (measurable_pi_apply (y + z)).comp measurable_subtype_coe

theorem measurable_ambientShift (y : Site d) :
    Measurable (fun η : Site d → ℤ => fun z => η (y + z)) :=
  measurable_pi_lambda _ fun z => measurable_pi_apply (y + z)

/-- Intertwining: the coordinates of `T_y ω` are the ambient translate of the coordinates of `ω`. -/
theorem val_carrierShift (ηmin : ℤ) (y : Site d) (ω : OmegaCarrier d ηmin) :
    (carrierShift ηmin y ω).val = (fun η : Site d → ℤ => fun z => η (y + z)) ω.val :=
  rfl

theorem image_carrierShift_eq_preimage (ηmin : ℤ) (y : Site d) (E : Set (OmegaCarrier d ηmin)) :
    carrierShift ηmin y '' E = carrierShift ηmin (-y) ⁻¹' E := by
  ext ω
  constructor
  · rintro ⟨ν, hν, rfl⟩
    show carrierShift ηmin (-y) (carrierShift ηmin y ν) ∈ E
    rwa [carrierShift_neg_shift]
  · intro hω
    exact ⟨carrierShift ηmin (-y) ω, hω, carrierShift_shift_neg ηmin y ω⟩

theorem preimage_carrierShift_eq_image (ηmin : ℤ) (y : Site d) (E : Set (OmegaCarrier d ηmin)) :
    carrierShift ηmin y ⁻¹' E = carrierShift ηmin (-y) '' E := by
  ext ω
  constructor
  · intro hω
    exact ⟨carrierShift ηmin y ω, hω, carrierShift_neg_shift ηmin y ω⟩
  · rintro ⟨ν, hν, rfl⟩
    show carrierShift ηmin y (carrierShift ηmin (-y) ν) ∈ E
    rwa [carrierShift_shift_neg]

/-! ### The literal source stationarity on `Ω` -/

/-- The literal source stationarity on `Ω`: for every measurable event `E` of `Ω` and every
`y ∈ L`, `Q (T_y '' E) = Q E`. -/
def ImageStationaryOn (ηmin : ℤ) (L : AddSubgroup (Site d)) (Q : Measure (OmegaCarrier d ηmin)) :
    Prop :=
  ∀ E : Set (OmegaCarrier d ηmin), MeasurableSet E → ∀ y ∈ L, Q (carrierShift ηmin y '' E) = Q E

/-- Image stationarity on `Ω` of a law `Q` is exactly `StationaryOn` for its ambient pushforward
`Q.map Subtype.val`. This holds for every measure `Q` on `Ω`. -/
theorem imageStationaryOn_iff_stationaryOn_map (ηmin : ℤ) (L : AddSubgroup (Site d))
    (Q : Measure (OmegaCarrier d ηmin)) :
    ImageStationaryOn ηmin L Q ↔ StationaryOn d L (Q.map Subtype.val) := by
  constructor
  · intro h y hy
    refine Measure.ext fun A hA => ?_
    have hE : MeasurableSet (Subtype.val ⁻¹' A : Set (OmegaCarrier d ηmin)) :=
      measurable_subtype_coe hA
    have hpre : Subtype.val ⁻¹' ((fun η : Site d → ℤ => fun z => η (y + z)) ⁻¹' A)
        = carrierShift ηmin y ⁻¹' (Subtype.val ⁻¹' A) := rfl
    rw [Measure.map_apply (measurable_ambientShift y) hA,
      Measure.map_apply measurable_subtype_coe (measurable_ambientShift y hA),
      Measure.map_apply measurable_subtype_coe hA, hpre, preimage_carrierShift_eq_image]
    exact h _ hE (-y) (L.neg_mem hy)
  · intro h E hE y hy
    obtain ⟨A, hA, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hE
    have hmap : ((Q.map Subtype.val).map (fun η : Site d → ℤ => fun z => η (-y + z))) A
        = (Q.map Subtype.val) A := by
      rw [h (-y) (L.neg_mem hy)]
    rw [Measure.map_apply (measurable_ambientShift (-y)) hA,
      Measure.map_apply measurable_subtype_coe (measurable_ambientShift (-y) hA),
      Measure.map_apply measurable_subtype_coe hA] at hmap
    rw [image_carrierShift_eq_preimage]
    exact hmap

/-! ### Pushforward of a law on `Ω`: probability and full `InOmega` support -/

theorem measurableSet_inOmega (ηmin : ℤ) :
    MeasurableSet {η : Site d → ℤ | InOmega d ηmin η} := by
  have h : {η : Site d → ℤ | InOmega d ηmin η} =
      ⋂ x : Site d, {η : Site d → ℤ | ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_iInter, InOmega]
  rw [h]
  refine MeasurableSet.iInter fun x => ?_
  exact (measurableSet_le measurable_const (measurable_pi_apply x)).inter
    (measurableSet_le (measurable_pi_apply x) measurable_const)

theorem isProbabilityMeasure_map_val (ηmin : ℤ) (Q : Measure (OmegaCarrier d ηmin))
    [IsProbabilityMeasure Q] : IsProbabilityMeasure (Q.map Subtype.val) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem ae_inOmega_map_val (ηmin : ℤ) (Q : Measure (OmegaCarrier d ηmin)) :
    ∀ᵐ η ∂(Q.map Subtype.val), InOmega d ηmin η :=
  (ae_map_iff measurable_subtype_coe.aemeasurable (measurableSet_inOmega ηmin)).mpr
    (ae_of_all Q fun ω => ω.property)

/-- The source consumer on one common law `Q`: the ambient pushforward is a probability law
with full `InOmega` support, and image stationarity of `Q` is `StationaryOn` of that pushforward. -/
theorem source_consumer_facts (ηmin : ℤ) (L : AddSubgroup (Site d))
    (Q : Measure (OmegaCarrier d ηmin)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (Q.map Subtype.val) ∧
      (∀ᵐ η ∂(Q.map Subtype.val), InOmega d ηmin η) ∧
      (ImageStationaryOn ηmin L Q ↔ StationaryOn d L (Q.map Subtype.val)) :=
  ⟨isProbabilityMeasure_map_val ηmin Q, ae_inOmega_map_val ηmin Q,
    imageStationaryOn_iff_stationaryOn_map ηmin L Q⟩

/-! ### The source law of an ambient law carried by `Ω` -/

/-- The source law on `Ω` read from an ambient law `P`: its comap along `Subtype.val`. -/
noncomputable def sourceLaw (ηmin : ℤ) (P : Measure (Site d → ℤ)) : Measure (OmegaCarrier d ηmin) :=
  P.comap Subtype.val

theorem map_val_sourceLaw (ηmin : ℤ) (P : Measure (Site d → ℤ))
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η) : (sourceLaw ηmin P).map Subtype.val = P := by
  have h : (P.comap (Subtype.val : OmegaCarrier d ηmin → Site d → ℤ)).map Subtype.val
      = P.restrict {η : Site d → ℤ | InOmega d ηmin η} :=
    map_comap_subtype_coe (measurableSet_inOmega ηmin) P
  rw [sourceLaw, h]
  exact Measure.restrict_eq_self_of_ae_mem (s := {η : Site d → ℤ | InOmega d ηmin η}) hsupp

theorem isProbabilityMeasure_sourceLaw (ηmin : ℤ) (P : Measure (Site d → ℤ))
    [IsProbabilityMeasure P] (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η) :
    IsProbabilityMeasure (sourceLaw ηmin P) := by
  have h : (sourceLaw ηmin P).map Subtype.val Set.univ = sourceLaw ηmin P Set.univ := by
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]
  constructor
  rw [← h, map_val_sourceLaw ηmin P hsupp, measure_univ]

/-- The event mass identity: a measurable ambient event `A` has source mass `P A`. -/
theorem sourceLaw_preimage_val (ηmin : ℤ) (P : Measure (Site d → ℤ))
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η) {A : Set (Site d → ℤ)} (hA : MeasurableSet A) :
    sourceLaw ηmin P (Subtype.val ⁻¹' A) = P A := by
  calc sourceLaw ηmin P (Subtype.val ⁻¹' A)
      = ((sourceLaw ηmin P).map Subtype.val) A := (Measure.map_apply measurable_subtype_coe hA).symm
    _ = P A := by rw [map_val_sourceLaw ηmin P hsupp]

/-- Source image stationarity of the comap law of an ambient `P` carried by `Ω` is exactly
`StationaryOn` of `P` itself. -/
theorem imageStationaryOn_sourceLaw_iff (ηmin : ℤ) (L : AddSubgroup (Site d))
    (P : Measure (Site d → ℤ)) (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η) :
    ImageStationaryOn ηmin L (sourceLaw ηmin P) ↔ StationaryOn d L P := by
  rw [imageStationaryOn_iff_stationaryOn_map, map_val_sourceLaw ηmin P hsupp]

end OmegaStationary
end Exploding
