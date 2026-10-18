/-
The source ergodicity on the state space `Ω = {η | InOmega d ηmin η}` of Section 5 of the corrected
source `paper/corrected-arxiv/exploding-corrected-arxiv.tex` (`\section{A generalization}`, lines
1233-1248), and the source-facing consumer of the explosion criterion (Proposition 7.1, lines
2377-2400) on one common law `Q` of `Ω`.

`SourceErgodicOmega` is the literal ergodicity of `Q` on `(Ω, F)`, where `F` is the coordinate
σ-field. It is equivalent to measurable ergodicity of the ambient pushforward `Q.map Subtype.val`
for every measure `Q`, and under the support hypothesis it is ergodicity of the source law
`OmegaStationary.sourceLaw`.
-/
import Exploding.Support.OmegaErgodic
import Exploding.Support.OmegaTraceSigma
import Exploding.Support.OmegaStationary
import Exploding.Support.RecurrentMeasurable
import Exploding.Support.ExplosiveMeasurable
import Exploding.Frozen.ExplosionCriteria

namespace Exploding

open LatticeProb MeasureTheory

/-- Ergodicity of `Q` on the state space `Ω` of Section 5 with respect to the sublattice `L`: every
event `E` of the coordinate σ-field that is invariant, `E = ⋂_{y ∈ L} T_y E`, has `Q`-probability
`0` or `1`. -/
def SourceErgodicOmega (d : ℕ) (ηmin : ℤ) (L : AddSubgroup (Site d))
    (Q : Measure {η : Site d → ℤ // InOmega d ηmin η}) : Prop :=
  ∀ E : Set {η : Site d → ℤ // InOmega d ηmin η},
    MeasurableSet[omegaCoordMeasurableSpace d ηmin] E →
      E = ⋂ y ∈ (L : Set (Site d)), omegaSubShift d ηmin y '' E →
        Q E = 0 ∨ Q E = 1

/-- The trace on the ambient space of the preimage of an ambient set is its intersection with `Ω`. -/
theorem val_image_preimage_eq_inter (d : ℕ) (ηmin : ℤ) (A : Set (Site d → ℤ)) :
    Subtype.val '' (Subtype.val ⁻¹' A : Set {η : Site d → ℤ // InOmega d ηmin η})
      = A ∩ {η | InOmega d ηmin η} := by
  ext η
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨hξ, ξ.2⟩
  · rintro ⟨hηA, hηΩ⟩
    exact ⟨⟨η, hηΩ⟩, hηA, rfl⟩

/-- The source ergodicity of `Q` on `Ω` is exactly measurable ergodicity of its ambient pushforward.
No support or probability hypothesis is needed: every event of `Ω` is the preimage of its trace. -/
theorem sourceErgodicOmega_iff_measurableErgodicOn (d : ℕ) (ηmin : ℤ) (L : AddSubgroup (Site d))
    (Q : Measure {η : Site d → ℤ // InOmega d ηmin η}) :
    SourceErgodicOmega d ηmin L Q ↔ MeasurableErgodicOn d L (Q.map Subtype.val) := by
  constructor
  · intro h A hA hAinv
    have hE : MeasurableSet[omegaCoordMeasurableSpace d ηmin]
        (Subtype.val ⁻¹' A : Set {η : Site d → ℤ // InOmega d ηmin η}) :=
      (measurableSet_omegaCoord_iff d ηmin _).mpr (hA.preimage measurable_subtype_coe)
    have hinv : (Subtype.val ⁻¹' A : Set {η : Site d → ℤ // InOmega d ηmin η}) =
        ⋂ y ∈ (L : Set (Site d)), omegaSubShift d ηmin y '' (Subtype.val ⁻¹' A) := by
      refine (omegaSub_invariant_iff d ηmin L _).mpr ?_
      rw [val_image_preimage_eq_inter]
      exact invariant_inter_inOmega hAinv
    rw [Measure.map_apply measurable_subtype_coe hA]
    exact h (Subtype.val ⁻¹' A) hE hinv
  · intro h E hE hEinv
    obtain ⟨A, hA, -, hEA, hAinv⟩ := (omegaCoord_invariant_iff_exists d ηmin L E).mp ⟨hE, hEinv⟩
    have hmap := h A hA hAinv
    rw [Measure.map_apply measurable_subtype_coe hA, ← hEA] at hmap
    exact hmap

/-- On the supported ambient law `P`, the source ergodicity of the comap law
`OmegaStationary.sourceLaw` is exactly measurable ergodicity of `P`. -/
theorem sourceErgodicOmega_sourceLaw_iff (d : ℕ) (ηmin : ℤ) (L : AddSubgroup (Site d))
    (P : Measure (Site d → ℤ)) (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η) :
    SourceErgodicOmega d ηmin L (OmegaStationary.sourceLaw ηmin P)
      ↔ MeasurableErgodicOn d L P := by
  rw [sourceErgodicOmega_iff_measurableErgodicOn, OmegaStationary.map_val_sourceLaw ηmin P hsupp]

/-- **Source-facing explosion criterion on one common law.** Let `Q` be a probability law on `Ω`
that is stationary and ergodic on `(Ω, F)`, whose ambient pushforward has finite-range dependence and
box crossing, and which gives the recurrent event probability one. Then `Q` gives the explosive event
probability one (Proposition 7.1). -/
theorem explosive_of_source_ergodic (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (Q : Measure {η : Site d → ℤ // InOmega d ηmin η}) [IsProbabilityMeasure Q]
    (hstat : ∀ E : Set {η : Site d → ℤ // InOmega d ηmin η},
      MeasurableSet[omegaCoordMeasurableSpace d ηmin] E →
        ∀ y ∈ L, Q (omegaSubShift d ηmin y '' E) = Q E)
    (herg : SourceErgodicOmega d ηmin L Q)
    (h1 : FiniteRangeOfDependence d (Q.map Subtype.val))
    (h2 : BoxCrossingHyp d (Q.map Subtype.val))
    (hrec : Q {ω | Recurrent ω.val} = 1) :
    Q {ω | Explosive ω.val} = 1 := by
  have hst : OmegaStationary.ImageStationaryOn ηmin L Q := fun E hE y hy =>
    hstat E ((measurableSet_omegaCoord_iff d ηmin E).mpr hE) y hy
  have hstat' : StationaryOn d L (Q.map Subtype.val) :=
    (OmegaStationary.imageStationaryOn_iff_stationaryOn_map ηmin L Q).mp hst
  have hherg : MeasurableErgodicOn d L (Q.map Subtype.val) :=
    (sourceErgodicOmega_iff_measurableErgodicOn d ηmin L Q).mp herg
  have hrec' : RecurrentLaw d (Q.map Subtype.val) :=
    (recurrentLaw_map_val_iff ηmin Q).mpr hrec
  have hexp : ExplosiveLaw d (Q.map Subtype.val) :=
    Exploding.Frozen.explosion_criteria d hd ηmin L hL (Q.map Subtype.val)
      (OmegaStationary.isProbabilityMeasure_map_val ηmin Q)
      (OmegaStationary.ae_inOmega_map_val ηmin Q) hstat' hherg h1 h2 hrec'
  exact (explosiveLaw_map_subtype_iff ηmin Q).mp hexp

end Exploding
