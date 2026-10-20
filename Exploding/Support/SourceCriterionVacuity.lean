import Exploding.Support.OmegaCriterionConsumer
import Exploding.Support.ExplosiveVacuity

/-!
# Source-criterion nonvacuity at `d = 2`

The source criterion `explosive_of_source_ergodic` is applied to one concrete law. Take `d = 2`,
`η_min = -1` and the sublattice `L = ⊤`. Let `P` be the product of Dirac masses at `3`, which is
`2d - 1` for `d = 2`, and let `Q` be its source law on `Ω`, the comap of `P` along the subtype
inclusion. The law `Q` satisfies every premise of the consumer, and the consumer then gives
probability one to the explosive event. No hypothesis is assumed; every premise is produced by the
existing witness `explosion_criteria_premises_nonvacuous` and the source transport lemmas.
-/

namespace Exploding

open LatticeProb MeasureTheory

/-- **Nonvacuity of the source criterion at `d = 2`, `η_min = -1`, `L = ⊤`.** With `P` the product
of Dirac masses at `3` and `Q = OmegaStationary.sourceLaw (-1) P`, the index of `⊤` is nonzero, `Q`
is a probability law on `Ω`, its coordinate image stationarity holds, it is source ergodic on `Ω`,
its ambient pushforward has finite range of dependence and box crossing, the recurrent event has
`Q`-probability one, and the explosive event has `Q`-probability one. -/
theorem source_criterion_vacuity_d2 :
    let P : Measure (Site 2 → ℤ) := Measure.infinitePi fun _ : Site 2 => Measure.dirac (3 : ℤ)
    let Q : Measure {η : Site 2 → ℤ // InOmega 2 (-1) η} := OmegaStationary.sourceLaw (-1) P
    (⊤ : AddSubgroup (Site 2)).index ≠ 0 ∧
    IsProbabilityMeasure Q ∧
    (∀ E : Set {η : Site 2 → ℤ // InOmega 2 (-1) η},
      MeasurableSet[omegaCoordMeasurableSpace 2 (-1)] E →
        ∀ y ∈ (⊤ : AddSubgroup (Site 2)), Q (omegaSubShift 2 (-1) y '' E) = Q E) ∧
    SourceErgodicOmega 2 (-1) ⊤ Q ∧
    FiniteRangeOfDependence 2 (Q.map Subtype.val) ∧
    BoxCrossingHyp 2 (Q.map Subtype.val) ∧
    Q {ω | Recurrent ω.val} = 1 ∧
    Q {ω | Explosive ω.val} = 1 := by
  intro P Q
  have hPeq : P = Measure.infinitePi fun _ : Site 2 => Measure.dirac (2 * ((2 : ℕ) : ℤ) - 1) :=
    rfl
  obtain ⟨hidx, hprob, hsupp, hstatP, hergP, h1P, h2P, hrecP⟩ :=
    explosion_criteria_premises_nonvacuous 2 (le_refl 2) (-1) (by norm_num)
  have hPprob : IsProbabilityMeasure P := by rw [hPeq]; exact hprob
  have hsuppP : ∀ᵐ η ∂P, InOmega 2 (-1) η := by rw [hPeq]; exact hsupp
  have hstatP' : StationaryOn 2 (⊤ : AddSubgroup (Site 2)) P := by rw [hPeq]; exact hstatP
  have hergP' : MeasurableErgodicOn 2 (⊤ : AddSubgroup (Site 2)) P := by rw [hPeq]; exact hergP
  have h1P' : FiniteRangeOfDependence 2 P := by rw [hPeq]; exact h1P
  have h2P' : BoxCrossingHyp 2 P := by rw [hPeq]; exact h2P
  have hrecP' : RecurrentLaw 2 P := by rw [hPeq]; exact hrecP
  haveI : IsProbabilityMeasure P := hPprob
  have hprobQ : IsProbabilityMeasure Q :=
    OmegaStationary.isProbabilityMeasure_sourceLaw (-1) P hsuppP
  haveI : IsProbabilityMeasure Q := hprobQ
  have hmapQ : Q.map Subtype.val = P := OmegaStationary.map_val_sourceLaw (-1) P hsuppP
  have hstatQ : ∀ E : Set {η : Site 2 → ℤ // InOmega 2 (-1) η},
      MeasurableSet[omegaCoordMeasurableSpace 2 (-1)] E →
        ∀ y ∈ (⊤ : AddSubgroup (Site 2)), Q (omegaSubShift 2 (-1) y '' E) = Q E :=
    fun E hE y hy =>
      (OmegaStationary.imageStationaryOn_sourceLaw_iff (-1) ⊤ P hsuppP).mpr hstatP' E
        ((measurableSet_omegaCoord_iff 2 (-1) E).mp hE) y hy
  have hergQ : SourceErgodicOmega 2 (-1) ⊤ Q :=
    (sourceErgodicOmega_sourceLaw_iff 2 (-1) ⊤ P hsuppP).mpr hergP'
  have h1Q : FiniteRangeOfDependence 2 (Q.map Subtype.val) := by rw [hmapQ]; exact h1P'
  have h2Q : BoxCrossingHyp 2 (Q.map Subtype.val) := by rw [hmapQ]; exact h2P'
  have hrecQ : Q {ω | Recurrent ω.val} = 1 :=
    (recurrentLaw_map_val_iff (-1) Q).mp (by rw [hmapQ]; exact hrecP')
  have hexpQ : Q {ω | Explosive ω.val} = 1 :=
    explosive_of_source_ergodic 2 (le_refl 2) (-1) ⊤ hidx Q hstatQ hergQ h1Q h2Q hrecQ
  exact ⟨hidx, hprobQ, hstatQ, hergQ, h1Q, h2Q, hrecQ, hexpQ⟩

end Exploding
