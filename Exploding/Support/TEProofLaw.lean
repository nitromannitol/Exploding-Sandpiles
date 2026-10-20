/-
Stationarity, finite range of dependence and ergodicity of an i.i.d. product law on
`ℤ^d`, in the form of Hypotheses of Section 5 of `paper/corrected-arxiv/exploding-corrected-arxiv.tex`, and the
zero-one law for translation-invariant events.
-/
import Exploding.Support.Hypotheses
import LatticeProb.Prob.Translation

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The translation `η ↦ η(y + ·)` as a reindexing of the coordinates. -/
theorem te_shift_eq_piCongrLeft (y : Site d) :
    (fun η : Site d → ℤ => fun z => η (y + z))
      = ⇑(MeasurableEquiv.piCongrLeft (fun _ : Site d => ℤ) (Equiv.addLeft y).symm) := by
  funext η z
  have h1 := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Site d => ℤ)
    (Equiv.addLeft y).symm η ((Equiv.addLeft y) z)
  rw [Equiv.symm_apply_apply] at h1
  rw [h1, Equiv.coe_addLeft]

/-- An i.i.d. product law is stationary under every lattice translation. -/
theorem te_stationary (d : ℕ) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν) :
    StationaryOn d (⊤ : AddSubgroup (Site d)) (Measure.infinitePi fun _ : Site d => ν) := by
  unfold StationaryOn
  intro y _
  rw [te_shift_eq_piCongrLeft y]
  exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : Site d => ν)
    (X := fun _ : Site d => ℤ) (Equiv.addLeft y).symm

/-- An i.i.d. product law has finite range of dependence (range `0`). -/
theorem te_finite_range (d : ℕ) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν) :
    FiniteRangeOfDependence d (Measure.infinitePi fun _ : Site d => ν) := by
  refine ⟨0, fun I J hIJ => ?_⟩
  haveI : ∀ i : Site d, IsProbabilityMeasure (ν : Measure ℤ) := fun _ => hν
  have h : ProbabilityTheory.iIndepFun (fun (i : Site d) (ω : Site d → ℤ) => ω i)
      (Measure.infinitePi fun _ : Site d => ν) :=
    ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : Site d => ν)
      (X := fun (_ : Site d) (m : ℤ) => m) (by fun_prop)
  have hdisj : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have := hIJ a ha a hb
    simp [mnorm] at this
  exact ProbabilityTheory.iIndepFun.indepFun_finset I J hdisj h (fun i => measurable_pi_apply i)

/-- The translation by `y`. -/
def teShift (y : Site d) (η : Site d → ℤ) : Site d → ℤ := fun z => η (y + z)

theorem teShift_add (y w : Site d) (η : Site d → ℤ) :
    teShift y (teShift w η) = teShift (w + y) η := by
  funext z
  simp only [teShift]
  rw [add_assoc]

theorem teShift_zero (η : Site d → ℤ) : teShift (0 : Site d) η = η := by
  funext z; simp [teShift]

theorem teShift_eq_coordShift (y : Site d) :
    teShift y = coordShift (X := ℤ) (fun x : Site d => x + y) := by
  funext η z
  simp [teShift, coordShift, add_comm]

theorem measurable_teShift (y : Site d) : Measurable (teShift y : (Site d → ℤ) → Site d → ℤ) := by
  rw [teShift_eq_coordShift]; exact measurable_coordShift _

/-- The zero-one law for events invariant under one nonzero translation. -/
theorem te_zero_one (d : ℕ) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    {A : Set (Site d → ℤ)} (hA : MeasurableSet A) (v : Site d) (hv : v ≠ 0)
    (hinv : teShift v ⁻¹' A = A) :
    (Measure.infinitePi fun _ : Site d => ν) A = 0 ∨
      (Measure.infinitePi fun _ : Site d => ν) A = 1 := by
  have h := measure_zero_or_one_of_translationInvariant ν hv hA
    (by rw [← teShift_eq_coordShift]; exact hinv)
  exact h

/-- An i.i.d. product law is ergodic under the full lattice of translations. -/
theorem te_ergodic (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν) :
    ErgodicOn d (⊤ : AddSubgroup (Site d)) (Measure.infinitePi fun _ : Site d => ν) := by
  intro E hE
  set P := Measure.infinitePi fun _ : Site d => ν with hP
  -- `E` is invariant under every translation.
  have hsub : ∀ w : Site d, E ⊆ (fun η : Site d → ℤ => fun z => η (w + z)) '' E := by
    intro w η hη
    rw [hE] at hη
    simp only [Set.mem_iInter] at hη
    exact hη w (AddSubgroup.mem_top w)
  have hinvE : ∀ y : Site d, E ⊆ teShift y ⁻¹' E := by
    intro y η hη
    obtain ⟨e, he, hee⟩ := hsub (-y) hη
    have : teShift y η = e := by
      rw [← hee]
      funext z
      simp [teShift]
    show teShift y η ∈ E
    rw [this]; exact he
  -- a measurable invariant hull
  set H := toMeasurable P E with hH
  have hHm : MeasurableSet H := measurableSet_toMeasurable P E
  have hEH : E ⊆ H := subset_toMeasurable P E
  have hHE : P H = P E := measure_toMeasurable E
  set H' : Set (Site d → ℤ) := ⋂ y : Site d, teShift y ⁻¹' H with hH'
  have hH'm : MeasurableSet H' :=
    MeasurableSet.iInter fun y => measurable_teShift y hHm
  have hEH' : E ⊆ H' := by
    intro η hη
    simp only [hH', Set.mem_iInter, Set.mem_preimage]
    intro y
    exact hEH (hinvE y hη)
  have hH'H : H' ⊆ H := by
    intro η hη
    simp only [hH', Set.mem_iInter, Set.mem_preimage] at hη
    have := hη 0
    rwa [teShift_zero] at this
  have hPH' : P H' = P E :=
    le_antisymm (hHE ▸ measure_mono hH'H) (measure_mono hEH')
  have hinv : teShift (unit (⟨0, by omega⟩ : Fin d)) ⁻¹' H' = H' := by
    ext η
    simp only [hH', Set.mem_iInter, Set.mem_preimage, teShift_add]
    constructor
    · intro h y
      have := h (y - unit (⟨0, by omega⟩ : Fin d))
      simpa [add_comm] using this
    · intro h y
      exact h _
  have := te_zero_one d ν hν hH'm _ (unit_ne_zero _) hinv
  rw [hPH'] at this
  exact this

end Exploding
