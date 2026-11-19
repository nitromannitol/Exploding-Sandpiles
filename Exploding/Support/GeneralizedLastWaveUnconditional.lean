import Exploding.Support.GeneralizedInputsUnconditional

/-!
# Generalized last-wave convergence

The generalized last-wave arrival times converge locally uniformly under the
standing hypotheses on the background law.
-/

open Exploding LatticeProb MeasureTheory Filter

/-- The generalized last wave has a deterministic time constant. -/
theorem Exploding.convergence_of_the_generalized_last_wave_unconditional (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : MeasurableErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂P,
        Explosive η ∧ (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε := by
  have _ := herg
  have hup : ∀ᵐ η ∂P, ∀ x : Site d, η x ≤ 2 * (d : ℤ) - 1 :=
    hsupp.mono fun η h x => (h x).2
  have hnn : ∀ᵐ η ∂P, ∀ x : Site d, 0 ≤ η x :=
    Exploding.pathFillingHyp_nonneg hd P hup h3
  have hsupp0 : ∀ᵐ η ∂P, InOmega d 0 η :=
    (hnn.and hup).mono fun η h x => ⟨h.1 x, h.2 x⟩
  obtain ⟨γ, C, hγ, hC, hloc⟩ := glws_origin_unconditional d hd 0 le_rfl P hP hsupp0 h1 h3 h4
  obtain ⟨γ', _, hcl⟩ := s3k_close_unconditional d hd 0 le_rfl P hP hsupp0 h1 h3 h4
  have hmix : glws_Mix d L P := fun y hy hy0 s S hS =>
    glw2_shift_mixing d P h1 y (glw_shift_ergodic_meas_pres d L P hstat y hy) hy0 s S hS
  exact glws_core d hd 0 le_rfl L hL P hP hsupp0 hstat hmix hγ hC hloc hcl
