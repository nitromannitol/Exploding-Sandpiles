import Exploding.Support.GeneralizedLastWaveUnconditional

/-!
# Generalized convergence of arrival times

Under the standing hypotheses on the background law, rescaled arrival times
converge locally uniformly to a deterministic time constant.
-/

open Exploding LatticeProb MeasureTheory Filter

/-- The generalized exploding sandpile has a deterministic time constant. -/
theorem Exploding.generalized_convergence_unconditional (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : MeasurableErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P) (h5 : WaveApproximationHyp d P) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂P,
        Explosive η ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) - N y| ≤ ε
:= by
  obtain ⟨N, hcont, hconv, hhom, hlast⟩ :=
    Exploding.convergence_of_the_generalized_last_wave_unconditional d hd ηmin L hL P hP hsupp
      hstat herg h1 h3 h4
  refine ⟨N, hcont, hconv, hhom, ?_⟩
  filter_upwards [hlast, h5] with η hlastη h5η
  obtain ⟨hexp, hfin, hloc⟩ := hlastη
  obtain ⟨hfinL, hfinA, hwave⟩ := h5η hexp
  refine ⟨hexp, hfinA, ?_⟩
  intro K hK ε hε
  obtain ⟨C, hC⟩ := Gen.exists_nat_bound_of_isCompact hK
  have hε2 : 0 < ε / 2 := by linarith
  have hloc' := hloc K hK (ε / 2) hε2
  have hwave' := hwave (ε / (2 * ((C : ℝ) + 2))) (by positivity)
  rw [Filter.eventually_atTop] at hloc' hwave'
  obtain ⟨n1, hn1⟩ := hloc'
  obtain ⟨n2, hn2⟩ := hwave'
  rw [Filter.eventually_atTop]
  refine ⟨max n1 (max n2 1), ?_⟩
  intro n hn y hy
  have hn1' : n1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2' : n2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn1'' : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnpos : 0 < n := hn1''
  have hx : nearestSite ((n : ℝ) • y) ∈ cent d (n * (C + 2)) := by
    intro i
    have h1' := Gen.nearestSite_smul_mem_cent y C n (hC y hy) i
    have h2' : ((n * (C + 1) + 1 : ℕ) : ℤ) ≤ ((n * (C + 2) : ℕ) : ℤ) := by
      push_cast
      nlinarith [hn1'']
    exact le_trans h1' h2'
  have hA := hn1 n hn1' y hy
  have hB := hn2 (n * (C + 2)) (le_trans hn2' (Nat.le_mul_of_pos_right n (by omega))) _ hx
  have hB' : |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ)
      - ((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ)| ≤ ε / 2 * (n : ℝ) := by
    have hmul : (ε / (2 * ((C : ℝ) + 2))) * ((n * (C + 2) : ℕ) : ℝ) = ε / 2 * (n : ℝ) := by
      have hcast : ((n * (C + 2) : ℕ) : ℝ) = (n : ℝ) * ((C : ℝ) + 2) := by push_cast; ring
      rw [hcast]
      field_simp
    linarith [hB]
  have hC' : |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
      - ((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)| ≤ ε / 2 :=
    Gen.div_sub_div_abs_le _ _ (ε / 2) n hnpos hB'
  have hD : |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
      - ((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)|
      ≤ ε / 2 := by rw [abs_sub_comm]; exact hC'
  have := Gen.abs_sub_le_of_le _ _ _ _ _ hD hA
  linarith
