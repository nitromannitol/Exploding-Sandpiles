/-
Theorem 5.2 of the paper: convergence of the exploding sandpile under the
general hypotheses.
-/
import Exploding.Support.Hypotheses
import Exploding.Support.Gen
import Exploding.Frozen.GeneralizedLastWave

open Exploding LatticeProb MeasureTheory Filter

/-- **Theorem 5.2** (`exploding.tex:1228-1232`, "Convergence of the exploding
sandpile", the unlabelled theorem of Section 5).

"Under the assumptions in Proposition 5.1 and Hypothesis 5.5, on an event of
probability 1, `η` is explosive and the rescaled arrival times
`n^{-1} T_η([nx]) := n^{-1} min{t > 0 : v_t([nx]) > 0}` converge locally
uniformly to `N_η`, a deterministic, continuous, convex, one-homogeneous
function on `ℝ^d` depending only on the law of `η`."

The assumptions of Proposition 5.1 are the Section 5 setting together with
Hypotheses 5.1, 5.3 and 5.4; Hypothesis 5.5 is the wave-approximation
hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.generalized_convergence (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : ErgodicOn d L P)
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
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨N, hcont, hconv, hhom, hlast⟩ :=
    Exploding.Frozen.convergence_of_the_generalized_last_wave d hd ηmin L hL P hP hsupp
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

