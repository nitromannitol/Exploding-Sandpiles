/-
Theorem 5.2 of the paper: convergence of the exploding sandpile under the
general hypotheses.
-/
import Exploding.Support.Hypotheses

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
:= by sorry
