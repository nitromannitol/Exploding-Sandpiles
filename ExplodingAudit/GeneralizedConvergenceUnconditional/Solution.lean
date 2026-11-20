import Exploding.Support.GeneralizedConvergenceUnconditional
import ExplodingAudit.GeneralizedConvergenceUnconditional.SolutionBasic

/-!
# GeneralizedConvergenceUnconditional: comparator solution

The independently stated theorem follows from the chemical-distance-free result.
-/

open MeasureTheory Filter

namespace Exploding
namespace StatementAudit
namespace GeneralizedConvergenceUnconditional

/-- The theorem without a chemical-distance assumption. -/
theorem generalized_convergence_unconditional (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
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
  set_option smartUnfolding false in
  exact Exploding.generalized_convergence_unconditional d hd ηmin L hL P hP hsupp hstat herg h1 h3 h4 h5

end GeneralizedConvergenceUnconditional
end StatementAudit
end Exploding
