import Exploding.Support.TimeConstantUnconditional
import ExplodingAudit.TimeConstantUnconditional.SolutionBasic

/-!
# TimeConstantUnconditional: comparator solution

The independently stated theorem follows from the chemical-distance-free result.
-/

open MeasureTheory Filter

namespace Exploding
namespace StatementAudit
namespace TimeConstantUnconditional

/-- The theorem without a chemical-distance assumption. -/
theorem convergence_of_time_constant_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        Explosive η ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) - N y| ≤ ε
:= by
  set_option smartUnfolding false in
  exact Exploding.convergence_of_time_constant_unconditional d hd p hp hp1

end TimeConstantUnconditional
end StatementAudit
end Exploding
