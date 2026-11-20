import Exploding.Support.LimitShapeUnconditional
import ExplodingAudit.LimitShapeUnconditional.SolutionBasic

/-!
# Limit shape: comparator solution

The independently stated limit shape follows from the chemical-distance-free theorem.
-/

open MeasureTheory Filter

namespace Exploding
namespace StatementAudit
namespace LimitShapeUnconditional

/-- The limit shape theorem without a chemical-distance assumption. -/
theorem limit_shape_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    :
    ∃ B : Set (Fin d → ℝ),
      Convex ℝ B ∧ IsOpen B ∧ B.Nonempty ∧
      ∀ᵐ η ∂(toyLaw d p),
        Tendsto
          (fun t : ℕ =>
            volume (symmDiff
              {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} B))
          atTop (nhds 0)
:= by
  set_option smartUnfolding false in
  exact Exploding.limit_shape_unconditional d hd p hp hp1

end LimitShapeUnconditional
end StatementAudit
end Exploding
