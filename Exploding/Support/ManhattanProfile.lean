import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The coordinate sum of absolute values on `ℝ^d`

The function `y ↦ ∑ i, |y i|` on `Fin d → ℝ` is continuous, convex and positively
one-homogeneous. This module proves exactly these three properties for this explicit
function, with no norm, no smoothness and no symmetry assumed.
-/

namespace Exploding.ManhattanProfile

open Finset

/-- The coordinate sum of absolute values `y ↦ ∑ i, |y i|` on `Fin d → ℝ` is continuous,
convex on `Set.univ`, and positively one-homogeneous, for every `d`. -/
theorem sum_abs_continuous_convexOn_smul (d : ℕ) :
    Continuous (fun y : Fin d → ℝ => ∑ i, |y i|) ∧
      ConvexOn ℝ Set.univ (fun y : Fin d → ℝ => ∑ i, |y i|) ∧
      ∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, ∑ i, |(c • y) i| = c * ∑ i, |y i| := by
  refine ⟨continuous_finsetSum _ fun i _ => (continuous_apply i).abs,
    ⟨convex_univ, ?_⟩, ?_⟩
  · intro x _ y _ a b ha hb _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun i _ => by
      simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a * x i) (b * y i)
  · intro c hc y
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc, mul_sum]

end Exploding.ManhattanProfile
