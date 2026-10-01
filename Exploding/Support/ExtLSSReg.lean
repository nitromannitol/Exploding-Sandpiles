/-
The product Bernoulli law on a countable index set is a probability measure and is inner
regular by closed sets: the configuration space is a compact metrizable space whose Borel
sigma-algebra is the product sigma-algebra, and a finite Borel measure on a metrizable
space is weakly regular.
-/
import Mathlib
import Exploding.Support.RNProofGraph

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Exploding

variable {S : Type}

/-- The product Bernoulli law is a probability measure for a density in `[0, 1]`. -/
theorem xlsd_isProbabilityMeasure (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    IsProbabilityMeasure (bernoulliProduct S ρ) := by
  unfold bernoulliProduct
  exact rn_infinitePi_isProb hρ0 hρ1

/-- Inner regularity of the product Bernoulli law by closed sets, on a countable index set. -/
theorem xlsd_measure_eq_iSup_isClosed [Countable S] (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {A : Set (S → Bool)} (hA : MeasurableSet A) :
    bernoulliProduct S ρ A =
      ⨆ (F : Set (S → Bool)) (_ : F ⊆ A) (_ : IsClosed F), bernoulliProduct S ρ F := by
  haveI := xlsd_isProbabilityMeasure (S := S) ρ hρ0 hρ1
  exact hA.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top _ _)

end Exploding
