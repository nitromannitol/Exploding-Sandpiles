/-
Measurability of the domination support, and the compactness route to the global
coupling.
-/
import Exploding.Support.ExtLSSProofGlobal

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Exploding

attribute [local instance] Classical.propDecidable

variable {S : Type}

/-- The set on which the second coordinate lies below the first is measurable. -/
theorem xlss9_support_measurable [Countable S] :
    MeasurableSet {z : (S → Bool) × (S → Bool) | ∀ s, z.2 s = true → z.1 s = true} := by
  rw [show {z : (S → Bool) × (S → Bool) | ∀ s, z.2 s = true → z.1 s = true} =
      ⋂ s, ({z : (S → Bool) × (S → Bool) | z.2 s = false} ∪ {z | z.1 s = true}) from by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union]
    constructor
    · intro h s
      by_cases hz : z.2 s = true
      · exact Or.inr (h s hz)
      · exact Or.inl (by simpa using hz)
    · intro h s hz
      rcases h s with h' | h'
      · exact absurd hz (by simpa using h')
      · exact h']
  refine MeasurableSet.iInter fun s => ?_
  measurability

end Exploding
