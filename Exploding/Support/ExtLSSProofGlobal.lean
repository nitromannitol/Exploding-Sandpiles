/-
The finite-coordinate coupling built from a thinning.  The first coordinate is
the field on the ambient space, the second is the indicator of the thinned
subset, weighted by the thinning.  Its marginals and support make it a coupling
of the field to the product law, and the consistent family of these couplings is
the input to the projective-limit construction of the global coupling.
-/
import Exploding.Support.ExtLSSProofCouple

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Exploding

attribute [local instance] Classical.propDecidable

variable {S : Type}

/-- The coupling on the ambient space associated to a thinning on `T`: the first coordinate is
the field, the second is the indicator of the thinned subset, weighted by the thinning. -/
noncomputable def xlss8_couple [DecidableEq S] (μ : Measure (S → Bool)) (T : Finset S)
    (w : S → Bool → Finset S → ℝ) : Measure ((S → Bool) × (S → Bool)) :=
  ∑ V ∈ T.powerset,
    (μ.withDensity (fun x => ENNReal.ofReal (∏ l ∈ T, w l (x l) V))).prod
      (Measure.dirac (fun s => decide (s ∈ V)))

end Exploding
