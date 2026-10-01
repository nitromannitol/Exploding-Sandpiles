/-
The corrected localisation of the hole boundary: with the box growing with the hole, the
inner boundary of a hole meeting `cent d n` lies in `cent d (n + R)` whenever `R` bounds the
sup-norm diameter from a point of `cent d n`.  The frozen form with `R = 0` is false (a ball
of radius `R` centred in the box), so the assembly must apply the bad event at the hole's own
scale.
-/
import Exploding.Support.ExtMHProof16

namespace Exploding

open LatticeProb MeasureTheory Filter Relation
open scoped BigOperators

variable {d : ℕ}
variable {q : ℝ}

/-- The inner boundary of a hole lies in the box whose radius is the hole's diameter plus `n`. -/
theorem xmh13_innerBoundary_subset_cent {B : Set (Site d)} {x : Site d} {n R : ℕ}
    (hx : x ∈ cent d n) (hR : ∀ z ∈ B, ∀ i, |z i - x i| ≤ (R : ℤ)) :
    innerBoundary B ⊆ cent d (n + R) :=
  (xmh12_innerBoundary_subset B).trans (xmh12_subset_cent hx hR)

/-- The corrected localisation: the inner boundary of a hole meeting `cent d n` meets
`cent d (n + R)` for any `R` bounding its sup-norm diameter from a point of `cent d n`. -/
theorem xmh13_boundary_meets_cent {B : Set (Site d)} {x : Site d} {n R : ℕ}
    (hx : x ∈ cent d n) (hR : ∀ z ∈ B, ∀ i, |z i - x i| ≤ (R : ℤ))
    (hne : (innerBoundary B).Nonempty) :
    ∃ p ∈ innerBoundary B, p ∈ cent d (n + R) :=
  xmh12_boundary_meets_cent hx hR hne

/-- The corrected localisation claim: a hole meeting `cent d n` of volume above `xmh3_V n` has
its inner boundary in a box growing with its diameter. -/
def xmh13_Localized (d : ℕ) (q : ℝ) : Prop :=
  ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
    ∀ n : ℕ, ∀ x ∈ cent d n, x ∉ C →
      xmh3_V n ≤ ((componentIn Cᶜ x).ncard : ℝ) →
      ∃ R : ℕ, (∀ z ∈ componentIn Cᶜ x, ∀ i, |z i - x i| ≤ (R : ℤ)) ∧
        (innerBoundary (componentIn Cᶜ x)).Nonempty ∧
        ∃ p ∈ innerBoundary (componentIn Cᶜ x), p ∈ cent d (n + R)

end Exploding
