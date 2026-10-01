/-
The localisation of the hole boundary needs the box to grow with the hole's diameter: an
open ball of radius `R` centred in `cent d n` has its boundary at distance `R`, so the
frozen form `∃ p ∈ ∂°B, p ∈ cent d n` is too strong.  The correct statement is recorded here,
together with the elementary bound that the boundary lies in `cent d (n + R)` when the hole
lies within sup-norm `R` of a point of `cent d n`.
-/
import Exploding.Support.ExtMHProof15

namespace Exploding

open LatticeProb MeasureTheory Filter
open scoped BigOperators

variable {d : ℕ}
variable {q : ℝ}

/-- If a set lies within sup-norm `R` of a point of `cent d n`, it lies in `cent d (n + R)`. -/
theorem xmh12_subset_cent {B : Set (Site d)} {x0 : Site d} {n R : ℕ}
    (hx0 : x0 ∈ cent d n) (hR : ∀ z ∈ B, ∀ i, |z i - x0 i| ≤ (R : ℤ)) :
    B ⊆ cent d (n + R) := by
  intro z hz i
  have h1 : z i = x0 i + (z i - x0 i) := by ring
  have h2 : |z i| ≤ |x0 i| + |z i - x0 i| := by
    have ha := abs_add_le (x0 i) (z i - x0 i)
    have hb : x0 i + (z i - x0 i) = z i := by ring
    rwa [hb] at ha
  have h3 : |x0 i| ≤ (n : ℤ) := hx0 i
  have h4 : |z i - x0 i| ≤ (R : ℤ) := hR z hz i
  have h5 : ((n : ℤ) + (R : ℤ)) = ((n + R : ℕ) : ℤ) := by push_cast; ring
  linarith

/-- The inner boundary is contained in the hole. -/
theorem xmh12_innerBoundary_subset (B : Set (Site d)) : innerBoundary B ⊆ B :=
  fun _ hz => hz.1

/-- **Corrected localisation.**  If a hole `B` meeting `cent d n` lies within sup-norm `R` of a
point of `cent d n`, its inner boundary meets `cent d (n + R)`. -/
theorem xmh12_boundary_meets_cent {B : Set (Site d)} {x0 : Site d} {n R : ℕ}
    (hx0 : x0 ∈ cent d n) (hR : ∀ z ∈ B, ∀ i, |z i - x0 i| ≤ (R : ℤ))
    (hne : (innerBoundary B).Nonempty) :
    ∃ p ∈ innerBoundary B, p ∈ cent d (n + R) := by
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, hp, xmh12_subset_cent hx0 hR (xmh12_innerBoundary_subset B hp)⟩

/-- The corrected localisation claim used by the assembly: the inner boundary of a hole
meeting `cent d n` is contained in a box whose radius is the hole's sup-norm diameter plus `n`. -/
def xmh12_Localized (d : ℕ) (q : ℝ) : Prop :=
  ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
    ∀ n : ℕ, ∀ x ∈ cent d n, x ∉ C →
      xmh3_V n ≤ ((componentIn Cᶜ x).ncard : ℝ) →
      ∃ R : ℕ, (∀ z ∈ componentIn Cᶜ x, ∀ i, |z i - x i| ≤ (R : ℤ)) ∧
        (componentIn Cᶜ x).Nonempty ∧
        ∃ p ∈ innerBoundary (componentIn Cᶜ x), p ∈ cent d (n + R)

end Exploding
