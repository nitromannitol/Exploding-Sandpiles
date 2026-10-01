/-
The finite-coordinate form of the product law: on a finite set of coordinates the
product measure of a finite set is the sum of the weights of its elements.  This
is the building block for the finite-coordinate domination step of the
bounded-degree theorem.
-/
import Exploding.Support.ExtLSSProofThin

open MeasureTheory ProbabilityTheory

namespace Exploding

/-- The finite product of probability measures on `ι → Bool`, evaluated on a finite set, as the
sum of the weights of its elements. -/
theorem xlss_pi_eq_sum {ι : Type*} [Fintype ι] (μ : ι → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] (B : Finset (ι → Bool)) :
    Measure.pi μ ((B : Set (ι → Bool))) = ∑ x ∈ B, ∏ i, μ i {x i} := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert a B ha ih =>
    rw [Finset.coe_insert, Finset.sum_insert ha]
    have hins : (insert a (↑B : Set (ι → Bool))) = ({a} : Set (ι → Bool)) ∪ (↑B : Set _) :=
      Set.insert_eq a (↑B : Set (ι → Bool))
    rw [hins, measure_union (by rw [Set.disjoint_singleton_left]; exact ha)
      B.finite_toSet.measurableSet, Measure.pi_singleton, ih]

end Exploding
