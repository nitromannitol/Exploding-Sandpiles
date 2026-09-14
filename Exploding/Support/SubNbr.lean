/-
The neighbour sum is monotone in its argument when the comparison is known only
at the neighbours, which is the form Section 4 of `paper/exploding.tex` needs:
the frozen odometer dominates the last wave off the frozen set, and on the
frozen set the domination is read off the inner boundary.
-/
import Exploding.Support.Wave

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- `nbrSumZ` is monotone when the comparison is known at the neighbours. -/
theorem nbrSumZ_le_of_adj (u v : Site d → ℤ) (x : Site d)
    (h : ∀ y, (lattice d).Adj y x → u y ≤ v y) :
    nbrSumZ u x ≤ nbrSumZ v x := by
  simp only [Exploding.nbrSumZ]
  exact Finset.sum_le_sum (fun i _ => add_le_add (h _ (adj_add_unit x i)) (h _ (adj_sub_unit x i)))

end Exploding
