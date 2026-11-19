import Exploding.Support.Percolation
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Chemical distance in a finite region

Loop erasure bounds the chemical distance between two vertices by the number of
sites in any finite region containing an open walk between them.
-/

open LatticeProb

namespace Exploding

variable {d : ℕ}

/-- An open walk confined to a finite set gives a chemical distance strictly
smaller than the cardinality of that set. -/
theorem open_bond_edist_lt_card_of_walk_support_subset
    {ω : Site d × Fin d → Bool} {x y : Site d} (F : Finset (Site d))
    (p : (openBondGraph ω).Walk x y) (hF : ∀ z ∈ p.support, z ∈ F) :
    (openBondGraph ω).edist x y < (F.card : ℕ∞) := by
  classical
  let w : (openBondGraph ω).Walk x y := p.toPath
  have hsubset : w.support.toFinset ⊆ F := by
    intro z hz
    exact hF z (p.support_toPath_subset_support (List.mem_toFinset.mp hz))
  have hcard : w.length + 1 ≤ F.card := by
    calc
      w.length + 1 = w.support.length := (SimpleGraph.Walk.length_support w).symm
      _ = w.support.toFinset.card :=
        (List.toFinset_card_of_nodup p.toPath.isPath.support_nodup).symm
      _ ≤ F.card := Finset.card_le_card hsubset
  have hlen : (w.length : ℕ∞) < (F.card : ℕ∞) := by
    exact_mod_cast (show w.length < F.card by omega)
  exact lt_of_le_of_lt (SimpleGraph.edist_le w) hlen

end Exploding
