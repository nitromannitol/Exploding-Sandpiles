import Exploding.Support.ArxivBondConfinedDistance
import Exploding.Support.ArxivBondCubeEnlargement

/-!
# Chemical distance in an enlarged region

An open walk inside the double unit-cube enlargement of a finite set has
chemical distance bounded by a dimension-dependent multiple of the set's size.
-/

open LatticeProb

namespace Exploding

variable {d : ℕ}

/-- An open walk in the double enlargement bounds chemical distance by the
cardinality of the original set times `3^(2d)`. -/
theorem open_bond_edist_lt_double_enlargement_bound
    {ω : Site d × Fin d → Bool} {x y : Site d} (F : Finset (Site d))
    (p : (openBondGraph ω).Walk x y)
    (hp : ∀ z ∈ p.support, z ∈ unitCubeEnlargement (unitCubeEnlargement F)) :
    (openBondGraph ω).edist x y < ((F.card * (3 ^ d) ^ 2 : ℕ) : ℕ∞) := by
  have hdist := open_bond_edist_lt_card_of_walk_support_subset
    (unitCubeEnlargement (unitCubeEnlargement F)) p hp
  have hcard : (((unitCubeEnlargement (unitCubeEnlargement F)).card : ℕ) : ℕ∞) ≤
      ((F.card * (3 ^ d) ^ 2 : ℕ) : ℕ∞) := by
    exact_mod_cast card_unit_cube_enlargement_twice_le F
  exact lt_of_lt_of_le hdist hcard

end Exploding
