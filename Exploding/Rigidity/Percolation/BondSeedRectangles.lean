/-
Copied from Percolation-Rigidity (https://github.com/nitromannitol/Percolation-Rigidity), commit
d5b6dd0b0019636ea3c88ad0f7da087a6ac194c3, file `Rigidity/Percolation/BondSeedRectangles.lean`,
licensed under the Apache License 2.0.
Changes: the module paths of the imports (`Rigidity.*` becomes `Exploding.Rigidity.*`); the
namespace `LatticeProb.Percolation` of the Lattice-Probability bond model becomes
`Exploding.LatticeBond`; deprecated lemma names are replaced by their current names
(`Finset.prod_le_prod'`, `Set.mem_setOf_eq`).
-/
import Exploding.Rigidity.Percolation.BondSeedCardinality
import Exploding.Rigidity.Percolation.BondSeedExploration

/-!
# Rectangular bond seeds

A uniform side-length bound gives a uniform bound on the number of bonds in
an integer rectangle, independently of its position.
-/

namespace Rigidity.Percolation

open Exploding.LatticeBond

/-- The number of vertices in an integer rectangle is the product of its
integer side lengths. -/
theorem card_latticeRectangle {d : ℕ} (lo hi : Vertex d) :
    (finite_latticeRectangle lo hi).toFinset.card =
      ∏ i : Fin d, (hi i - lo i).toNat := by
  classical
  have heq : (finite_latticeRectangle lo hi).toFinset =
      Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)) := by
    ext x
    simp only [Set.Finite.mem_toFinset, latticeRectangle, Set.mem_ofPred_eq,
      Fintype.mem_piFinset, Finset.mem_Ico]
  rw [heq, Fintype.card_piFinset]
  simp only [Int.card_Ico]

/-- Side lengths bounded by `M` give at most `M ^ d` vertices. -/
theorem card_latticeRectangle_le {d : ℕ} (lo hi : Vertex d) (M : ℕ)
    (hM : ∀ i, (hi i - lo i).toNat ≤ M) :
    (finite_latticeRectangle lo hi).toFinset.card ≤ M ^ d := by
  rw [card_latticeRectangle]
  calc
    (∏ i : Fin d, (hi i - lo i).toNat) ≤ ∏ _i : Fin d, M :=
      Finset.prod_le_prod (fun i _ => hM i)
    _ = M ^ d := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Internal bonds of rectangles with side lengths at most `M` are uniformly
bounded in number, regardless of the rectangle's location. -/
theorem card_localBonds_latticeRectangle_le {d : ℕ} (lo hi : Vertex d) (M : ℕ)
    (hM : ∀ i, (hi i - lo i).toNat ≤ M) :
    (finite_localBonds (finite_latticeRectangle lo hi)).toFinset.card ≤ (M ^ d) ^ 2 :=
  card_localBonds_le_of_card_le (finite_latticeRectangle lo hi)
    (card_latticeRectangle_le lo hi M hM)

end Rigidity.Percolation
