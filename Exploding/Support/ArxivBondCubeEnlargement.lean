import Exploding.Support.ExtAPProof

/-!
# Finite cube enlargements

Enlarging a finite set by unit cubes includes its star-neighbors and increases
its cardinality by at most a dimension-dependent factor.
-/

open LatticeProb

namespace Exploding

variable {d : ℕ}

/-- The union of the unit cubes centered at the sites of a finite set. -/
noncomputable def unitCubeEnlargement (F : Finset (Site d)) : Finset (Site d) :=
  F.biUnion xap_cubeFinset

/-- A set is contained in its unit-cube enlargement. -/
theorem subset_unit_cube_enlargement (F : Finset (Site d)) : F ⊆ unitCubeEnlargement F := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨x, hx, (xap_mem_cubeFinset x x).2 (xap_mem_cube_self x)⟩

/-- The unit-cube enlargement contains all star-neighbors of the set. -/
theorem mem_unit_cube_enlargement_of_star {F : Finset (Site d)} {x y : Site d}
    (hx : x ∈ F) (hxy : xap_Star x y) : y ∈ unitCubeEnlargement F := by
  exact Finset.mem_biUnion.mpr ⟨x, hx, (xap_mem_cubeFinset x y).2 (xap_star_mem_cube hxy)⟩

/-- A unit-cube enlargement has at most `3^d` sites per original site. -/
theorem card_unit_cube_enlargement_le (F : Finset (Site d)) :
    (unitCubeEnlargement F).card ≤ F.card * 3 ^ d := by
  classical
  refine Finset.card_biUnion_le.trans ?_
  simp only [xap_card_cubeFinset, Finset.sum_const, smul_eq_mul, le_refl]

/-- Two successive unit-cube enlargements have at most `3^(2d)` sites per
original site. -/
theorem card_unit_cube_enlargement_twice_le (F : Finset (Site d)) :
    (unitCubeEnlargement (unitCubeEnlargement F)).card ≤ F.card * (3 ^ d) ^ 2 := by
  calc
    _ ≤ (unitCubeEnlargement F).card * 3 ^ d := card_unit_cube_enlargement_le _
    _ ≤ (F.card * 3 ^ d) * 3 ^ d := Nat.mul_le_mul_right _ (card_unit_cube_enlargement_le F)
    _ = F.card * (3 ^ d) ^ 2 := by ring

end Exploding
