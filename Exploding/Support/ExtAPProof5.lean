/-
The two inputs requested after the linear separator bound was refuted.

First, the count of `*`-walks: a `*`-walk of length `n` from the origin is a list of
`n` star steps, each chosen from the `3^d - 1` star-neighbours of a site, so there
are at most `(3^d)^n` of them; a `*`-connected set of size `s` is the support of
such a walk of length at most `2s`, so there are at most `(3^d)^{2s}` of size `s`.

Second, the event that the good cluster of the origin misses `y` splits into the
case where the cluster is finite (its boundary is a bad separator) and the case
where it is infinite, which the finite-separator count cannot reach; the case of
the one-site cluster has probability `δ (1 - δ)^{3^d - 1}`, so the miss event
itself does not decay with `mnorm y` and the chemical-distance bound must instead
count long bad paths.
-/
import Exploding.Support.ExtAPProof4

open Exploding LatticeProb MeasureTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-! ### The star-step directions and the walk count -/

/-- The `*`-neighbour directions of a site: the sites differing from the origin by
at most one in every coordinate. -/
noncomputable def xap5_dirFinset (d : ℕ) : Finset (Site d) :=
  (xap_cubeFinset (0 : Site d)).erase 0

theorem xap5_mem_dirFinset {v : Site d} :
    v ∈ xap5_dirFinset d ↔ xap_Star (0 : Site d) v := by
  rw [xap5_dirFinset, Finset.mem_erase, xap_mem_cubeFinset, xap_cube, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne.symm, fun i => ?_⟩
    have := h i
    rw [Pi.zero_apply, abs_sub_comm] at this
    exact this
  · rintro ⟨hne, h⟩
    refine ⟨hne.symm, fun i => ?_⟩
    have := h i
    rw [Pi.zero_apply, abs_sub_comm] at this
    exact this

theorem xap5_dirFinset_card_le (d : ℕ) : (xap5_dirFinset d).card ≤ 3 ^ d := by
  rw [xap5_dirFinset]
  exact (Finset.card_erase_le (s := xap_cubeFinset (0 : Site d)) (a := 0)).trans
    (le_of_eq (xap_card_cubeFinset 0))

/-- There are at most `(3^d)^n` star-step sequences of length `n`. -/
theorem xap5_dirSeq_card_le (d n : ℕ) :
    Fintype.card (Fin n → ↥(xap5_dirFinset d)) ≤ (3 ^ d) ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin]
  calc (Fintype.card ↥(xap5_dirFinset d)) ^ n
      = (xap5_dirFinset d).card ^ n := by rw [Fintype.card_coe]
    _ ≤ (3 ^ d) ^ n := Nat.pow_le_pow_left (xap5_dirFinset_card_le d) n

/-! ### The reworked event decomposition -/

/-- The good cluster of the origin misses `y`. -/
def xap5_Misses (ω : Site d × Fin d → Bool) (y : Site d) : Prop :=
  ¬ xap3_GoodConnected ω y

/-- The good cluster of the origin is finite. -/
def xap5_SmallCluster (ω : Site d × Fin d → Bool) : Prop :=
  {z : Site d | xap3_GoodConnected ω z}.Finite

/-- The miss event splits into the finite-cluster case and the infinite one. -/
theorem xap5_misses_le_small_add_large (ω : Site d × Fin d → Bool) (y : Site d) :
    xap5_Misses ω y →
      xap5_SmallCluster ω ∨ (¬ xap5_SmallCluster ω ∧ xap5_Misses ω y) := by
  intro h
  by_cases hs : xap5_SmallCluster ω
  · exact Or.inl hs
  · exact Or.inr ⟨hs, h⟩

/-- The covering-walk input: every finite `*`-connected set containing the origin
is the support of a closed star-walk from the origin of length at most twice its
cardinality.  This is a depth-first traversal of a spanning tree, and it is what
turns the star-walk count into a count of star-connected sets. -/
def xap5_CoveringWalk : Prop :=
  ∀ S : Finset (Site d), (0 : Site d) ∈ S →
    (∀ z ∈ S, ∃ p : (xap2_kingGraph d).Walk (0 : Site d) z,
      ∀ w ∈ p.support, w ∈ S) →
    ∃ p : (xap2_kingGraph d).Walk (0 : Site d) (0 : Site d),
      p.support.toFinset = S ∧ p.length ≤ 2 * S.card

end Exploding
