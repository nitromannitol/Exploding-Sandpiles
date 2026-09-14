/-
The layer decomposition of the box used in the proof of Proposition 7.5:
`Q_n^{(d+1)} = ⋃_{i=1}^{n} L_i` with `L_i = {x ∈ Q_n^{(d+1)} : x_0 = i}`.
-/
import Exploding.Support.Reduction

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The layer `L_i = {x ∈ Q_n^{(d+1)} : x_0 = i}` of the proof of
Proposition 7.5. -/
def layer (d n : ℕ) (i : ℤ) : Set (Site (d + 1)) := {x ∈ cube (d + 1) n | x 0 = i}

/-- The box is the union of its layers. -/
theorem cube_eq_iUnion_layer (d n : ℕ) :
    cube (d + 1) n = ⋃ i ∈ Finset.Icc 1 n, layer d n (i : ℤ) := by
  ext x
  simp only [Set.mem_iUnion, layer, cube, Set.mem_setOf_eq, Finset.mem_Icc]
  constructor
  · intro h
    have h0 := h 0
    have hpos : 0 ≤ x 0 := by omega
    have hcast : (↑(x 0).toNat : ℤ) = x 0 := Int.toNat_of_nonneg hpos
    refine ⟨(x 0).toNat, ⟨?_, ?_⟩, h, ?_⟩
    · omega
    · omega
    · omega
  · rintro ⟨i, ⟨hi1, hin⟩, hx, hx0⟩
    exact hx

end Exploding
