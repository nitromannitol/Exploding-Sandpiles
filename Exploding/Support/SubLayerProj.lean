/-
The projection of a layer of `Q_n^{(d+1)}` onto `ℤ^d` is the box `Q_n^{(d)}`,
used in the proof of Proposition 7.5.
-/
import Exploding.Support.Reduction

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The layer `L_i = {x ∈ Q_n^{(d+1)} : x_0 = i}` of the proof of
Proposition 7.5. -/
def layer (d n : ℕ) (i : ℤ) : Set (Site (d + 1)) := {x ∈ cube (d + 1) n | x 0 = i}

/-- The projection of the layer `L_i` onto `ℤ^d` is the box `Q_n^{(d)}`. -/
theorem mem_layer_iff (d n : ℕ) (i : ℤ) (hi : 1 ≤ i) (hin : i ≤ (n : ℤ)) (y : Site d) :
    cons i y ∈ layer d n i ↔ y ∈ cube d n := by
  simp only [layer, cube, Set.mem_setOf_eq, cons]
  constructor
  · rintro ⟨hcube, -⟩
    intro j
    simpa [Fin.cons_succ] using hcube j.succ
  · intro hy
    refine ⟨?_, by simp [Fin.cons_zero]⟩
    intro j
    refine Fin.cases ?_ ?_ j
    · simpa [Fin.cons_zero] using ⟨hi, hin⟩
    · intro k
      simpa [Fin.cons_succ] using hy k

end Exploding
