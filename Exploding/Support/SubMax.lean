/-
The maximizer step of the recurrence argument of Proposition 7.3 of
`paper/exploding.tex`: among the sites of `V` that have not yet toppled, one
maximizing the coordinate sum has all its `+e_i` neighbours toppled.
-/
import Exploding.Support.SubRec
import Exploding.Support.Wave

namespace Exploding

open LatticeProb
open scoped Classical

variable {d : ℕ}

/-- Among the sites of `V` that have not yet toppled, one maximizing the
coordinate sum has all its `+e_i` neighbours toppled. -/
theorem exists_max_unfilled (d : ℕ) (V : Finset (Site d)) (t : ℕ)
    (hnot : ∃ x ∈ V, recOdo d V t x = 0) :
    ∃ x ∈ V, recOdo d V t x = 0 ∧ ∀ i : Fin d, 1 ≤ recOdo d V t (x + unit i) := by
  classical
  obtain ⟨x0, hx0V, hx00⟩ := hnot
  have hs : (V.filter (fun x => recOdo d V t x = 0)).Nonempty :=
    ⟨x0, Finset.mem_filter.mpr ⟨hx0V, hx00⟩⟩
  obtain ⟨x, hxs, hmax⟩ := Finset.exists_max_image (V.filter (fun x => recOdo d V t x = 0))
    (fun x => ∑ i, x i) hs
  rw [Finset.mem_filter] at hxs
  refine ⟨x, hxs.1, hxs.2, fun i => ?_⟩
  by_cases hmem : x + unit i ∈ V
  · have h1 : recOdo d V t (x + unit i) ≠ 0 := by
      intro hz
      have h2 := hmax (x + unit i) (Finset.mem_filter.mpr ⟨hmem, hz⟩)
      have h3 : (∑ l, (x + unit i) l) = (∑ l, x l) + 1 := by
        simp [Pi.add_apply, unit, Finset.sum_add_distrib]
      omega
    have hnn := recOdo_nonneg d V t (x + unit i)
    omega
  · have hb : x + unit i ∈ outerBoundary (↑V : Set (Site d)) :=
      ⟨hmem, x, hxs.1, adj_add_unit x i⟩
    rw [recOdo_of_notMem d V t hmem, if_pos hb]

end Exploding
