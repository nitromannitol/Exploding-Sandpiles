/-
The counting step of the recurrence argument of Proposition 7.3 of
`paper/exploding.tex`.
-/
import Exploding.Support.SubRecOne
import Exploding.Support.SubRecSub
import Exploding.Support.SubMax
import Exploding.Support.SubTopple

namespace Exploding

open LatticeProb
open scoped Classical

variable {d : ℕ}

/-- While some site of `V` has not toppled, the set of toppled sites of `V`
grows strictly. -/
theorem recOdo_filter_grows (d : ℕ) (hd : 1 ≤ d) (V : Finset (Site d)) (t : ℕ)
    (h : ∃ x ∈ V, recOdo d V t x = 0) :
    (V.filter (fun x => recOdo d V t x = 1)).card <
      (V.filter (fun x => recOdo d V (t + 1) x = 1)).card := by
  obtain ⟨x, hxV, hx0, hup⟩ := exists_max_unfilled d V t h
  have hx1 : x ∈ V.filter (fun x => recOdo d V (t+1) x = 1) :=
    Finset.mem_filter.mpr ⟨hxV, recOdo_topple d hd V t hxV hx0 hup⟩
  have hxnot : x ∉ V.filter (fun x => recOdo d V t x = 1) := fun hh => by
    rw [Finset.mem_filter] at hh; omega
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨recOdo_subset_succ d hd V t, fun heq => hxnot (heq ▸ hx1)⟩

end Exploding
