/-
The counting step of the recurrence argument of Proposition 7.3 of
`paper/corrected-arxiv/exploding-corrected-arxiv.tex`.
-/
import Exploding.Support.SubRecOne
import Exploding.Support.SubRecSub
import Exploding.Support.SubMax
import Exploding.Support.SubRecCard
import Exploding.Support.SubTopple

namespace Exploding

open LatticeProb
open scoped Classical

variable {d : ℕ}

/-- After `min t |V|` steps, at least `min t |V|` sites of `V` have toppled. -/
theorem recOdo_card_le (d : ℕ) (hd : 1 ≤ d) (V : Finset (Site d)) (t : ℕ) :
    min t V.card ≤ (V.filter (fun x => recOdo d V t x = 1)).card := by
  induction t with
  | zero => simp
  | succ t ih =>
    by_cases h : ∃ x ∈ V, recOdo d V t x = 0
    · have := recOdo_filter_grows d hd V t h
      omega
    · simp only [not_exists, not_and] at h
      have hV : V.filter (fun x => recOdo d V t x = 1) = V := by
        apply Finset.ext
        intro x
        rw [Finset.mem_filter]
        constructor
        · exact fun hh => hh.1
        · intro hx
          refine ⟨hx, ?_⟩
          have h1 := recOdo_le_one d hd V t hx
          have h2 := recOdo_nonneg d V t x
          have h3 := h x hx
          omega
      have hc : (V.filter (fun x => recOdo d V t x = 1)).card = V.card := by rw [hV]
      have hmono := Finset.card_le_card (recOdo_subset_succ d hd V t)
      omega

end Exploding
