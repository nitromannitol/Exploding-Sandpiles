/-
Proposition 7.3 of the paper: the constant background `d` is recurrent.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubRecMin

open Exploding LatticeProb

/-- **Proposition 7.3** (`paper/corrected-arxiv/exploding-corrected-arxiv.tex:2575-2577`, label `prop:recurrence`).

"For every `d ≥ 1`, `η : ℤ^d → {d}` is recurrent."

Recurrence of `η` is `Exploding.Recurrent`: for every finite domain `V`, firing
`∂V` makes every site of `V` topple, that is, the `V^c`-frozen odometer from
`w_0 = 1{x ∈ ∂V}` equals `1` on `V` from time `|V|` on. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.recurrence (d : ℕ) (hd : 1 ≤ d) : Recurrent (fun _ : Site d => (d : ℤ))
-- FROZEN-STATEMENT-END
:= by
  intro V t ht x hx
  have h1 : min t V.card ≤ (V.filter (fun x => recOdo d V t x = 1)).card := recOdo_card_le d hd V t
  have h2 : (V.filter (fun x => recOdo d V t x = 1)).card ≤ V.card := Finset.card_filter_le _ _
  have h3 : V.card ≤ t := ht
  have h4 : min t V.card = V.card := by rw [Nat.min_comm]; exact min_eq_left h3
  have h5 : (V.filter (fun x => recOdo d V t x = 1)).card = V.card := le_antisymm h2 (h4 ▸ h1)
  have h6 : V.filter (fun x => recOdo d V t x = 1) = V :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [h5])
  have h7 : x ∈ V.filter (fun x => recOdo d V t x = 1) := by rw [h6]; exact hx
  rw [Finset.mem_filter] at h7
  exact h7.2
