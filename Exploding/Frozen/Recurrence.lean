/-
Proposition 7.3 of the paper: the constant background `d` is recurrent.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb

/-- **Proposition 7.3** (`exploding.tex:1906-1908`, label `prop:recurrence`).

"For every `d ≥ 1`, `η : ℤ^d → {d}` is recurrent."

Recurrence of `η` is `Exploding.Recurrent`: for every finite domain `V`, firing
`∂V` makes every site of `V` topple, that is, the `V^c`-frozen odometer from
`w_0 = 1{x ∈ ∂V}` equals `1` on `V` from time `|V|` on. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.recurrence (d : ℕ) (hd : 1 ≤ d) : Recurrent (fun _ : Site d => (d : ℤ))
-- FROZEN-STATEMENT-END
:= by sorry
