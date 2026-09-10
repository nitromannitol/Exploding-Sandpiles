/-
Theorem 1.4 of the paper: a product background with at least `d` chips
everywhere and a positive density of sites with `2d - 1` chips is explosive.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb MeasureTheory

/-- **Theorem 1.4** (`exploding.tex:265-268`, label `theorem:explosive`).

"Suppose `β : ℤ^d → ℤ` is drawn from a product measure `P`.  If `β ≥ d` and
`P(β(0) = (2d - 1)) > 0`, then `β` is explosive with probability 1."

`P` is the product measure with one-site law `ν`; `β ≥ d` is the statement that
`ν` gives full mass to `{m : d ≤ m}`, which is what "`β ≥ d`" asserts for a
product measure. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.explosive (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)}) :
    ∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => ν), Explosive β
-- FROZEN-STATEMENT-END
:= by sorry
