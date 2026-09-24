/-
Proposition 7.1 of the paper: a criterion for a background law to be explosive.
-/
import Exploding.Support.Hypotheses

open Exploding LatticeProb MeasureTheory

/-- **Proposition 7.1** (`exploding.tex:1821-1825`, label
`prop:explosion_criteria`).

"If Hypotheses 5.1 and 5.2 are satisfied and `P` is recurrent then `P` is
explosive."

The setting is that of Section 5: `P` is a probability measure on backgrounds
bounded between `η_min ≥ 0` and `2d - 1`, stationary and ergodic with respect to a
sublattice `L`, a finite-index subgroup of `ℤ^d`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.explosion_criteria (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : ErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h2 : BoxCrossingHyp d P)
    (hrec : RecurrentLaw d P) :
    ExplosiveLaw d P
-- FROZEN-STATEMENT-END
:= by sorry
