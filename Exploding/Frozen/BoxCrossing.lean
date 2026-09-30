/-
Proposition 7.5 of the paper: a product background with at least `d` chips and
a positive density of `(2d-1)`-sites is box-crossing.
-/
import Exploding.Support.Hypotheses
import Exploding.External.Schonmann
import Exploding.Support.BCProofMain

open Exploding LatticeProb MeasureTheory

/-- **Proposition 7.5** (`exploding.tex:1986-1988`, the unlabelled proposition
of Section 7.3).

"In all dimensions, `P` is box-crossing."

`P` is the measure of Section 7: a product measure with `P(η ≥ d) = 1` and
`P(η(0) = 2d - 1) > 0`.

Schonmann's bound, Proposition 7.4 of the paper, which the paper cites rather
than proves, enters as the explicit hypothesis `hSch`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.box_crossing (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)})
    (hSch : Exploding.External.SchonmannBootstrap) :
    BoxCrossingHyp d (Measure.infinitePi fun _ : Site d => ν)
-- FROZEN-STATEMENT-END
:= by
  exact bc_box_crossing d hd ν hν hlow hhit hSch
