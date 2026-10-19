/-
The box-crossing proposition of the paper, in both of its cases
(Proposition 7.5). For `d ≥ 2`, a product background
with at least `d` chips and a positive density of `(2d-1)`-sites is box-crossing. In dimension one,
any law supported on backgrounds `η ≥ 1` is box-crossing. Both clauses are stated here.
-/
import Exploding.Support.Hypotheses
import Exploding.External.Schonmann
import Exploding.Support.BCProofMain
import Exploding.Support.BCDimOne

open Exploding LatticeProb MeasureTheory

/-- **Box-crossing, both cases** (Proposition 7.5 of the paper).

"For `d ≥ 2`, the original product law `P` is box-crossing. In dimension one, any law supported on
backgrounds `η ≥ 1` is box-crossing."

The first conjunct is the product case: `P` is the product of `ν` with `ν(m ≥ d) = 1` and
`ν(2d-1) > 0`. Schonmann's bootstrap (`prop:schonnmann_bootstrap`),
which the paper cites rather than proves, enters as an explicit hypothesis of this conjunct only.
The second conjunct is the dimension-one case: any probability law supported on `η ≥ 1`, with no
product law and no Schonmann hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.box_crossing :
    (∀ (d : ℕ) (_hd : 2 ≤ d) (ν : Measure ℤ) (_hν : IsProbabilityMeasure ν)
      (_hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (_hhit : 0 < ν {(2 * (d : ℤ) - 1)})
      (_hSch : Exploding.External.SchonmannBootstrap),
      BoxCrossingHyp d (Measure.infinitePi fun _ : Site d => ν)) ∧
    (∀ (P : Measure (Site 1 → ℤ)) (_hP : IsProbabilityMeasure P)
      (_hsupp : P {η : Site 1 → ℤ | ∀ x, (1 : ℤ) ≤ η x} = 1),
      BoxCrossingHyp 1 P)
-- FROZEN-STATEMENT-END
:= by
  refine ⟨fun d hd ν hν hlow hhit hSch => bc_box_crossing d hd ν hν hlow hhit hSch, ?_⟩
  intro P hP hsupp
  haveI := hP
  exact bc_dim_one_box_crossing P hsupp
