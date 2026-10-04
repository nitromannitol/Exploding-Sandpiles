/-
The supercritical-density reduction of the chemical-distance estimate.

`Exploding.xap12_SupercriticalReduction` asserts that the high-density bound
`xap12_HighDensityBound` — proved at densities close to one — extends to the
frozen statement `Exploding.External.AntalPisztoraChemicalDistance`, which holds
at **every** density `q > bondCritical d`.  The extension is the renormalisation
of Antal--Pisztora: at such a density the boxes of a fixed large scale are crossed
with probability close to one (the input `xap15_BoxCrossing`), the crossed boxes
percolate, and the chemical distance inside the resulting cluster is comparable
to the `mnorm` distance with an exponential upper tail.

This file isolates the renormalisation as the single named input
`xmj_BoxCrossingCoarseGraining` and proves the reduction
`xap12_SupercriticalReduction` from it together with the box-crossing input
(`xmj_supercriticalReduction_of_boxCrossing`).  It also records that the
high-density bound is exactly the frozen statement restricted to a density close
to one (`xmj_highDensity_of_antalPisztora`), so the reduction adds no content at
high density.

**Refuted route — monotonicity.**  One cannot transfer the high-density bound to
lower densities by the pointwise coupling of configurations.  Adding open bonds
may shorten the shortest path below `ρ |y|` while leaving it finite, so
`xap12_BigDistance` is not monotone: on `ℤ²` with `y = (2,0)` and `ρ = 3/2`, the
configuration whose only open bonds form the detour
`0 → (0,1) → (1,1) → (2,1) → (2,0)` has distance `4 > 3` and so satisfies
`BigDistance`, while the larger configuration that also opens the straight path
`0 → (1,0) → (2,0)` has distance `2 < 3` and does not.  Hence the renormalisation
is genuinely needed.
-/
import Exploding.Support.ExtAPBridge

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology

namespace Exploding

variable {d : ℕ}

/-! ### The coarse-graining input -/

/-- The renormalisation step of the supercritical reduction: box crossings at
every density above the critical one imply the chemical-distance large deviation
at that density.  This is the coarse-graining of Antal--Pisztora and is the single
input needed to extend the high-density bound. -/
def xmj_BoxCrossingCoarseGraining : Prop :=
  ∀ d : ℕ, 2 ≤ d → xap15_BoxCrossing d →
    ∀ q : ℝ, bondCritical d < q → q ≤ 1 →
      ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
        bondPercolation d q {ω | xap12_BigDistance d ρ ω y} ≤
          ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ))))

/-- The supercritical-density reduction follows from the box-crossing input and
its coarse-graining: the high-density hypothesis is not used, because the
renormalisation proves the bound directly at every supercritical density. -/
theorem xmj_supercriticalReduction_of_boxCrossing
    (hbc : ∀ d : ℕ, 2 ≤ d → xap15_BoxCrossing d)
    (hcg : xmj_BoxCrossingCoarseGraining) : xap12_SupercriticalReduction :=
  fun _ d hd q hq hq1 => hcg d hd (hbc d hd) q hq hq1

/-- The supercritical reduction is, by definition, the extension of the
high-density bound; the named coarse-graining input is exactly what its proof
has to supply. -/
theorem xmj_supercriticalReduction_iff :
    xap12_SupercriticalReduction ↔
      (xap12_HighDensityBound → Exploding.External.AntalPisztoraChemicalDistance) :=
  Iff.rfl

/-! ### The high-density bound is the frozen statement at high density -/

/-- The frozen statement is stronger than the high-density bound: its density
range `q > bondCritical d` already includes the high-density range, because
`bondCritical d < 1`. -/
theorem xmj_highDensity_of_antalPisztora
    (h : Exploding.External.AntalPisztoraChemicalDistance) : xap12_HighDensityBound :=
  fun d hd =>
    ⟨bondCritical d, xap13_bondCritical_lt_one hd, fun q hq hq1 => h d hd q hq hq1⟩

/-- Consequently the high-density hypothesis of the supercritical reduction is
redundant as soon as the frozen node is available, and the supercritical
reduction then holds outright. -/
theorem xmj_supercriticalReduction_of_antalPisztora
    (h : Exploding.External.AntalPisztoraChemicalDistance) : xap12_SupercriticalReduction :=
  fun _ => h

/-! ### The assembled reduction -/

/-- The frozen statement follows from the supercritical reduction and the two
corrected cluster halves. -/
theorem xmj_antalPisztora_of_parts (hSuper : xap12_SupercriticalReduction)
    (hFin : xap13_FiniteClusterBound) (hInf : xap13_InfiniteClusterBound) :
    Exploding.External.AntalPisztoraChemicalDistance :=
  xap13_AntalPisztora_of_bounds hSuper hFin hInf

end Exploding
