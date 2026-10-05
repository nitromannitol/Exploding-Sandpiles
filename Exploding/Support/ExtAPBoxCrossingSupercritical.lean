/-
The bond box-crossing input at the critical density, from the confined high-density
crossing.

The confined high-density crossing `xmw_highDensity_ae` already produces, above a
threshold, an almost sure open bond crossing that stays inside the box, for the good
cubes of the star duality.  Passing to probabilities with the almost-sure-to-limit
step `xmj2_tendsto_measure_one_of_ae_eventually` gives the confined crossing
probability tending to one, so the confinement transfer `xmj2_ConfinementTransfer`
of `Exploding.Support.ExtAPBoxCrossingBond` is no longer needed.  The only remaining
input is the RSW extension `xmj2_SupercriticalCrossingExtension`, which raises the
high-density bound to every density above `bondCritical d`.

Thus `xap15_BoxCrossing d` is *equivalent* to the RSW extension, in dimension at
least two, and the supercritical reduction `xap12_SupercriticalReduction` is
assembled from it together with the coarse-graining input
`xmj_BoxCrossingCoarseGraining`.  No star-duality or confinement input remains.
-/
import Exploding.Support.ExtAPBoxCrossingBond
import Exploding.Support.ExtAPBoxCrossingFinal
import Exploding.Support.ExtAPSupercritical

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology ENNReal

namespace Exploding

variable {d : ℕ}

/-! ### The confined high-density crossing, unconditionally -/

/-- **The confined high-density bond box crossing.**  Above a density threshold below one,
the probability that the box has an open bond crossing confined to it tends to one.  This is
the high-density input of the RSW extension, obtained directly from the almost sure confined
crossing without the confinement transfer. -/
theorem xmx_highDensity_openCrosses (d : ℕ) (hd : 2 ≤ d) :
    ∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧ ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      p ≤ q ^ (xap_cubeBonds (0 : Site d)).card →
      ∀ i : Fin d,
        Tendsto (fun n : ℕ => bondPercolation d q {ω | xap15_OpenCrosses d n i ω})
          Filter.atTop (𝓝 1) := by
  obtain ⟨p, hp0, hp1, hp⟩ := xmw_highDensity_ae (d := d) hd
  refine ⟨p, hp0, hp1, fun q hq0 hq1 hpq i => ?_⟩
  haveI : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb hq0 hq1
  exact xmj2_tendsto_measure_one_of_ae_eventually (bondPercolation d q)
    (fun n => xmw_openCrosses_measurable (n := n) i) (hp q hq0 hq1 hpq i)

/-! ### The sharpest named input -/

/-- **`xap15_BoxCrossing` reduces to the RSW extension.**  Given the supercritical crossing
extension, the confined high-density crossing gives the bond box crossing at every
density above the critical one. -/
theorem xmx_boxCrossing_of_extension (d : ℕ) (hd : 2 ≤ d)
    (hext : xmj2_SupercriticalCrossingExtension d) : xap15_BoxCrossing d :=
  hext (xmx_highDensity_openCrosses d hd)

/-- **The bond box crossing is equivalent to the RSW extension** in dimension at least two:
the extension is necessary and sufficient, once the confined high-density crossing is
available. -/
theorem xmx_boxCrossing_iff_extension (d : ℕ) (hd : 2 ≤ d) :
    xap15_BoxCrossing d ↔ xmj2_SupercriticalCrossingExtension d :=
  ⟨fun h _ => h, xmx_boxCrossing_of_extension d hd⟩

/-! ### The supercritical reduction -/

/-- **The supercritical reduction assembled from the RSW extension.**  The bond box crossing
supplied by the extension feeds the coarse-graining input of the high-density estimate. -/
theorem xmx_supercriticalReduction_of_extension
    (hext : ∀ d : ℕ, 2 ≤ d → xmj2_SupercriticalCrossingExtension d)
    (hcg : xmj_BoxCrossingCoarseGraining) : xap12_SupercriticalReduction :=
  xmj_supercriticalReduction_of_boxCrossing
    (fun d hd => xmx_boxCrossing_of_extension d hd (hext d hd)) hcg

end Exploding
