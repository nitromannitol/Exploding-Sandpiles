/-
Unconditional consequences of the box-crossing star duality.

`Exploding.xmh_starDuality` proves `xbc_StarDuality d` for `d ≥ 2`.  Instantiating the
conditional lemmas removes the duality hypothesis: the site crossing probability tends to one,
almost surely every large box is crossed, and the good sites of bond percolation give an open
bond crossing.
-/
import Exploding.Support.ExtBCBernoulli3
import Exploding.Support.ExtAPBridge
import Exploding.Support.ExtAPMinCutStarFinal

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology ENNReal

namespace Exploding

variable {d : ℕ}

/-- The high-density site box-crossing probability tends to one, unconditionally. -/
theorem xmv_crossing_tendsto (hd : 2 ≤ d) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hr : xbc_rho d q < 1) (i : Fin d) :
    Tendsto (fun n : ℕ => sitePercolation d q {ω | xbc_Crosses d n i ω}) atTop (𝓝 1) :=
  xbc_crossing_tendsto (xmh_starDuality d hd) h0 h1 hr i

/-- Almost surely every large box is crossed at high density, unconditionally. -/
theorem xmv_ae_eventually_crosses (hd : 2 ≤ d) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hr : xbc_rho d q < 1) (i : Fin d) :
    ∀ᵐ ω ∂(sitePercolation d q), ∀ᶠ n : ℕ in atTop, xbc_Crosses d n i ω :=
  xbc_ae_eventually_crosses (xmh_starDuality d hd) h0 h1 hr i

/-- The good sites of bond percolation cross a large box when the density is high,
unconditionally. -/
theorem xmv_bond_box_crossing (hd : 2 ≤ d) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hrho : xbc_rho d ρ < 1) :
    ∃ p : ℝ, 0 ≤ p ∧ p < 1 ∧ ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      p ≤ q ^ (xap_cubeBonds (0 : Site d)).card →
      ∀ i : Fin d, ∀ᵐ ω ∂(bondPercolation d q),
        ∀ᶠ n : ℕ in atTop, xbb_BondCrosses d n i ω :=
  xbb_bond_box_crossing (xmh_starDuality d hd) (by omega) hρ0 hρ1 hrho

end Exploding
