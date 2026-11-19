/-
The high-density chemical-distance bound implies the almost-sure all-pairs
estimate at every density above its threshold.
-/
import Exploding.Support.RNProofChem
import Exploding.Support.ExtAPProof12

open MeasureTheory Exploding LatticeProb

namespace Exploding

/-- A high-density chemical-distance bound gives the almost-sure all-pairs estimate. -/
theorem rn_chem_ae_of_highDensity (hChem : xap12_HighDensityBound) (d : ℕ)
    (hd : 2 ≤ d) :
    ∃ q0 : ℝ, q0 < 1 ∧ ∀ q : ℝ, q0 < q → 0 ≤ q → q ≤ 1 →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ᵐ ζ ∂(bondPercolation d q), RnChemProp d C ζ := by
  obtain ⟨q0, hq0, hbound⟩ := hChem d hd
  refine ⟨q0, hq0, fun q hq hq0' hq1 => ?_⟩
  exact rn_chem_ae_of_bound d hq0' hq1 (hbound q hq hq1)

end Exploding
