import Exploding.Support.ArxivAllHighCrossing

/-!
# The deterministic endpoint of the crossing bound

At parameter one, the actual product background law is concentrated on the
all-high configuration.  That configuration is good at scale one for every
line seed in the closed cube, so the source crossing bound has probability one.
-/

namespace Exploding

open MeasureTheory
open LatticeProb

/-- At parameter one, the one-site chip law is concentrated at its first value. -/
theorem chipLaw_one_eq_dirac (a b : ℤ) :
    chipLaw a b (1 : ℝ) = Measure.dirac a := by
  simp [chipLaw]

/-- The actual product law at parameter one is concentrated on the all-high
configuration. -/
theorem toyLaw_one_eq_dirac (d : ℕ) :
    toyLaw d (1 : ℝ) = Measure.dirac (fun _ : Site d => 2 * (d : ℤ) - 1) := by
  simp [toyLaw, productLaw, chipLaw]

/-- The all-high configuration belongs to the actual scale-one good-cube event,
which therefore has measure one under the actual endpoint law. -/
theorem toyLaw_one_goodCube_measure (d : ℕ) (hd : 2 ≤ d) :
    toyLaw d (1 : ℝ) {η | GoodCube η 1} = 1 := by
  rw [toyLaw_one_eq_dirac]
  exact Measure.dirac_apply_of_mem (arxivAllHigh_goodOne d hd)

/-- The corrected-source crossing bound holds at parameter one with the
scale-one witness. -/
theorem crossing_time_p1 (d : ℕ) (hd : 2 ≤ d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧
      ENNReal.ofReal (1 - δ) ≤ toyLaw d (1 : ℝ) {η | GoodCube η k} := by
  refine ⟨1, by norm_num, ?_⟩
  calc
    ENNReal.ofReal (1 - δ) ≤ 1 :=
      ENNReal.ofReal_le_one.mpr (by linarith)
    _ = toyLaw d (1 : ℝ) {η | GoodCube η 1} :=
      (toyLaw_one_goodCube_measure d hd).symm

end Exploding
