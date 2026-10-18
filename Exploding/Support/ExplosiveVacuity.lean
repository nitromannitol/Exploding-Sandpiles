import Exploding.Frozen.Explosive
import Exploding.Support.AllHighPodoFront
import Exploding.Support.ExtSchFinal

/-!
# Theorem 1.4 at the all-high endpoint

At dimension `d ≥ 2` the one-site law `δ_{2d-1}` has full mass on `{m ≥ d}` and positive mass at
`2d - 1`, so the public consumer `Exploding.Frozen.explosive` applies to the product of these laws,
with its cited bootstrap input supplied by the in-repository `Exploding.xsr_schonmann`. The product
is the Dirac mass at the all-high configuration. On that background with one origin chip, the
ordinary parallel-toppling odometer is positive at `(t, x)` exactly when `mnorm x < t`. The three
clauses are stated in one theorem, so the probability space, the consumer, and the odometer front
refer to the same background. The theorem assumes nothing beyond the hypotheses of the cited
theorem, and it adds no external input.
-/

namespace Exploding

open LatticeProb MeasureTheory

/-- For `d ≥ 2`, the product of one-site Dirac masses at `2d - 1` is the Dirac mass at the
all-high configuration; this product law is almost surely explosive by `Exploding.Frozen.explosive`;
and the ordinary odometer of the all-high background with one origin chip is positive at time `t`
and site `x` exactly when `mnorm x < t`. -/
theorem explosive_all_high_nonvacuity (d : ℕ) (hd : 2 ≤ d) :
    (Measure.infinitePi fun _ : Site d => Measure.dirac (2 * (d : ℤ) - 1)) =
        Measure.dirac (fun _ : Site d => 2 * (d : ℤ) - 1) ∧
      (∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => Measure.dirac (2 * (d : ℤ) - 1)),
        Explosive β) ∧
      ∀ (t : ℕ) (x : Site d),
        (0 < podo (fun y : Site d => 2 * (d : ℤ) - 1 + dirac (0 : Site d) y) t x ↔
          mnorm x < (t : ℤ)) := by
  have hlow : Measure.dirac (2 * (d : ℤ) - 1) {m : ℤ | (d : ℤ) ≤ m} = 1 :=
    Measure.dirac_apply_of_mem (by show (d : ℤ) ≤ 2 * (d : ℤ) - 1; omega)
  have hhit : 0 < Measure.dirac (2 * (d : ℤ) - 1) {2 * (d : ℤ) - 1} := by
    rw [Measure.dirac_apply_of_mem (Set.mem_singleton _)]
    exact zero_lt_one
  exact ⟨Measure.infinitePi_dirac (fun _ : Site d => 2 * (d : ℤ) - 1),
    Exploding.Frozen.explosive d hd (Measure.dirac (2 * (d : ℤ) - 1)) inferInstance hlow hhit
      Exploding.xsr_schonmann,
    fun t x => all_high_podo_pos_iff d t x⟩

end Exploding
