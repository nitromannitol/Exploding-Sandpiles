/-
Theorem 1.4 of the paper: a product background with at least `d` chips
everywhere and a positive density of sites with `2d - 1` chips is explosive.
-/
import Exploding.Support.Vocab
import Exploding.External.Schonmann
import Exploding.Support.TEProofRec
import Exploding.Support.TEProofLaw
import Exploding.Support.TEProofBlock
import Exploding.Frozen.Recurrence
import Exploding.Frozen.BoxCrossing
import Exploding.Frozen.ExplosionCriteria

open Exploding LatticeProb MeasureTheory

/-- **Theorem 1.4** (`exploding.tex:265-268`, label `theorem:explosive`).

"Suppose `β : ℤ^d → ℤ` is drawn from a product measure `P`.  If `β ≥ d` and
`P(β(0) = (2d - 1)) > 0`, then `β` is explosive with probability 1."

`P` is the product measure with one-site law `ν`; `β ≥ d` is the statement that
`ν` gives full mass to `{m : d ≤ m}`, which is what "`β ≥ d`" asserts for a
product measure.

Schonmann's bound, Proposition 7.4 of the paper, used through Proposition 7.5,
enters as the explicit hypothesis `hSch`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.explosive (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)})
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => ν), Explosive β
-- FROZEN-STATEMENT-END
:= by
  haveI : IsProbabilityMeasure ν := hν
  have hd1 : 1 ≤ d := by omega
  rcases eq_zero_or_pos (ν {m : ℤ | 2 * (d : ℤ) ≤ m}) with hq | hq
  · -- no site holds `2d` chips or more: the law is supported in `[d, 2d - 1]`
    have hupper : ν {m : ℤ | m ≤ 2 * (d : ℤ) - 1} = 1 := by
      have hc : {m : ℤ | m ≤ 2 * (d : ℤ) - 1} = {m : ℤ | 2 * (d : ℤ) ≤ m}ᶜ := by
        ext m; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]; omega
      have hm : MeasurableSet {m : ℤ | 2 * (d : ℤ) ≤ m} := measurableSet_Ici
      rw [hc, measure_compl hm (measure_ne_top _ _), hq]
      simp
    have hP : IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν) := inferInstance
    have hsupp : ∀ᵐ η ∂(Measure.infinitePi fun _ : Site d => ν), InOmega d (d : ℤ) η := by
      filter_upwards [te_ae_prod d ν hν (fun m : ℤ => (d : ℤ) ≤ m) measurableSet_Ici hlow,
        te_ae_prod d ν hν (fun m : ℤ => m ≤ 2 * (d : ℤ) - 1) measurableSet_Iic hupper] with
        η h1 h2 x
      exact ⟨h1 x, h2 x⟩
    exact Exploding.Frozen.explosion_criteria d hd (d : ℤ) (Int.natCast_nonneg d)
      (⊤ : AddSubgroup (Site d)) (by rw [AddSubgroup.index_top]; norm_num)
      (Measure.infinitePi fun _ : Site d => ν) hP hsupp (te_stationary d ν hν)
      (te_ergodic d hd1 ν hν) (te_finite_range d ν hν)
      (Exploding.Frozen.box_crossing d hd ν hν hlow hhit hSch)
      (te_recurrent_law d (Exploding.Frozen.recurrence d hd1) ν hν hlow hupper)
  · -- a positive proportion of sites hold `2d` chips or more: arbitrarily large blocks of
    -- unstable sites force non-stabilizability
    exact te_explosive_of_blocks d hd1 ν hν hq
