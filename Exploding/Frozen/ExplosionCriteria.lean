/-
Proposition 7.1 of the paper: a criterion for a background law to be explosive.
-/
import Exploding.Support.Hypotheses
import Exploding.Support.ECProofMain
import Exploding.Support.RecurrenceNonneg

open Exploding LatticeProb MeasureTheory

/-- **Proposition 7.1** (`paper/corrected-arxiv/exploding-corrected-arxiv.tex:1956-1958`, label `prop:explosion_criteria`), in the bounded-background setting of
Section 5 (`sec:generalization`) with `d ≥ 2`.

"Let `d ≥ 2`. If Hypotheses `hyp:finite_range_of_dependence` and `hyp:box_crossing` are
satisfied and `P` is recurrent then `P` is explosive."

Almost surely `η_min ≤ η ≤ 2d - 1` (`hsupp`) for an integer `η_min`, and `P` is stationary
and measurably ergodic with respect to a sublattice `L`, a finite-index subgroup of `ℤ^d`.
The lower bound `0 ≤ η` is not assumed: recurrence (`recurrent_nonneg`, from the singleton
`{x}`) gives it almost surely, so the proof uses only the upper bound of `hsupp`. The `herg`
binder tests measurable events of the ambient product space; identifying it with ergodicity
on the paper's `(Ω, F)` under `hsupp` is a separate step. The premises `hL`, `hstat` and `herg`
belong to the setting of Section 5 and are not used by the proof for `d ≥ 2`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.explosion_criteria (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : MeasurableErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h2 : BoxCrossingHyp d P)
    (hrec : RecurrentLaw d P) :
    ExplosiveLaw d P
-- FROZEN-STATEMENT-END
:= by
  have _unused := And.intro hL (And.intro hstat herg)
  have hrec' : ∀ᵐ η ∂P, Recurrent η := hrec
  have hlow : ∀ᵐ η ∂P, ∀ x, 0 ≤ η x := by
    filter_upwards [hrec'] with η hη x
    exact recurrent_nonneg η hη x
  have hsupp' : ∀ᵐ η ∂P, ∀ x, 0 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
    filter_upwards [hlow, hsupp] with η hl hη x
    exact ⟨hl x, (hη x).2⟩
  exact ec_explosive_ae hd P hP hsupp' h1 h2
