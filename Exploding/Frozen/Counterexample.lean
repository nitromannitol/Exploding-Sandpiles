import Exploding.Frozen.CounterexampleArrival
import Exploding.Frozen.CounterexampleSupport
import Exploding.Support.ArxivCounterexampleExact

open Exploding LatticeProb MeasureTheory Filter
open scoped Topology

/-- **Theorem 6.1** (`paper/corrected-arxiv/exploding-corrected-arxiv.tex:1471-1481`, label `theorem:counterexample`); its same-background measurable-volume
obstruction is at the end of the proof in `sec:proof_of_generalization`. The witness has finite
axial arrivals, both stated axial limits, and no measurable symmetric-difference-volume limit. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.counterexample (d : ℕ) (hd : 2 ≤ d) :
    ∃ η : Site d → ℤ, ∃ hη : Explosive η,
      (¬ ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x) ∧
      (∀ n : ℕ, counterexampleArrival η hη ((n : ℤ) • e1 d) ≠ ⊤) ∧
      3 / 2 ≤ limsup
        (fun n : ℕ =>
          ((counterexampleArrival η hη ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ))
        atTop ∧
      liminf
        (fun n : ℕ =>
          ((counterexampleArrival η hη ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ))
        atTop = 1 ∧
      ¬ ∃ B : Set (Fin d → ℝ),
        MeasurableSet B ∧
        Tendsto
          (fun t : ℕ => volume (symmDiff (counterexampleSupport η hη t) B))
          atTop (nhds 0)
-- FROZEN-STATEMENT-END
:= by
  exact Exploding.ce_counterexample_complete d hd
