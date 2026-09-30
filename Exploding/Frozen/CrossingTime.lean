/-
Proposition 2.1 of the paper: a large box is crossed quickly with high
probability.
-/
import Exploding.Support.Vocab
import Exploding.Support.CrossingTimeAux

open Exploding LatticeProb MeasureTheory

/-- **Proposition 2.1** (`exploding.tex:416-422`, label `prop:crossing_time`).

"For every `δ > 0`, there is a `k` so that `max_{i,z} 𝔠_k^{(i,z)} ≤ k^d` with
probability at least `(1 - δ)`."

`𝔠_k^{(i,z)}` is `Exploding.crossingTime`, taken in `ℕ∞` so that the paper's
value `∞` is `⊤`; the maximum over `i` and `z ∈ Q̄_k` being at most `k^d` is
`Exploding.GoodCube η k`.  The probability is the law `(1.2)`, and the bound is
written in `ℝ≥0∞` so that no real-valued `toReal` of `⊤` is read. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.crossing_time (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧ ENNReal.ofReal (1 - δ) ≤ toyLaw d p {η | GoodCube η k}
-- FROZEN-STATEMENT-END
:= by
  exact aux_ct_assemble d hd p hp hp1 δ hδ
