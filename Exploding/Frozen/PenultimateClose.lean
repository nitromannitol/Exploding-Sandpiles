/-
Lemma 3.7 of the paper: the last-wave and penultimate-cluster arrival times are
polylogarithmically close.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb MeasureTheory

/-- **Lemma 3.7** (`exploding.tex:830-835`, label
`lemma:last_penultimate_close`).

"There exists a constant `γ > 0` so that on an event of probability 1, for all
`n` sufficiently large and `|x| ≤ n`, `T̂(x) ≤ T̃(x) ≤ T̂(x) + (log n)^γ`."

Both arrival times are taken in `ℕ∞`.  The first inequality is stated there;
the second is stated through natural numbers equal to them, which also records
that both are finite. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.last_penultimate_close (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
          ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
            clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ
-- FROZEN-STATEMENT-END
:= by sorry
