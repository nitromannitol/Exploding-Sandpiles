/-
Lemma 3.5 of the paper: penultimate clusters are polylogarithmically small.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb MeasureTheory

/-- **Lemma 3.5** (`exploding.tex:790-796`, label
`lemma:last_penultimate_cluster`).

"There is a constant `γ > 0` so that for all `n` sufficiently large and
`|x| ≤ n`, `P(x) ⊂ x + [-(log n)^γ, (log n)^γ]^d`."

`γ` is deterministic, so it is bound before `η`; "for all `n` sufficiently
large" is a threshold that may depend on `η`, so it is bound inside.  `|x|` is
the Manhattan norm. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.last_penultimate_cluster (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∀ y ∈ penultimateCluster η x, ∀ i, ((|y i - x i| : ℤ) : ℝ) ≤ Real.log n ^ γ
-- FROZEN-STATEMENT-END
:= by sorry
