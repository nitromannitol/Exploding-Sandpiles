/-
Lemma 3.4 of the paper: the penultimate-cluster arrival times are subadditive.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb

/-- **Lemma 3.4** (`exploding.tex:758-763`, label `lemma:approx_subadditivity`).

"The penultimate-cluster arrival times are subadditive: for all `a, b, z ∈ ℤ^d`,
`T̃(a,z) ≤ T̃(a,b) + T̃(b,z)`."

The arrival times are taken in `ℕ∞`, where addition is monotone and `⊤` absorbs,
so the inequality says exactly what the paper's does and never reads a junk
natural number.  Section 3 fixes `η` as in `(1.2)` and takes every last wave to
be well defined, which is Lemma 3.2. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.approx_subadditivity (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y)
    (a b z : Site d) :
    clusterArrival η a z ≤ clusterArrival η a b + clusterArrival η b z
-- FROZEN-STATEMENT-END
:= by sorry
