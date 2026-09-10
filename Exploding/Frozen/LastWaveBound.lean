/-
Lemma 3.3 of the paper: the last wave exceeds the penultimate wave by at most
one.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb

/-- **Lemma 3.3** (`exploding.tex:728-733`, label `lemma:last_wave_bound`).

"The last wave started at `z` is bounded by one outside the interior of the
penultimate-cluster of `z`.  Moreover, for all `t ≥ 1` and `x, z ∈ ℤ^d`,
`u_t^{(z)}(x) ≤ (1 + ũ^{(z)}(x))`."

The displayed inequality is the content; the sentence before it is the reading
of that inequality off `(3.3)`.  Section 3 fixes `η` as in `(1.2)`, so
`2d - 2 ≤ η ≤ 2d - 1`, and takes the last wave to be well defined, which is
Lemma 3.2: some `n ≥ 1` has a non-stabilizable wave at `z`.  Those are the two
hypotheses carried. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.last_wave_bound (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z)
    (t : ℕ) (ht : 1 ≤ t) (x : Site d) :
    lastWave η z t x ≤ 1 + penultimateWave η z x
-- FROZEN-STATEMENT-END
:= by sorry
