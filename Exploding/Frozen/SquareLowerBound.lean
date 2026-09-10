/-
Lemma 3.1 of the paper: a wave of order `n^d` covers the box of radius `n`.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb

/-- **Lemma 3.1** (`exploding.tex:705-707`, label `lemma:square_lower_bound`).

"There is a constant `C := C_d` so that for all `n ≥ 1`, the support of the
`(C n^d)`-wave contains `[-n,n]^d`."

The support of a wave is the set of sites its odometer is ever positive at.
`C` depends only on the dimension, so it is bound before the background and
before `n`.  Section 3 fixes `η` as in `(1.2)`, so `2d - 2 ≤ η ≤ 2d - 1`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.square_lower_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℕ, 0 < C ∧ ∀ η : Site d → ℤ, (∀ x, 2 * (d : ℤ) - 2 ≤ η x) →
      (∀ x, η x ≤ 2 * (d : ℤ) - 1) → ∀ n : ℕ, 1 ≤ n → ∀ x ∈ cent d n,
        ∃ t : ℕ, 0 < wave η (C * n ^ d) (0 : Site d) t x
-- FROZEN-STATEMENT-END
:= by sorry
