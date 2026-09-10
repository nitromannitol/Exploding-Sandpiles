/-
Lemma 2.3 of the paper: a path of topplings fills its bounding rectangle.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb
/-- **Lemma 2.3** (`exploding.tex:531-535`, label `lemma:local_convexity`).

"Let `A := {z^(i)}` be a finite path `z^(i) ∼ z^(i+1)`.  Let `w_t` denote
`A`-frozen parallel toppling with initial conditions `w_0|_A = 1`, `s_0' = η`.
Then, `w_t|_{br(A)} = 1`, for all `t ≥ |br(A)|`."

The path is given by its vertices `z 0, …, z m`, consecutive ones adjacent, and
`A` is their image.  Section 2 fixes `η` as in `(1.2)`, so `2d - 2 ≤ η ≤ 2d - 1`.
`w_0 = 1{x ∈ A}` is `Set.indicator A 1`.
`|br(A)|` is the cardinality of the bounding rectangle, whose finiteness is
carried explicitly rather than read through `Set.ncard = 0`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.local_convexity (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (m : ℕ) (z : ℕ → Site d) (hpath : ∀ i : ℕ, i < m → (lattice d).Adj (z i) (z (i + 1)))
    (A : Set (Site d)) (hA : A = z '' {i : ℕ | i ≤ m})
    (hfin : (br A).Finite) (t : ℕ) (ht : hfin.toFinset.card ≤ t)
    (x : Site d) (hx : x ∈ br A) :
    fodo A η (Set.indicator A 1) t x = 1
-- FROZEN-STATEMENT-END
:= by sorry
