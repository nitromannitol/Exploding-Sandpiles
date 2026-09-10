/-
Theorem 6.1 of the paper: explosive backgrounds without a limit shape.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb Filter

/-- **Theorem 6.1** (`exploding.tex:1330-1340`, label
`theorem:counterexample`).

"For each dimension `d ≥ 2`, there are explosive backgrounds `η ≱ (2d-2)` on
`ℤ^d` which fail to have a limit shape; the first arrival times
`T(n) := min{t > 0 : v_t(n e_1) > 0}` do not converge,
`limsup_n n^{-1} T(n) ≥ 3/2` and `liminf_n n^{-1} T(n) = 1`."

`T(n)` is the arrival time of the exploding sandpile at `n e_1`; its finiteness
at every `n` is asserted, so that reading it as a natural number is not a junk
value.  The `limsup` and `liminf` are of a bounded sequence of reals, so the
two clauses are the paper's. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.counterexample (d : ℕ) (hd : 2 ≤ d) :
    ∃ η : Site d → ℤ,
      Explosive η ∧
      (¬ ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x) ∧
      (∀ n : ℕ, arrival η ((n : ℤ) • e1 d) ≠ ⊤) ∧
      3 / 2 ≤ limsup (fun n : ℕ => ((arrival η ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)) atTop ∧
      liminf (fun n : ℕ => ((arrival η ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)) atTop = 1
-- FROZEN-STATEMENT-END
:= by sorry
