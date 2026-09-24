/-
Theorem 2.8 of Fey, Meester and Redig, the least action principle for legal
toppling procedures in infinite volume, quoted in the proof of Theorem 6.1 of
the paper.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb

namespace Exploding.External

/-- `u` is a legal toppling procedure in discrete time for the configuration
`s0`: it starts at `0`, and at each step every site topples at most once, and
only if it holds at least `2d` chips in the configuration `s0 + Δ u` reached so
far. -/
def IsLegalToppling {d : ℕ} (s0 : Site d → ℤ) (u : ℕ → Site d → ℤ) : Prop :=
  u 0 = 0 ∧ ∀ (k : ℕ) (x : Site d),
    u (k + 1) x = u k x ∨ (u (k + 1) x = u k x + 1 ∧ 2 * (d : ℤ) ≤ s0 x + lap (u k) x)

end Exploding.External

/-- **Theorem 2.8** of A. Fey, R. Meester and F. Redig, *Stabilizability and
percolation in the infinite volume sandpile model*, Ann. Probab. 37 (2009),
cited at `exploding.tex:1415-1424` in the proof of Theorem 6.1 (label
`theorem:counterexample`).

The source: let `T`, `T'` be legal toppling procedures that are finite for `η`.
If `T` is stabilizing for `η`, then `T'(∞, x) ≤ T(∞, x)` for every `x`
(Statement 1); for stabilizable `η` there is no legal toppling procedure that is
not finite (Statement 3).

Stated for procedures in discrete time, which satisfy the conditions of
Definition 2.1 of the source, and for configurations with nonnegative heights,
the state space of the source.  `v` is stabilizing with final odometer `w`:
every site's count is eventually `w x`, and `s0 + Δ w` is stable.  Applying
Statement 1 to the procedure `u` stopped at step `k`, as in the proof of
Statement 3, gives `u k ≤ w`.  The paper cites the result rather than proving
it, so it enters as an explicit hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
def Exploding.External.FeyMeesterRedigLeastAction : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ s0 : Site d → ℤ, (∀ x, 0 ≤ s0 x) →
    ∀ u v : ℕ → Site d → ℤ,
      Exploding.External.IsLegalToppling s0 u → Exploding.External.IsLegalToppling s0 v →
      ∀ w : Site d → ℤ, (∀ x, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → v k x = w x) →
        (∀ x, s0 x + lap w x < 2 * (d : ℤ)) →
        ∀ (k : ℕ) (x : Site d), u k x ≤ w x
-- FROZEN-STATEMENT-END
