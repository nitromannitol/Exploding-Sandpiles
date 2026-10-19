/-
Proposition 1.4 of Fey, Levine and Peres, quoted as Theorem 1.1 of the paper.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb MeasureTheory

/-- **Theorem 1.1** of the paper (`exploding.tex:238-240`, label
`prop:fey_levine_peres_explode`), which the paper attributes to Proposition 1.4
of A. Fey, L. Levine and Y. Peres, *Growth rates and explosions in sandpiles*,
J. Stat. Phys. 138 (2010).

"Let `η` be as in (1.2).  If `p > 0`, `η` is explosive with probability 1."

The paper cites this rather than proving it, so it enters as an explicit
hypothesis; Theorem 1.4 of the paper strengthens it. -/
-- FROZEN-STATEMENT-BEGIN
def Exploding.External.FeyLevinePeresExplosive : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ᵐ η ∂(toyLaw d p), Explosive η
-- FROZEN-STATEMENT-END
