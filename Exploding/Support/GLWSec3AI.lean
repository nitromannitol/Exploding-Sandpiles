/-
Proposition 5.1 of the paper (generalized last wave): the local bound from the origin
(`eq:generalized_lipschitz`), proved from Hypotheses 1, 3 and 4 and the cited percolation
results.
-/
import Exploding.Support.GLWSec3AC
import Exploding.Support.GLWSec3AH

open Exploding LatticeProb MeasureTheory

namespace Exploding

/-- **The paper's local bound measured from the origin** (`eq:generalized_lipschitz`):
`T̃(x) ≤ C |x| + (log n)^γ` and `T̃(x') ≤ T̃(x) + C |x - x'| + (log n)^γ` on `[-n,n]^d` for `n` large,
almost surely, with the last wave from the origin not stabilizing at any site. -/
theorem glws_origin (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (P : Measure (Site d → ℤ)) : glws_Origin d ηmin P :=
  glws_origin_of_renorm d hd ηmin hηmin P (glws_renorm d P)

end Exploding
