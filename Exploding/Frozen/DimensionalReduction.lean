/-
Proposition 7.2 of the paper: the dynamics on a face of a cube in `ℤ^{d+1}`
reduce to `d`-dimensional dynamics, with the tangential external values chosen
pointwise.  The paper prescribes these values as `u_0^{(d-1)}(𝐲) = u_0^{(d)}(1,𝐲) ∈ {0,1}` on the
outer boundary of `Q_n^{(d-1)}`; the function `beta` supplies them pointwise.  The odometers and
configurations are the literal definitions of `Exploding.Support.ReductionBoundary`.
-/
import Exploding.Support.ReductionBoundary

open Exploding LatticeProb

/-- **Proposition 7.2** (`paper/corrected-arxiv/exploding-corrected-arxiv.tex:2059-2068`, label `prop:dimensional_reduction`), with the
paper's `d` written `d + 1`, so that the lower-dimensional lattice is `ℤ^d`; `(1, 𝐱)` is
`cons 1 y` and `F_1(Q_n^{(d)})` is the internal face `faceLow (d + 1) n 0`.  The tangential
external values are the Boolean function `beta`, evaluated at each outer boundary site.

"For all `t ≥ 0` and `(1, 𝐱_{d-1}) ∈ F_1(Q_n^{(d)})`,
`u_t^{(d)}(1, 𝐱_{d-1}) = u_t^{(d-1)}(𝐱_{d-1})` and
`s_t^{(d)}(1, 𝐱_{d-1}) = s_t^{(d-1)}(𝐱_{d-1}) + 2` if `u_t^{(d)}(1, 𝐱_{d-1}) = 0`." -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.dimensional_reduction (d n : ℕ) (hd : 1 ≤ d) (beta : Site d → Bool)
    (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) (hy : cons 1 y ∈ faceLow (d + 1) n 0) :
    bUpOdo beta n η t (cons 1 y) = bLowOdo beta n η t y ∧
      (bUpOdo beta n η t (cons 1 y) = 0 →
        bUpConf beta n η t (cons 1 y) = bLowConf beta n η t y + 2)
-- FROZEN-STATEMENT-END
:= by
  exact bOdo_dimensional_reduction beta n hd η t y ((mem_cube_cons_one hd y).mp hy.1)
