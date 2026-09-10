/-
Proposition 7.2 of the paper: the dynamics on a face of a cube in `ℤ^{d+1}`
reduce to `d`-dimensional dynamics.
-/
import Exploding.Support.Reduction

open Exploding LatticeProb

-- The face membership is part of the statement but not needed: the identity
-- holds at every `(1, y)`, because both processes are frozen off their cubes and
-- `cons 1 y` lies in `Q_n^{(d+1)}` exactly when `y` lies in `Q_n^{(d)}`.
set_option linter.unusedVariables false in
/-- **Proposition 7.2** (`exploding.tex:1869-1878`, label
`prop:dimensional_reduction`).

"For all `t ≥ 0` and `(1, 𝐱_{d-1}) ∈ F_1(Q_n^{(d)})`,
`u_t^{(d)}(1, 𝐱_{d-1}) = u_t^{(d-1)}(𝐱_{d-1})` and
`s_t^{(d)}(1, 𝐱_{d-1}) = s_t^{(d-1)}(𝐱_{d-1}) + 2` if `u_t^{(d)}(1,𝐱_{d-1}) = 0`."

The paper's `d` is written `d + 1` here, so that the lower-dimensional lattice
is `ℤ^d`; `(1, 𝐱)` is `cons 1 y` and `F_1(Q_n^{(d)})` is the internal face
`faceLow (d+1) n 0`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.dimensional_reduction (d n : ℕ) (hd : 1 ≤ d) (η : Site (d + 1) → ℤ)
    (t : ℕ) (y : Site d) (hy : cons 1 y ∈ faceLow (d + 1) n 0) :
    redOdoUp n η t (cons 1 y) = redOdoDown n η t y ∧
      (redOdoUp n η t (cons 1 y) = 0 →
        redConfUp n η t (cons 1 y) = redConfDown n η t y + 2)
-- FROZEN-STATEMENT-END
:= by
  refine ⟨redOdo_agree hd t y, fun h0 => ?_⟩
  have hlap := lap_redOdoUp_cons_one (n := n) (η := η) t y
  have hlapv : lap (fun w => redOdoUp n η t (cons 1 w)) y = lap (redOdoDown n η t) y := by
    simp only [lap]
    rw [nbrSumZ_congr (fun w => redOdo_agree hd t w) y, redOdo_agree hd t y]
  rw [hlapv, h0] at hlap
  simp only [redConfUp, redConfDown, hlap]
  ring
