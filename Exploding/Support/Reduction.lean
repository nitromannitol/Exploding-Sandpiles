/-
The constrained frozen toppling processes of Section 7.1 of
`paper/exploding.tex`, in which the dynamics on the face `x_1 = 1` of a cube in
`ℤ^{d+1}` are compared with `d`-dimensional dynamics on a cube in `ℤ^d`.

A site of `ℤ^{d+1}` is written `cons a y = (a, 𝐲)` with `a ∈ ℤ` and `𝐲 ∈ ℤ^d`.
The initial conditions are `(7.3)` and the updates `(7.4)`, `(7.5)`; the
sandpiles are `s_t = s_0 + Δ(u_t - u_0)` as in the unconstrained case.
-/
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The site `(a, 𝐲)` of `ℤ^{d+1}`. -/
def cons (a : ℤ) (y : Site d) : Site (d + 1) := Fin.cons a y

open scoped Classical in
/-- The `(d+1)`-dimensional constrained frozen odometer `u_t^{(d)}` of `(7.4)`,
started from `u_0 = 1{x_1 = 0}`. -/
noncomputable def redOdoUp (n : ℕ) (η : Site (d + 1) → ℤ) : ℕ → Site (d + 1) → ℤ
  | 0 => fun x => if x 0 = 0 then 1 else 0
  | t + 1 => fun x =>
      if x ∉ cube (d + 1) n then redOdoUp n η t x
      else if 1 < x 0 then redOdoUp n η t x
      else if redOdoUp n η t x = 1 then redOdoUp n η t x
      else redOdoUp n η t x +
        (if 2 * ((d : ℤ) + 1) ≤ η x + lap (redOdoUp n η t) x then 1 else 0)

/-- The `(d+1)`-dimensional constrained sandpile `s_t^{(d)}`. -/
noncomputable def redConfUp (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (x : Site (d + 1)) : ℤ :=
  η x + lap (redOdoUp n η t) x

open scoped Classical in
/-- The `d`-dimensional constrained frozen odometer `u_t^{(d-1)}` of `(7.5)`,
on the background `η^{(d-1)}(𝐲) = η(1, 𝐲) - 1`, started from `u_0 = 0`. -/
noncomputable def redOdoDown (n : ℕ) (η : Site (d + 1) → ℤ) : ℕ → Site d → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun y =>
      if y ∉ cube d n then redOdoDown n η t y
      else if redOdoDown n η t y = 1 then redOdoDown n η t y
      else redOdoDown n η t y +
        (if 2 * (d : ℤ) ≤ (η (cons 1 y) - 1) + lap (redOdoDown n η t) y then 1 else 0)

/-- The `d`-dimensional constrained sandpile `s_t^{(d-1)}`. -/
noncomputable def redConfDown (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) : ℤ :=
  (η (cons 1 y) - 1) + lap (redOdoDown n η t) y

end Exploding
