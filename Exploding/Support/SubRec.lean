/-
The recurrence of the constant background `d` (Proposition 7.3 of
`paper/exploding.tex`).

`recOdo d V` is the `Vᶜ`-frozen odometer of the recurrence argument: background
`d`, initial odometer the indicator of the outer boundary `∂V`.  The paper's
`RecurrentOn η V` says that `recOdo d V t` equals `1` on `V` from `t = |V|` on.

The proof is the paper's, made direct: a site of `V` topples exactly when it has
at least `d` toppled neighbours, and a site of `V` that is not yet toppled and
maximizes the coordinate sum has all of `x + e_i` toppled (each is either
toppled in `V` or lies in `∂V`, which is toppled from the start).  So at every
step before `V` is full at least one new site topples, and `|V|` steps suffice.
-/
import Exploding.Support.SubFodo

namespace Exploding

open LatticeProb
open scoped Classical

variable {d : ℕ}

/-- The `Vᶜ`-frozen odometer of the recurrence argument: background `d`, initial
odometer the indicator of `∂V`. -/
noncomputable def recOdo (d : ℕ) (V : Finset (Site d)) : ℕ → Site d → ℤ :=
  fodo ((↑V : Set (Site d))ᶜ) (fun _ => (d : ℤ))
    (fun y => if y ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0)

@[simp] theorem recOdo_zero (d : ℕ) (V : Finset (Site d)) (x : Site d) :
    recOdo d V 0 x = if x ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0 := rfl

theorem recOdo_succ (d : ℕ) (V : Finset (Site d)) (t : ℕ) (x : Site d) :
    recOdo d V (t + 1) x =
      if x ∈ (↑V : Set (Site d))ᶜ then
        (if x ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0)
      else recOdo d V t x +
        (if 2 * (d : ℤ) ≤ (d : ℤ) + lap (recOdo d V t) x then 1 else 0) := by
  rw [recOdo, fodo_succ]
  by_cases hx : x ∈ (↑V : Set (Site d))ᶜ
  · rw [if_pos hx, if_pos hx]
  · rw [if_neg hx, if_neg hx]
    congr 1

/-- Off `V` the recurrence odometer never moves. -/
theorem recOdo_of_notMem (d : ℕ) (V : Finset (Site d)) (t : ℕ) {x : Site d}
    (hx : x ∉ V) :
    recOdo d V t x = if x ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0 :=
  fodo_of_mem _ _ _ _ (by simpa using hx)

/-- On `V` the recurrence odometer starts at `0`. -/
theorem recOdo_zero_of_mem (d : ℕ) (V : Finset (Site d)) {x : Site d} (hx : x ∈ V) :
    recOdo d V 0 x = 0 := by
  rw [recOdo_zero, if_neg (fun h => h.1 hx)]

/-- The recurrence odometer is nonnegative. -/
theorem recOdo_nonneg (d : ℕ) (V : Finset (Site d)) (t : ℕ) (x : Site d) :
    0 ≤ recOdo d V t x :=
  Exploding.fodo_nonneg _ _ _ (fun y => by
    by_cases hy : y ∈ outerBoundary (↑V : Set (Site d)) <;> simp [hy]) t x

/-- The recurrence odometer is nondecreasing in time. -/
theorem recOdo_mono (d : ℕ) (V : Finset (Site d)) (t : ℕ) (x : Site d) :
    recOdo d V t x ≤ recOdo d V (t + 1) x := by
  rw [recOdo_succ]
  by_cases hx : x ∈ (↑V : Set (Site d))ᶜ
  · rw [if_pos hx, recOdo_of_notMem d V t (by simpa using hx)]
  · rw [if_neg hx]
    split_ifs <;> omega

end Exploding
