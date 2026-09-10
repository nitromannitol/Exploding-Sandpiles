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

/-! ### Moving between `ℤ^{d+1}` and `ℤ^d` -/

/-- Translating the tail by a unit vector. -/
theorem cons_add_unit (a : ℤ) (y : Site d) (j : Fin d) :
    cons a (y + unit j) = cons a y + unit j.succ := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [cons, unit, Fin.succ_ne_zero]
  · intro k
    simp [cons, unit, Pi.single_apply, Fin.succ_inj]

/-- Translating the tail by a unit vector, downwards. -/
theorem cons_sub_unit (a : ℤ) (y : Site d) (j : Fin d) :
    cons a (y - unit j) = cons a y - unit j.succ := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [cons, unit, Fin.succ_ne_zero]
  · intro k
    simp [cons, unit, Pi.single_apply, Fin.succ_inj]

/-- Translating the head upwards. -/
theorem cons_add_unit_zero (a : ℤ) (y : Site d) :
    cons a y + unit (0 : Fin (d + 1)) = cons (a + 1) y := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [cons, unit]
  · intro k
    simp [cons, unit]

/-- Translating the head downwards. -/
theorem cons_sub_unit_zero (a : ℤ) (y : Site d) :
    cons a y - unit (0 : Fin (d + 1)) = cons (a - 1) y := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [cons, unit]
  · intro k
    simp [cons, unit]

/-- The neighbour sum at `(a, 𝐲)` splits into the two neighbours in the first
direction and the `d`-dimensional neighbour sum of the slice. -/
theorem nbrSumZ_cons (u : Site (d + 1) → ℤ) (a : ℤ) (y : Site d) :
    nbrSumZ u (cons a y) =
      (u (cons (a + 1) y) + u (cons (a - 1) y)) + nbrSumZ (fun w => u (cons a w)) y := by
  simp only [nbrSumZ, Fin.sum_univ_succ]
  rw [cons_add_unit_zero, cons_sub_unit_zero]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← cons_add_unit, ← cons_sub_unit]


/-! ### The constrained processes -/

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

open scoped Classical in
theorem redOdoUp_succ (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (x : Site (d + 1)) :
    redOdoUp n η (t + 1) x =
      if x ∉ cube (d + 1) n then redOdoUp n η t x
      else if 1 < x 0 then redOdoUp n η t x
      else if redOdoUp n η t x = 1 then redOdoUp n η t x
      else redOdoUp n η t x +
        (if 2 * ((d : ℤ) + 1) ≤ η x + lap (redOdoUp n η t) x then 1 else 0) := rfl

theorem redOdoUp_zero (n : ℕ) (η : Site (d + 1) → ℤ) (x : Site (d + 1)) :
    redOdoUp n η 0 x = if x 0 = 0 then 1 else 0 := rfl

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

open scoped Classical in
theorem redOdoDown_succ (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) :
    redOdoDown n η (t + 1) y =
      if y ∉ cube d n then redOdoDown n η t y
      else if redOdoDown n η t y = 1 then redOdoDown n η t y
      else redOdoDown n η t y +
        (if 2 * (d : ℤ) ≤ (η (cons 1 y) - 1) + lap (redOdoDown n η t) y then 1 else 0) := rfl

theorem redOdoDown_zero (n : ℕ) (η : Site (d + 1) → ℤ) (y : Site d) :
    redOdoDown n η 0 y = 0 := rfl

/-- The `d`-dimensional constrained sandpile `s_t^{(d-1)}`. -/
noncomputable def redConfDown (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) : ℤ :=
  (η (cons 1 y) - 1) + lap (redOdoDown n η t) y

/-! ### The reduction -/

section Reduction

variable {n : ℕ} {η : Site (d + 1) → ℤ}

theorem cons_notMem_cube_of_head (a : ℤ) (y : Site d) (h : a = 0) :
    cons a y ∉ cube (d + 1) n := by
  intro hc
  have := (hc 0).1
  simp [cons, h] at this

theorem redOdoUp_head_zero (t : ℕ) (y : Site d) : redOdoUp n η t (cons 0 y) = 1 := by
  induction t with
  | zero => simp [redOdoUp_zero, cons]
  | succ t ih =>
    rw [redOdoUp_succ]
    rw [if_pos (cons_notMem_cube_of_head 0 y rfl)]
    exact ih

theorem redOdoUp_head_high (t : ℕ) (x : Site (d + 1)) (h : 1 < x 0) :
    redOdoUp n η t x = redOdoUp n η 0 x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [redOdoUp_succ]
    by_cases hc : x ∉ cube (d + 1) n
    · rw [if_pos hc]; exact ih
    · rw [if_neg hc, if_pos h]; exact ih

theorem redOdoUp_cons_high (t : ℕ) (y : Site d) (a : ℤ) (ha : 1 < a) :
    redOdoUp n η t (cons a y) = 0 := by
  have h : (1 : ℤ) < (cons a y) 0 := by simpa [cons] using ha
  rw [redOdoUp_head_high t _ h]
  have hne : ((cons a y) 0) ≠ 0 := by simp only [cons, Fin.cons_zero]; omega
  simp [redOdoUp_zero, hne]

theorem mem_cube_cons_one (hd : 1 ≤ d) (y : Site d) :
    cons (1 : ℤ) y ∈ cube (d + 1) n ↔ y ∈ cube d n := by
  constructor
  · intro hc j
    have := hc j.succ
    simpa [cons] using this
  · intro hy i
    refine Fin.cases ?_ ?_ i
    · refine ⟨by simp [cons], ?_⟩
      have h0 := hy ⟨0, by omega⟩
      simp only [cons, Fin.cons_zero]
      omega
    · intro k; simpa [cons] using hy k

theorem redOdoDown_zero_or_one (t : ℕ) (y : Site d) :
    redOdoDown n η t y = 0 ∨ redOdoDown n η t y = 1 := by
  induction t generalizing y with
  | zero => left; rfl
  | succ t ih =>
    rw [redOdoDown_succ]
    by_cases hy : y ∉ cube d n
    · rw [if_pos hy]; exact ih y
    · rw [if_neg hy]
      by_cases h1 : redOdoDown n η t y = 1
      · rw [if_pos h1]; right; exact h1
      · rw [if_neg h1]
        have h0 : redOdoDown n η t y = 0 := (ih y).resolve_right h1
        rw [h0]
        by_cases hc : 2 * (d : ℤ) ≤ (η (cons 1 y) - 1) + lap (redOdoDown n η t) y
        · rw [if_pos hc]; right; ring
        · rw [if_neg hc]; left; ring

theorem lap_redOdoUp_cons_one (t : ℕ) (y : Site d) :
    lap (redOdoUp n η t) (cons 1 y) =
      1 + lap (fun w => redOdoUp n η t (cons 1 w)) y
        - 2 * redOdoUp n η t (cons 1 y) := by
  simp only [lap, nbrSumZ_cons]
  norm_num
  rw [redOdoUp_cons_high t y 2 (by norm_num), redOdoUp_head_zero t y]
  push_cast
  ring

theorem redOdo_agree (hd : 1 ≤ d) (t : ℕ) (y : Site d) :
    redOdoUp n η t (cons 1 y) = redOdoDown n η t y := by
  induction t generalizing y with
  | zero => simp [redOdoUp_zero, redOdoDown_zero, cons]
  | succ t ih =>
    rw [redOdoUp_succ, redOdoDown_succ]
    have hmem : (cons (1 : ℤ) y ∉ cube (d + 1) n) ↔ (y ∉ cube d n) := by
      simp [mem_cube_cons_one hd y]
    by_cases hy : y ∉ cube d n
    · rw [if_pos (hmem.mpr hy), if_pos hy]; exact ih y
    · rw [if_neg (fun hcon => hy (hmem.mp hcon)), if_neg hy]
      have hhead : ¬ (1 : ℤ) < (cons (1 : ℤ) y) 0 := by simp [cons]
      rw [if_neg hhead]
      by_cases h1 : redOdoDown n η t y = 1
      · rw [if_pos (by rw [ih y]; exact h1), if_pos h1]; exact ih y
      · rw [if_neg (by rw [ih y]; exact h1), if_neg h1]
        have h0 : redOdoDown n η t y = 0 := (redOdoDown_zero_or_one t y).resolve_right h1
        have hup0 : redOdoUp n η t (cons 1 y) = 0 := by rw [ih y]; exact h0
        have hlapv : lap (fun w => redOdoUp n η t (cons 1 w)) y
            = lap (redOdoDown n η t) y := by
          simp only [lap]
          rw [nbrSumZ_congr (fun w => ih w) y, ih y]
        have hlap := lap_redOdoUp_cons_one (n := n) (η := η) t y
        rw [hlapv, hup0] at hlap
        have hiff : (2 * ((d : ℤ) + 1) ≤ η (cons 1 y) + lap (redOdoUp n η t) (cons 1 y))
            ↔ (2 * (d : ℤ) ≤ (η (cons 1 y) - 1) + lap (redOdoDown n η t) y) := by
          rw [hlap]; constructor <;> intro h <;> linarith
        rw [ih y]
        by_cases hc : 2 * (d : ℤ) ≤ (η (cons 1 y) - 1) + lap (redOdoDown n η t) y
        · rw [if_pos (hiff.mpr hc), if_pos hc]
        · rw [if_neg (fun hcon => hc (hiff.mp hcon)), if_neg hc]

end Reduction

end Exploding
