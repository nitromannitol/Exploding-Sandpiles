/-
The dimensional reduction of Section 7 on the face `F_1(Q_n^{(d+1)})`, with the
tangential external odometers of the corrected source
`paper/corrected-arxiv/exploding-corrected-arxiv.tex` (`prop:dimensional_reduction`).

A site of `ℤ^{d+1}` is written `cons a y = (a, 𝐲)`.  The lower constrained frozen
odometer lives on `ℤ^d` and the upper one on `ℤ^{d+1}`.  The tangential external values
are chosen pointwise: `beta : Site d → Bool` gives the value `bVal (beta y) ∈ {0,1}` at each
outer boundary site `y ∈ ∂Q_n^{(d)}`, and both odometers take that value there.  Their initial
data are

* lower: `bVal (beta y)` on the outer boundary `∂Q_n^{(d)}`, zero elsewhere;
* upper: `1` on `cons 0 y` for `y ∈ Q_n^{(d)}`, `bVal (beta y)` on `cons 1 y` for
  `y ∈ ∂Q_n^{(d)}`, zero elsewhere.

The updates are the frozen-and-capped updates of the corrected source, and the
configurations are `η + Δu` with `η^{(d-1)}(y) = η(1,y) - 1` on the lower side.

`Exploding.Support.Reduction` proves the zero-boundary case with the normal-face
initial value one on all of `ℤ^d`; here that value is restricted to the cube, as in
the corrected source.  The bridge at the end shows that the two odometers agree at
every face site when `beta = fun _ => false`, so the finite normal-face choice is harmless for
that consumer.
-/
import Exploding.Support.Reduction

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### The tangential value and the initial odometers -/

/-- The tangential external value `b ∈ {0,1}` as an integer. -/
def bVal (b : Bool) : ℤ := if b then 1 else 0

theorem bVal_zero_or_one (b : Bool) : bVal b = 0 ∨ bVal b = 1 := by
  cases b <;> simp [bVal]

theorem bVal_false : bVal false = 0 := by simp [bVal]

theorem bVal_true : bVal true = 1 := by simp [bVal]

open scoped Classical in
/-- The lower initial odometer `u_0^{(d-1)}`: `bVal (beta y)` on the outer boundary of
`Q_n^{(d)}`, zero elsewhere. -/
noncomputable def bLowInit (beta : Site d → Bool) (n : ℕ) (y : Site d) : ℤ :=
  if y ∈ outerBoundary (cube d n) then bVal (beta y) else 0

open scoped Classical in
/-- The upper initial odometer `u_0^{(d)}` on `ℤ^{d+1}`: `1` on `cons 0 y` for
`y ∈ Q_n^{(d)}`, `bVal (beta y)` on `cons 1 y` for `y` in the outer boundary of `Q_n^{(d)}`,
and zero elsewhere. -/
noncomputable def bUpInit (beta : Site d → Bool) (n : ℕ) (x : Site (d + 1)) : ℤ :=
  if x 0 = 0 ∧ (Fin.tail x : Site d) ∈ cube d n then 1
  else if x 0 = 1 ∧ (Fin.tail x : Site d) ∈ outerBoundary (cube d n) then
    bVal (beta (Fin.tail x : Site d))
  else 0

/-! ### Characterizations of the initial data -/

section Initial

variable {n : ℕ}

theorem bUpInit_cons_zero_of_mem (beta : Site d → Bool) {y : Site d} (hy : y ∈ cube d n) :
    bUpInit beta n (cons 0 y) = 1 := by
  simp [bUpInit, cons, hy]

theorem bUpInit_cons_zero_of_notMem (beta : Site d → Bool) {y : Site d} (hy : y ∉ cube d n) :
    bUpInit beta n (cons 0 y) = 0 := by
  simp [bUpInit, cons, hy]

theorem bUpInit_cons_one_of_mem (beta : Site d → Bool) {y : Site d}
    (hy : y ∈ outerBoundary (cube d n)) : bUpInit beta n (cons 1 y) = bVal (beta y) := by
  simp [bUpInit, cons, hy]

theorem bUpInit_cons_one_of_notMem (beta : Site d → Bool) {y : Site d}
    (hy : y ∉ outerBoundary (cube d n)) : bUpInit beta n (cons 1 y) = 0 := by
  simp [bUpInit, cons, hy]

theorem bUpInit_cons_of_ne (beta : Site d → Bool) (a : ℤ) (y : Site d) (h0 : a ≠ 0)
    (h1 : a ≠ 1) : bUpInit beta n (cons a y) = 0 := by
  simp [bUpInit, cons, h0, h1]

theorem bLowInit_of_mem (beta : Site d → Bool) {y : Site d}
    (hy : y ∈ outerBoundary (cube d n)) : bLowInit beta n y = bVal (beta y) := by
  simp [bLowInit, hy]

theorem bLowInit_of_notMem (beta : Site d → Bool) {y : Site d}
    (hy : y ∉ outerBoundary (cube d n)) : bLowInit beta n y = 0 := by
  simp [bLowInit, hy]

end Initial

/-! ### The constrained odometers and configurations -/

open scoped Classical in
/-- The lower constrained frozen odometer `u_t^{(d-1)}` of the corrected source: frozen off
`Q_n^{(d)}`, capped at one, and otherwise raised by one when `s_t^{(d-1)} ≥ 2d`. -/
noncomputable def bLowOdo (beta : Site d → Bool) (n : ℕ) (η : Site (d + 1) → ℤ) :
    ℕ → Site d → ℤ
  | 0 => bLowInit beta n
  | t + 1 => fun y =>
      if y ∉ cube d n then bLowOdo beta n η t y
      else if bLowOdo beta n η t y = 1 then bLowOdo beta n η t y
      else bLowOdo beta n η t y +
        (if 2 * (d : ℤ) ≤ (η (cons 1 y) - 1) + lap (bLowOdo beta n η t) y then 1 else 0)

open scoped Classical in
/-- The upper constrained frozen odometer `u_t^{(d)}` of the corrected source on `ℤ^{d+1}`:
frozen off `Q_n^{(d)}` and for `x_1 > 1`, capped at one on `x_1 = 1`, and otherwise raised by
one when `s_t^{(d)} ≥ 2(d+1)`. -/
noncomputable def bUpOdo (beta : Site d → Bool) (n : ℕ) (η : Site (d + 1) → ℤ) :
    ℕ → Site (d + 1) → ℤ
  | 0 => bUpInit beta n
  | t + 1 => fun x =>
      if x ∉ cube (d + 1) n then bUpOdo beta n η t x
      else if 1 < x 0 then bUpOdo beta n η t x
      else if bUpOdo beta n η t x = 1 then bUpOdo beta n η t x
      else bUpOdo beta n η t x +
        (if 2 * ((d : ℤ) + 1) ≤ η x + lap (bUpOdo beta n η t) x then 1 else 0)

/-- The lower configuration `s_t^{(d-1)} = η^{(d-1)} + Δ u_t^{(d-1)}` with
`η^{(d-1)}(y) = η(1,y) - 1`. -/
noncomputable def bLowConf (beta : Site d → Bool) (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ)
    (y : Site d) : ℤ :=
  (η (cons 1 y) - 1) + lap (bLowOdo beta n η t) y

/-- The upper configuration `s_t^{(d)} = η + Δ u_t^{(d)}`. -/
noncomputable def bUpConf (beta : Site d → Bool) (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ)
    (x : Site (d + 1)) : ℤ :=
  η x + lap (bUpOdo beta n η t) x

/-! ### Update characterizations -/

section Update

variable {beta : Site d → Bool} {n : ℕ} {η : Site (d + 1) → ℤ}

theorem bLowOdo_zero : bLowOdo beta n η 0 = bLowInit beta n := rfl

theorem bUpOdo_zero : bUpOdo beta n η 0 = bUpInit beta n := rfl

open scoped Classical in
theorem bLowOdo_succ (t : ℕ) (y : Site d) :
    bLowOdo beta n η (t + 1) y =
      if y ∉ cube d n then bLowOdo beta n η t y
      else if bLowOdo beta n η t y = 1 then bLowOdo beta n η t y
      else bLowOdo beta n η t y +
        (if 2 * (d : ℤ) ≤ (η (cons 1 y) - 1) + lap (bLowOdo beta n η t) y then 1 else 0) :=
        rfl

open scoped Classical in
theorem bUpOdo_succ (t : ℕ) (x : Site (d + 1)) :
    bUpOdo beta n η (t + 1) x =
      if x ∉ cube (d + 1) n then bUpOdo beta n η t x
      else if 1 < x 0 then bUpOdo beta n η t x
      else if bUpOdo beta n η t x = 1 then bUpOdo beta n η t x
      else bUpOdo beta n η t x +
        (if 2 * ((d : ℤ) + 1) ≤ η x + lap (bUpOdo beta n η t) x then 1 else 0) := rfl

theorem bLowOdo_zero_or_one (t : ℕ) (y : Site d) :
    bLowOdo beta n η t y = 0 ∨ bLowOdo beta n η t y = 1 := by
  induction t generalizing y with
  | zero =>
    show bLowInit beta n y = 0 ∨ bLowInit beta n y = 1
    by_cases hy : y ∈ outerBoundary (cube d n)
    · rw [bLowInit_of_mem beta hy]; exact bVal_zero_or_one (beta y)
    · rw [bLowInit_of_notMem beta hy]; exact Or.inl rfl
  | succ t ih =>
    rw [bLowOdo_succ]
    by_cases hy : y ∉ cube d n
    · rw [if_pos hy]; exact ih y
    · rw [if_neg hy]
      by_cases h1 : bLowOdo beta n η t y = 1
      · rw [if_pos h1]; exact Or.inr h1
      · rw [if_neg h1]
        have h0 : bLowOdo beta n η t y = 0 := (ih y).resolve_right h1
        rw [h0]
        by_cases hc : 2 * (d : ℤ) ≤ (η (cons 1 y) - 1) + lap (bLowOdo beta n η t) y
        · rw [if_pos hc]; right; norm_num
        · rw [if_neg hc]; left; norm_num

open scoped Classical in
theorem bUpOdo_succ_of_frozen (t : ℕ) (x : Site (d + 1))
    (h : x ∉ cube (d + 1) n ∨ 1 < x 0) : bUpOdo beta n η (t + 1) x = bUpOdo beta n η t x := by
  rw [bUpOdo_succ]
  rcases h with hx | hx
  · rw [if_pos hx]
  · by_cases hc : x ∈ cube (d + 1) n
    · have hnc : ¬ (x ∉ cube (d + 1) n) := fun h' => h' hc
      rw [if_neg hnc, if_pos hx]
    · rw [if_pos hc]

theorem bUpOdo_cons_zero (t : ℕ) {w : Site d} (hw : w ∈ cube d n) :
    bUpOdo beta n η t (cons 0 w) = 1 := by
  induction t with
  | zero => exact bUpInit_cons_zero_of_mem beta hw
  | succ t ih =>
    rw [bUpOdo_succ_of_frozen t (cons 0 w)
      (Or.inl (cons_notMem_cube_of_head (n := n) 0 w rfl)), ih]

theorem bUpOdo_cons_of_one_lt (t : ℕ) (a : ℤ) (w : Site d) (ha : 1 < a) :
    bUpOdo beta n η t (cons a w) = 0 := by
  induction t with
  | zero => exact bUpInit_cons_of_ne beta a w (by omega) (by omega)
  | succ t ih =>
    have hhigh : 1 < (cons a w) 0 := by simpa [cons] using ha
    rw [bUpOdo_succ_of_frozen t (cons a w) (Or.inr hhigh), ih]

/-- The Laplacian of the upper odometer at the face site `cons 1 w`, for `w` in the cube:
the head neighbours contribute `1 + 0`, and the tangential part is the Laplacian of the
face odometer. -/
theorem lap_bUpOdo_cons_one (t : ℕ) {w : Site d} (hw : w ∈ cube d n) :
    lap (bUpOdo beta n η t) (cons 1 w) =
      1 + lap (fun v => bUpOdo beta n η t (cons 1 v)) w - 2 * bUpOdo beta n η t (cons 1 w) := by
  have h2 : bUpOdo beta n η t (cons 2 w) = 0 := bUpOdo_cons_of_one_lt t 2 w (by norm_num)
  have h0 : bUpOdo beta n η t (cons 0 w) = 1 := bUpOdo_cons_zero t hw
  have hc1 : cons ((1 : ℤ) + 1) w = cons 2 w := by norm_num
  have hc0 : cons ((1 : ℤ) - 1) w = cons 0 w := by norm_num
  simp only [lap, nbrSumZ_cons, hc1, hc0, h2, h0]
  push_cast
  ring

/-- **Face odometer equality.** For `d ≥ 1`, at every time, the upper odometer on the face
equals the lower odometer at every site of `ℤ^d` (both are frozen off the cube and equal to
`bVal (beta y)` on the outer boundary).  The induction is on all of `ℤ^d`, so the tangential
neighbours of a cube site are covered by the hypothesis. -/
theorem bUpOdo_cons_one_eq (hd : 1 ≤ d) (t : ℕ) (w : Site d) :
    bUpOdo beta n η t (cons 1 w) = bLowOdo beta n η t w := by
  induction t generalizing w with
  | zero =>
    show bUpInit beta n (cons 1 w) = bLowInit beta n w
    by_cases hw : w ∈ outerBoundary (cube d n)
    · rw [bUpInit_cons_one_of_mem beta hw, bLowInit_of_mem beta hw]
    · rw [bUpInit_cons_one_of_notMem beta hw, bLowInit_of_notMem beta hw]
  | succ t ih =>
    have hlapfun : lap (fun v => bUpOdo beta n η t (cons 1 v)) w = lap (bLowOdo beta n η t) w :=
      congrArg (fun f => lap f w) (funext ih)
    by_cases hw : w ∈ cube d n
    · have hup : cons 1 w ∈ cube (d + 1) n := (mem_cube_cons_one hd w).mpr hw
      have hlap := lap_bUpOdo_cons_one (beta := beta) (η := η) t hw
      rw [hlapfun, ih w] at hlap
      have e1 : ¬ (cons 1 w ∉ cube (d + 1) n) := fun h' => h' hup
      have e2 : ¬ (w ∉ cube d n) := fun h' => h' hw
      have e3 : ¬ (1 < (cons 1 w) 0) := by simp [cons]
      rw [bUpOdo_succ, bLowOdo_succ, if_neg e1, if_neg e3, if_neg e2]
      by_cases h1 : bLowOdo beta n η t w = 1
      · have h1' : bUpOdo beta n η t (cons 1 w) = 1 := (ih w).trans h1
        rw [if_pos h1', if_pos h1]
        exact ih w
      · have h1' : ¬ bUpOdo beta n η t (cons 1 w) = 1 := fun h => h1 ((ih w).symm.trans h)
        have h0 : bLowOdo beta n η t w = 0 := (bLowOdo_zero_or_one t w).resolve_right h1
        have hiff :
            (2 * ((d : ℤ) + 1) ≤ η (cons 1 w) + lap (bUpOdo beta n η t) (cons 1 w)) ↔
              (2 * (d : ℤ) ≤ (η (cons 1 w) - 1) + lap (bLowOdo beta n η t) w) := by
          rw [hlap, h0]
          constructor <;> intro h <;> linarith
        rw [if_neg h1', if_neg h1, ih w, h0]
        by_cases hc : 2 * (d : ℤ) ≤ (η (cons 1 w) - 1) + lap (bLowOdo beta n η t) w
        · rw [if_pos (hiff.mpr hc), if_pos hc]
        · have hn :
              ¬ (2 * ((d : ℤ) + 1) ≤ η (cons 1 w) + lap (bUpOdo beta n η t) (cons 1 w)) :=
            fun h => hc (hiff.mp h)
          rw [if_neg hn, if_neg hc]
    · have hup : cons 1 w ∉ cube (d + 1) n := fun h => hw ((mem_cube_cons_one hd w).mp h)
      rw [bUpOdo_succ_of_frozen t (cons 1 w) (Or.inl hup), bLowOdo_succ, if_pos hw]
      exact ih w

/-- **Configuration `+2`.** Where the upper odometer on the face vanishes, the upper
configuration exceeds the lower one by `2`, at every cube site and every time. -/
theorem bUpConf_eq_add_two (hd : 1 ≤ d) (t : ℕ) {w : Site d} (hw : w ∈ cube d n)
    (h0 : bUpOdo beta n η t (cons 1 w) = 0) :
    bUpConf beta n η t (cons 1 w) = bLowConf beta n η t w + 2 := by
  have hlapfun : lap (fun v => bUpOdo beta n η t (cons 1 v)) w = lap (bLowOdo beta n η t) w :=
    congrArg (fun f => lap f w) (funext (bUpOdo_cons_one_eq hd t))
  have hlap := lap_bUpOdo_cons_one (beta := beta) (η := η) t hw
  rw [hlapfun, h0] at hlap
  show η (cons 1 w) + lap (bUpOdo beta n η t) (cons 1 w) =
    (η (cons 1 w) - 1) + lap (bLowOdo beta n η t) w + 2
  rw [hlap]
  ring

end Update

/-- **Dimensional reduction on the face with pointwise tangential boundary seeds.** For `d ≥ 1`,
any `n`, any `beta : Site d → Bool` (the tangential value `bVal (beta y) ∈ {0,1}` chosen
independently at each boundary site), any `η` and `t`, and any `y ∈ Q_n^{(d)}`: the upper
odometer at `cons 1 y` equals the lower odometer at `y`, and where it vanishes the upper
configuration at `cons 1 y` is the lower configuration at `y` plus `2`. -/
theorem bOdo_dimensional_reduction (beta : Site d → Bool) (n : ℕ) (hd : 1 ≤ d)
    (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) (hy : y ∈ cube d n) :
    bUpOdo beta n η t (cons 1 y) = bLowOdo beta n η t y ∧
      (bUpOdo beta n η t (cons 1 y) = 0 →
        bUpConf beta n η t (cons 1 y) = bLowConf beta n η t y + 2) :=
  ⟨bUpOdo_cons_one_eq hd t y, fun h0 => bUpConf_eq_add_two hd t hy h0⟩

/-! ### Bridge to the zero-boundary odometers of `Exploding.Support.Reduction` -/

section Bridge

variable {n : ℕ} {η : Site (d + 1) → ℤ}

/-- With `beta = fun _ => false` the lower odometer is the zero-boundary one. -/
theorem bLowOdo_false_eq_redOdoDown (t : ℕ) (y : Site d) :
    bLowOdo (fun _ => false) n η t y = redOdoDown n η t y := by
  induction t generalizing y with
  | zero =>
    show bLowInit (fun _ => false) n y = 0
    by_cases hy : y ∈ outerBoundary (cube d n)
    · exact (bLowInit_of_mem (fun _ => false) hy).trans bVal_false
    · rw [bLowInit_of_notMem (fun _ => false) hy]
  | succ t ih =>
    have hf : bLowOdo (fun _ => false) n η t = redOdoDown n η t := funext ih
    rw [bLowOdo_succ, redOdoDown_succ, hf]

/-- With `beta = fun _ => false` the upper odometer agrees with the zero-boundary one at every
face site. The two differ only on `cons 0 y` with `y ∉ Q_n^{(d)}`, which the face dynamics
never read. -/
theorem bUpOdo_false_cons_one_eq_redOdoUp (t : ℕ) (y : Site d) :
    bUpOdo (fun _ => false) n η t (cons 1 y) = redOdoUp n η t (cons 1 y) := by
  induction t generalizing y with
  | zero =>
    show bUpInit (fun _ => false) n (cons 1 y) = redOdoUp n η 0 (cons 1 y)
    have hne : ¬ ((cons (1 : ℤ) y) 0 = 0) := by simp [cons]
    rw [redOdoUp_zero, if_neg hne]
    by_cases hy : y ∈ outerBoundary (cube d n)
    · exact (bUpInit_cons_one_of_mem (fun _ => false) hy).trans bVal_false
    · rw [bUpInit_cons_one_of_notMem (fun _ => false) hy]
  | succ t ih =>
    have hlapfun : lap (fun v => bUpOdo (fun _ => false) n η t (cons 1 v)) y
        = lap (fun v => redOdoUp n η t (cons 1 v)) y :=
      congrArg (fun f => lap f y) (funext ih)
    by_cases hx : cons 1 y ∈ cube (d + 1) n
    · have hy : y ∈ cube d n := by
        intro j
        simpa [cons] using hx j.succ
      have hl : lap (redOdoUp n η t) (cons 1 y) =
          lap (bUpOdo (fun _ => false) n η t) (cons 1 y) := by
        rw [lap_redOdoUp_cons_one, lap_bUpOdo_cons_one (beta := fun _ => false) (n := n) (η := η)
          t hy, hlapfun, ih y]
      have hnc : ¬ (cons 1 y ∉ cube (d + 1) n) := fun h => h hx
      have hhead : ¬ ((1 : ℤ) < (cons (1 : ℤ) y) 0) := by simp [cons]
      rw [redOdoUp_succ, bUpOdo_succ, if_neg hnc, if_neg hnc, if_neg hhead, if_neg hhead,
        ih y, ← hl]
    · rw [redOdoUp_succ, bUpOdo_succ, if_pos hx, if_pos hx]
      exact ih y

end Bridge

/-! ### Check of the `d = 1`, `n = 1` example

The cube `Q_1^{(1)}` is `{![1]}`, its outer boundary is `{![0], ![2]}`, and the face site
is `cons 1 ![1] = ![1, 1]`.  The statements below take an arbitrary pointwise boundary choice
`beta`; the two constant choices and a nonconstant one are instantiated. -/

section Example

theorem one_mem_cube : (![1] : Site 1) ∈ cube 1 1 := by
  intro i
  fin_cases i
  simp

theorem one_not_mem_outer : (![1] : Site 1) ∉ outerBoundary (cube 1 1) :=
  fun h => h.1 one_mem_cube

theorem zero_mem_outer : (![0] : Site 1) ∈ outerBoundary (cube 1 1) :=
  ⟨fun h => by have := h 0; norm_num at this, ![1], one_mem_cube, 0,
    Or.inl (by funext i; fin_cases i; simp [unit])⟩

theorem two_mem_outer : (![2] : Site 1) ∈ outerBoundary (cube 1 1) :=
  ⟨fun h => by have := h 0; norm_num at this, ![1], one_mem_cube, 0,
    Or.inr (by funext i; fin_cases i; simp [unit])⟩

theorem add_unit_zero_one : (![1] : Site 1) + unit 0 = ![2] := by
  funext i; fin_cases i; simp [unit]

theorem sub_unit_zero_one : (![1] : Site 1) - unit 0 = ![0] := by
  funext i; fin_cases i; simp [unit]

theorem lap_bLowOdo_zero_one (beta : Site 1 → Bool) (η : Site 2 → ℤ) :
    lap (bLowOdo beta 1 η 0) ![1] = bVal (beta ![2]) + bVal (beta ![0]) := by
  simp only [lap, nbrSumZ, Fin.sum_univ_one, bLowOdo_zero, add_unit_zero_one,
    sub_unit_zero_one, bLowInit_of_mem beta two_mem_outer, bLowInit_of_mem beta zero_mem_outer,
    bLowInit_of_notMem beta one_not_mem_outer, Nat.cast_one]
  ring

theorem bUpOdo_zero_cons_one_one (beta : Site 1 → Bool) (η : Site 2 → ℤ) :
    bUpOdo beta 1 η 0 (cons 1 ![1]) = 0 :=
  bUpInit_cons_one_of_notMem beta one_not_mem_outer

/-- Initial odometers and delivered heights at the face site `cons 1 ![1]` and the lower site
`![1]` of the `d = 1`, `n = 1` example, for any pointwise boundary choice `beta`. -/
theorem face_initial_delivered (beta : Site 1 → Bool) (η : Site 2 → ℤ) :
    bUpConf beta 1 η 0 (cons 1 ![1]) =
        η (cons 1 ![1]) + 1 + (bVal (beta ![2]) + bVal (beta ![0])) ∧
      bLowConf beta 1 η 0 ![1] = η (cons 1 ![1]) - 1 + (bVal (beta ![2]) + bVal (beta ![0])) := by
  have hfun : (fun v => bUpOdo beta 1 η 0 (cons 1 v)) = bLowOdo beta 1 η 0 :=
    funext (bUpOdo_cons_one_eq (d := 1) (beta := beta) (n := 1) (η := η) le_rfl 0)
  have hl' : lap (fun v => bUpOdo beta 1 η 0 (cons 1 v)) ![1] = lap (bLowOdo beta 1 η 0) ![1] :=
    congrArg (fun f => lap f ![1]) hfun
  have hl := lap_bUpOdo_cons_one (beta := beta) (η := η) (n := 1) 0 one_mem_cube
  rw [hl', bUpOdo_zero_cons_one_one, lap_bLowOdo_zero_one] at hl
  refine ⟨?_, ?_⟩
  · show η (cons 1 ![1]) + lap (bUpOdo beta 1 η 0) (cons 1 ![1]) = _
    rw [hl]
    ring
  · show (η (cons 1 ![1]) - 1) + lap (bLowOdo beta 1 η 0) ![1] = _
    rw [lap_bLowOdo_zero_one]

/-- The two constant seeds give the delivered heights `η + 1` (for `beta = fun _ => false`)
and `η + 3` (for `beta = fun _ => true`) at the face site. -/
theorem face_initial_both_seeds (η : Site 2 → ℤ) :
    bUpConf (fun _ => false) 1 η 0 (cons 1 ![1]) = η (cons 1 ![1]) + 1 ∧
      bUpConf (fun _ => true) 1 η 0 (cons 1 ![1]) = η (cons 1 ![1]) + 3 := by
  refine ⟨?_, ?_⟩
  · rw [(face_initial_delivered (fun _ => false) η).1, bVal_false]
    ring
  · rw [(face_initial_delivered (fun _ => true) η).1, bVal_true]
    ring

/-- **Nonconstant boundary check.** If `beta(0) = true` and `beta(2) = false` at the two outer
boundary sites, then the lower delivered height at `![1]` is `η(1,1)` and the upper one at the
face site `cons 1 ![1]` is `η(1,1) + 2`. Both odometers start at zero there. -/
theorem face_initial_nonconstant (beta : Site 1 → Bool) (η : Site 2 → ℤ)
    (h0 : beta ![0] = true) (h2 : beta ![2] = false) :
    bLowConf beta 1 η 0 ![1] = η (cons 1 ![1]) ∧
      bUpConf beta 1 η 0 (cons 1 ![1]) = η (cons 1 ![1]) + 2 := by
  obtain ⟨hu, hl⟩ := face_initial_delivered beta η
  rw [h0, h2, bVal_true, bVal_false] at hu hl
  refine ⟨?_, ?_⟩
  · rw [hl]
    ring
  · rw [hu]
    ring

/-- The nonconstant check is realized by the concrete choice `beta y = decide (y 0 = 0)`. -/
theorem face_mixed_boundary_check (η : Site 2 → ℤ) :
    bLowConf (fun y : Site 1 => decide (y 0 = 0)) 1 η 0 ![1] = η (cons 1 ![1]) ∧
      bUpConf (fun y : Site 1 => decide (y 0 = 0)) 1 η 0 (cons 1 ![1]) =
        η (cons 1 ![1]) + 2 :=
  face_initial_nonconstant _ η (by decide) (by decide)

end Example

end Exploding
