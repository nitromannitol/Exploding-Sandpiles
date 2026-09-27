/-
The constrained frozen toppling processes of Section 7.1 of `paper/exploding.tex`
with the *floor* at an arbitrary layer `i` rather than at layer `0`: the
dynamics on the face `x_0 = i + 1` of a cube in `ℤ^{d+1}` are compared with
`d`-dimensional dynamics on a cube in `ℤ^d`, exactly as in
`Exploding/Support/Reduction.lean`, whose lemmas are hard-coded to `i = 0`.

A site of `ℤ^{d+1}` is written `cons a y = (a, 𝐲)` with `a ∈ ℤ` and `𝐲 ∈ ℤ^d`.
The layer induction of Proposition 7.5 consumes this at `i = 1, …, n - 1`, once
layer `i` has been toppled and acts as the permanently lit floor for layer
`i + 1`.
-/
import Exploding.Support.Reduction

namespace Exploding

open LatticeProb

open scoped Classical

variable {d : ℕ}

/-- The `(d+1)`-dimensional constrained odometer of `(7.4)` with the floor at
layer `i`: the sites of layer `i` are permanently lit, the sites of layer
`i + 1` topple at most once, and the sites above are frozen. -/
noncomputable def redOdoUpAt (i : ℤ) (n : ℕ) (η : Site (d + 1) → ℤ) :
    ℕ → Site (d + 1) → ℤ
  | 0 => fun x => if x 0 = i then 1 else 0
  | t + 1 => fun x =>
      if x ∉ cube (d + 1) n then redOdoUpAt i n η t x
      else if x 0 ≤ i then redOdoUpAt i n η t x
      else if i + 1 < x 0 then redOdoUpAt i n η t x
      else if redOdoUpAt i n η t x = 1 then redOdoUpAt i n η t x
      else redOdoUpAt i n η t x +
        (if 2 * ((d : ℤ) + 1) ≤ η x + lap (redOdoUpAt i n η t) x then 1 else 0)

/-- The one-step unfolding of the shifted-floor constrained odometer. -/
theorem redOdoUpAt_succ (i : ℤ) (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (x : Site (d + 1)) :
    redOdoUpAt i n η (t + 1) x =
      if x ∉ cube (d + 1) n then redOdoUpAt i n η t x
      else if x 0 ≤ i then redOdoUpAt i n η t x
      else if i + 1 < x 0 then redOdoUpAt i n η t x
      else if redOdoUpAt i n η t x = 1 then redOdoUpAt i n η t x
      else redOdoUpAt i n η t x +
        (if 2 * ((d : ℤ) + 1) ≤ η x + lap (redOdoUpAt i n η t) x then 1 else 0) := rfl

/-- The initial data of the shifted-floor constrained odometer. -/
theorem redOdoUpAt_zero (i : ℤ) (n : ℕ) (η : Site (d + 1) → ℤ) (x : Site (d + 1)) :
    redOdoUpAt i n η 0 x = if x 0 = i then 1 else 0 := rfl

/-- The `d`-dimensional constrained odometer of `(7.5)` on the background
`η(i + 1, ·) - 1`, with the floor at layer `i`. -/
noncomputable def redOdoDownAt (i : ℤ) (n : ℕ) (η : Site (d + 1) → ℤ) :
    ℕ → Site d → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun y =>
      if y ∉ cube d n then redOdoDownAt i n η t y
      else if redOdoDownAt i n η t y = 1 then redOdoDownAt i n η t y
      else redOdoDownAt i n η t y +
        (if 2 * (d : ℤ) ≤ (η (cons (i + 1) y) - 1) + lap (redOdoDownAt i n η t) y
          then 1 else 0)

/-- The one-step unfolding of the shifted-floor reduced odometer. -/
theorem redOdoDownAt_succ (i : ℤ) (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) :
    redOdoDownAt i n η (t + 1) y =
      if y ∉ cube d n then redOdoDownAt i n η t y
      else if redOdoDownAt i n η t y = 1 then redOdoDownAt i n η t y
      else redOdoDownAt i n η t y +
        (if 2 * (d : ℤ) ≤ (η (cons (i + 1) y) - 1) + lap (redOdoDownAt i n η t) y
          then 1 else 0) := rfl

/-- The initial data of the shifted-floor reduced odometer. -/
theorem redOdoDownAt_zero (i : ℤ) (n : ℕ) (η : Site (d + 1) → ℤ) (y : Site d) :
    redOdoDownAt i n η 0 y = 0 := rfl

/-! ### The shifted-floor reduction -/

section ReductionShift

variable {i : ℤ} {n : ℕ}

/-- A site of layer `i` is off the cube, so it is permanently lit. -/
theorem cons_notMem_cube_of_head_eq (a : ℤ) (y : LatticeProb.Site d) (h : a = i)
    (hi : i < 1 ∨ (n : ℤ) < i) : cons a y ∉ cube (d + 1) n := by
  intro hc
  have h0 := (hc 0).1
  have h1 := (hc 0).2
  simp only [cons, Fin.cons_zero] at h0 h1
  omega

/-- The shifted-floor constrained odometer is one on its floor. -/
theorem redOdoUpAt_floor (η : LatticeProb.Site (d + 1) → ℤ) (t : ℕ) (y : Site d) :
    redOdoUpAt i n η t (cons i y) = 1 := by
  induction t with
  | zero => simp [redOdoUpAt_zero, cons]
  | succ t ih =>
    rw [redOdoUpAt_succ]
    by_cases hc : cons i y ∉ cube (d + 1) n
    · rw [if_pos hc]; exact ih
    · rw [if_neg hc]
      have hle : (cons i y) 0 ≤ i := le_of_eq (by simp only [cons, Fin.cons_zero])
      rw [if_pos hle]
      exact ih

/-- Above the active layer the shifted-floor constrained odometer is frozen. -/
theorem redOdoUpAt_above (η : LatticeProb.Site (d + 1) → ℤ) (t : ℕ) (x : LatticeProb.Site (d + 1))
    (h : i + 1 < x 0) :
    redOdoUpAt i n η t x = redOdoUpAt i n η 0 x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [redOdoUpAt_succ]
    by_cases hc : x ∉ cube (d + 1) n
    · rw [if_pos hc]; exact ih
    · rw [if_neg hc]
      by_cases hle : x 0 ≤ i
      · rw [if_pos hle]; exact ih
      · rw [if_neg hle, if_pos h]; exact ih

/-- Two layers above the floor the shifted-floor constrained odometer is zero. -/
theorem redOdoUpAt_cons_high (η : LatticeProb.Site (d + 1) → ℤ) (t : ℕ) (y : LatticeProb.Site d)
    (a : ℤ) (ha : i + 1 < a) :
    redOdoUpAt i n η t (cons a y) = 0 := by
  have h : i + 1 < (cons a y) 0 := by simpa [cons] using ha
  rw [redOdoUpAt_above η t _ h]
  have hne : ((cons a y) 0) ≠ i := by simp only [cons, Fin.cons_zero]; omega
  simp [redOdoUpAt_zero, hne]

/-- The active layer of the shifted-floor reduction is inside the cube exactly when
its `d`-dimensional shadow is. -/
theorem mem_cube_cons_succ (hi : 0 ≤ i) (hi' : i + 1 ≤ (n : ℤ))
    (y : LatticeProb.Site d) :
    cons (i + 1) y ∈ cube (d + 1) n ↔ y ∈ cube d n := by
  constructor
  · intro hc j
    have := hc j.succ
    simpa [cons] using this
  · intro hy j
    refine Fin.cases ?_ ?_ j
    · refine ⟨?_, ?_⟩
      · simp only [cons, Fin.cons_zero]; omega
      · simp only [cons, Fin.cons_zero]; omega
    · intro k
      have := hy k
      simpa [cons] using this

/-- The shifted-floor reduced odometer takes only the values zero and one. -/
theorem redOdoDownAt_zero_or_one (η : LatticeProb.Site (d + 1) → ℤ) (t : ℕ) (y : LatticeProb.Site d) :
    redOdoDownAt i n η t y = 0 ∨ redOdoDownAt i n η t y = 1 := by
  induction t generalizing y with
  | zero => left; rfl
  | succ t ih =>
    rw [redOdoDownAt_succ]
    by_cases hy : y ∉ cube d n
    · rw [if_pos hy]; exact ih y
    · rw [if_neg hy]
      by_cases h1 : redOdoDownAt i n η t y = 1
      · rw [if_pos h1]; right; exact h1
      · rw [if_neg h1]
        have h0 : redOdoDownAt i n η t y = 0 := (ih y).resolve_right h1
        rw [h0]
        by_cases hc : 2 * (d : ℤ) ≤ (η (cons (i + 1) y) - 1) + lap (redOdoDownAt i n η t) y
        · rw [if_pos hc]; right; ring
        · rw [if_neg hc]; left; ring

/-- The Laplacian at the active layer, in terms of the floor and the shadow. -/
theorem lap_redOdoUpAt_cons_succ (η : LatticeProb.Site (d + 1) → ℤ) (t : ℕ) (y : LatticeProb.Site d) :
    lap (redOdoUpAt i n η t) (cons (i + 1) y) =
      1 + lap (fun w => redOdoUpAt i n η t (cons (i + 1) w)) y
        - 2 * redOdoUpAt i n η t (cons (i + 1) y) := by
  simp only [lap, nbrSumZ_cons]
  rw [show redOdoUpAt i n η t (cons (i + 1 + 1) y) = 0 from
      redOdoUpAt_cons_high η t y (i + 1 + 1) (by omega),
    show redOdoUpAt i n η t (cons (i + 1 - 1) y) = 1 from by
      rw [show i + 1 - 1 = i from by ring]; exact redOdoUpAt_floor η t y]
  push_cast
  ring

/-- **The shifted-floor reduction.**  On the active layer the `(d+1)`-dimensional
constrained odometer equals the `d`-dimensional constrained odometer of the
background `η(i + 1, ·) - 1`. -/
theorem redOdoUpAt_agree (η : LatticeProb.Site (d + 1) → ℤ) (hi0 : 0 ≤ i)
    (hi : i + 1 ≤ (n : ℤ)) (t : ℕ) (y : LatticeProb.Site d) :
    redOdoUpAt i n η t (cons (i + 1) y) = redOdoDownAt i n η t y := by
  induction t generalizing y with
  | zero => simp [redOdoUpAt_zero, redOdoDownAt_zero, cons]
  | succ t ih =>
    rw [redOdoUpAt_succ, redOdoDownAt_succ]
    have hmem : (cons (i + 1) y ∉ cube (d + 1) n) ↔ (y ∉ cube d n) := by
      simp [mem_cube_cons_succ hi0 hi y]
    have hnot : ¬ (i + 1 < (cons (i + 1) y) 0) := by
      simp only [cons, Fin.cons_zero]; omega
    have hle : ¬ ((cons (i + 1) y) 0 ≤ i) := by
      simp only [cons, Fin.cons_zero]; omega
    rw [if_neg hle, if_neg hnot]
    by_cases hy : y ∉ cube d n
    · rw [if_pos (hmem.mpr hy), if_pos hy]
      exact ih y
    · rw [if_neg (fun h => hy (hmem.mp h)), if_neg hy]
      by_cases h1 : redOdoDownAt i n η t y = 1
      · rw [if_pos h1]
        rw [if_pos (by rw [ih y]; exact h1)]
        exact ih y
      · rw [if_neg h1]
        rw [if_neg (by rw [ih y]; exact h1)]
        have hlap : lap (redOdoUpAt i n η t) (cons (i + 1) y)
            = 1 + lap (redOdoDownAt i n η t) y - 2 * redOdoDownAt i n η t y := by
          rw [lap_redOdoUpAt_cons_succ]
          simp only [lap]
          rw [nbrSumZ_congr (fun w => ih w) y, ih y]
        have h0 : redOdoDownAt i n η t y = 0 :=
          (redOdoDownAt_zero_or_one η t y).resolve_right h1
        rw [ih y, h0, hlap]
        congr 1
        by_cases h : 2 * (d : ℤ) ≤ η (cons (i + 1) y) - 1 + lap (redOdoDownAt i n η t) y
        · rw [if_pos h, if_pos (by linarith)]
        · rw [if_neg h, if_neg (by linarith)]
end ReductionShift

end Exploding
