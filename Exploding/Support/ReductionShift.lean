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
import Exploding.Support.SubSpanZero
import Exploding.Support.SubFodo
import Exploding.Support.SubOdo
import Exploding.Support.CrossingTimeAux

namespace Exploding

open LatticeProb

open scoped Classical

variable {d : ℕ}

/-- The `(d+1)`-dimensional constrained odometer of `(7.4)` with the floor at
layer `i`: the sites of layer `i` are permanently lit, the sites of layer
`i + 1` topple at most once, and the sites above are frozen. -/
noncomputable def redOdoUpAt (i : ℤ) (n : ℕ) (η : Site (d + 1) → ℤ) :
    ℕ → Site (d + 1) → ℤ
  | 0 => fun x => if x 0 = i ∧ x ∈ cube (d + 1) n then 1 else 0
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
    redOdoUpAt i n η 0 x = if x 0 = i ∧ x ∈ cube (d + 1) n then 1 else 0 := rfl

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
theorem redOdoUpAt_floor (η : LatticeProb.Site (d + 1) → ℤ) (t : ℕ) (y : Site d)
    (hy : cons i y ∈ cube (d + 1) n) :
    redOdoUpAt i n η t (cons i y) = 1 := by
  induction t with
  | zero =>
    rw [redOdoUpAt_zero]
    rw [if_pos]
    exact ⟨rfl, hy⟩
  | succ t ih =>
    rw [redOdoUpAt_succ]
    by_cases hc : cons i y ∉ cube (d + 1) n
    · rw [if_pos hc]; exact ih
    · rw [if_neg hc]
      have hle : (cons i y) 0 ≤ i := le_of_eq (by simp only [cons, Fin.cons_zero])
      rw [if_pos hle]
      exact ih

/-- Below its floor the shifted-floor constrained odometer is zero. -/
theorem redOdoUpAt_below (η : LatticeProb.Site (d + 1) → ℤ) (t : ℕ) (x : LatticeProb.Site (d + 1))
    (h : x 0 < i) : redOdoUpAt i n η t x = 0 := by
  induction t with
  | zero =>
    rw [redOdoUpAt_zero, if_neg]
    rintro ⟨heq, -⟩
    omega
  | succ t ih =>
    rw [redOdoUpAt_succ]
    by_cases hc : x ∉ cube (d + 1) n
    · rw [if_pos hc]; exact ih
    · rw [if_neg hc]
      by_cases hle : x 0 ≤ i
      · rw [if_pos hle]; exact ih
      · rw [if_neg hle]
        exfalso; omega

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
theorem lap_redOdoUpAt_cons_succ (η : LatticeProb.Site (d + 1) → ℤ) (t : ℕ) (y : LatticeProb.Site d)
    (hi1 : 1 ≤ i) (hy : cons (i + 1) y ∈ cube (d + 1) n) :
    lap (redOdoUpAt i n η t) (cons (i + 1) y) =
      1 + lap (fun w => redOdoUpAt i n η t (cons (i + 1) w)) y
        - 2 * redOdoUpAt i n η t (cons (i + 1) y) := by
  simp only [lap, nbrSumZ_cons]
  rw [show redOdoUpAt i n η t (cons (i + 1 + 1) y) = 0 from
      redOdoUpAt_cons_high η t y (i + 1 + 1) (by omega),
    show redOdoUpAt i n η t (cons (i + 1 - 1) y) = 1 from by
      rw [show i + 1 - 1 = i from by ring]
      exact redOdoUpAt_floor η t y (by
        intro l
        refine Fin.cases ?_ ?_ l
        · have h0 : (i + 1 : ℤ) ≤ (n : ℤ) := by
            have := hy 0
            simpa only [cons, Fin.cons_zero] using this.2
          simp only [cons, Fin.cons_zero]
          exact ⟨hi1, by omega⟩
        · intro k
          simpa only [cons, Fin.cons_succ] using hy k.succ)]
  push_cast
  ring

/-- **The shifted-floor reduction.**  On the active layer the `(d+1)`-dimensional
constrained odometer equals the `d`-dimensional constrained odometer of the
background `η(i + 1, ·) - 1`. -/
theorem redOdoUpAt_agree (η : LatticeProb.Site (d + 1) → ℤ) (hi0 : 0 ≤ i) (hi1 : 1 ≤ i)
    (hi : i + 1 ≤ (n : ℤ)) (t : ℕ) (y : LatticeProb.Site d) :
    redOdoUpAt i n η t (cons (i + 1) y) = redOdoDownAt i n η t y := by
  induction t generalizing y with
  | zero =>
    rw [redOdoUpAt_zero, redOdoDownAt_zero]
    rw [if_neg]
    simp only [cons, Fin.cons_zero]
    omega
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
          rw [lap_redOdoUpAt_cons_succ η t y hi1
            ((mem_cube_cons_succ hi0 hi y).mpr (not_not.mp hy))]
          simp only [lap]
          rw [nbrSumZ_congr (fun w => ih w) y, ih y]
        have h0 : redOdoDownAt i n η t y = 0 :=
          (redOdoDownAt_zero_or_one η t y).resolve_right h1
        rw [ih y, h0, hlap]
        congr 1
        by_cases h : 2 * (d : ℤ) ≤ η (cons (i + 1) y) - 1 + lap (redOdoDownAt i n η t) y
        · rw [if_pos h, if_pos (by linarith)]
        · rw [if_neg h, if_neg (by linarith)]
theorem redOdoDownAt_eq_spanOdo (η : LatticeProb.Site (d + 1) → ℤ) (t : ℕ)
    (y : LatticeProb.Site d) :
    redOdoDownAt i n η t y = spanOdo n (fun w => η (cons (i + 1) w) - 1) t y := by
  induction t generalizing y with
  | zero => rfl
  | succ t ih =>
    rw [redOdoDownAt_succ]
    have hlap : lap (fun w => redOdoDownAt i n η t w) y
        = lap (spanOdo n (fun w => η (cons (i + 1) w) - 1) t) y := by
      simp only [lap]
      rw [nbrSumZ_congr (fun w => ih w) y, ih y]
    rw [hlap, ih y]
    simp only [spanOdo]
    by_cases hy : y ∉ cube d n
    · rw [if_pos hy, if_pos hy]; exact spanOdo_of_notMem n _ t hy
    · rw [if_neg hy, if_neg hy]
      by_cases h1 : spanOdo n (fun w => η (cons (i + 1) w) - 1) t y = 1
      · simp only [if_pos h1]; exact h1
      · rw [if_neg h1, if_neg h1]

/-- **The layer step.**  If the `d`-dimensional shadow of layer `i + 1` is
internally spanned, then layer `i + 1` of the box topples completely, at a
uniform time, once layer `i` is permanently lit. -/
theorem layer_topples (η : LatticeProb.Site (d + 1) → ℤ) (hi0 : 0 ≤ i) (hi1 : 1 ≤ i)
    (hi : i + 1 ≤ (n : ℤ))
    (hspan : InternallySpanned (fun w : LatticeProb.Site d => η (cons (i + 1) w) - 1) n) :
    ∀ y ∈ cube d n, ∃ t : ℕ, redOdoUpAt i n η t (cons (i + 1) y) = 1 := by
  intro y hy
  obtain ⟨t, ht⟩ := hspan y hy
  refine ⟨t, ?_⟩
  rw [redOdoUpAt_agree η hi0 hi1 hi t y, redOdoDownAt_eq_spanOdo]
  exact ht

/-- The low face of the box is the outer boundary of the box at layer `0`. -/
theorem cons_zero_mem_faceOut (hn : 1 ≤ n) (y : Site d) (hy : y ∈ cube d n) :
    cons (0 : ℤ) y ∈ faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false := by
  refine ⟨?_, ?_⟩
  · right
    refine ⟨?_, cons 1 y, ?_, ?_⟩
    · intro h
      have h0 := h 0
      simp only [cons, Fin.cons_zero, Pi.zero_apply] at h0
      omega
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [cons, Fin.cons_zero, Pi.zero_apply]
        exact ⟨by omega, by omega⟩
      · intro k
        simp only [cons, Fin.cons_succ, Pi.zero_apply]
        have hk := hy k
        exact ⟨by omega, by omega⟩
    · refine ⟨⟨0, by omega⟩, ?_⟩
      left
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [cons, unit]
      · intro k
        simp [cons, unit]
  · simp [cons]

/-- The frozen odometer never decreases in time. -/
theorem fodo_mono_time (S : Set (Site d)) (s0 w0 : Site d → ℤ) :
    ∀ t x, fodo S s0 w0 t x ≤ fodo S s0 w0 (t + 1) x := by
  intro t x
  rw [fodo_succ]
  by_cases hx : x ∈ S
  · rw [if_pos hx, fodo_of_mem S s0 w0 t hx]
  · rw [if_neg hx]
    split_ifs <;> omega


/-- `fodo` is monotone in time. -/
theorem fodo_mono_time' (S : Set (Site d)) (s0 w0 : Site d → ℤ) :
    ∀ t t' x, t ≤ t' → fodo S s0 w0 t x ≤ fodo S s0 w0 t' x := by
  intro t t' x h
  induction t' with
  | zero =>
    have h0 : t = 0 := Nat.le_zero.mp h
    subst h0; exact le_rfl
  | succ t' ih =>
    rcases Nat.lt_or_ge t (t' + 1) with hlt | hge
    · have hle : t ≤ t' := Nat.lt_succ_iff.mp hlt
      exact le_trans (ih hle) (fodo_mono_time S s0 w0 t' x)
    · have heq : t = t' + 1 := le_antisymm h hge
      subst heq; exact le_rfl

/-- The shifted-floor constrained odometer is at most one. -/
theorem redOdoUpAt_le_one (n : ℕ) (η : Site (d + 1) → ℤ) (i : ℤ) :
    ∀ t x, redOdoUpAt i n η t x ≤ 1 := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [redOdoUpAt_zero]
    split_ifs <;> omega
  | succ t ih =>
    intro x
    rw [redOdoUpAt_succ]
    have h := ih x
    split_ifs <;> omega

/-- The shifted-floor constrained odometer takes only the values zero and one. -/
theorem redOdoUpAt_zero_or_one (n : ℕ) (η : Site (d + 1) → ℤ) (i : ℤ) :
    ∀ t x, redOdoUpAt i n η t x = 0 ∨ redOdoUpAt i n η t x = 1 := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [redOdoUpAt_zero]
    split_ifs <;> omega
  | succ t ih =>
    intro x
    rw [redOdoUpAt_succ]
    have h := ih x
    split_ifs <;> omega

/-- The firing case of the transport step. -/
theorem fodo_fires_of_redOdoUpAt (n : ℕ) (η : Site (d + 1) → ℤ) (i : ℤ) (T t : ℕ)
    (x : Site (d + 1))
    (hle1 : ∀ y, redOdoUpAt i n η t y ≤
      fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + t) y)
    (h0 : redOdoUpAt i n η t x = 0)
    (hc : x ∈ cube (d + 1) n)
    (hthr : 2 * ((d : ℤ) + 1) ≤ η x + lap (redOdoUpAt i n η t) x) :
    redOdoUpAt i n η (t + 1) x ≤
      fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + (t + 1)) x := by
  by_cases hf : fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
      (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
        (fun _ => (1 : ℤ))) (T + t) x = 0
  · have hthr' : 2 * ((d : ℤ) + 1) ≤ η x + lap (fodo ((rboxShift (fun _ : Fin (d+1) => n)
        (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + t)) x := by
      simp only [lap]
      rw [hf, mul_zero, sub_zero]
      have hmono : nbrSumZ (redOdoUpAt i n η t) x ≤
          nbrSumZ (fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
            (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
              ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (T + t)) x :=
        nbrSumZ_mono (fun y => hle1 y) x
      simp only [lap] at hthr
      rw [h0, mul_zero, sub_zero] at hthr
      linarith
    have hle1' : redOdoUpAt i n η (t + 1) x ≤ 1 := redOdoUpAt_le_one n η i (t + 1) x
    have hfodo1 : fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + (t + 1)) x = 1 := by
      have hidx : T + (t + 1) = (T + t) + 1 := by omega
      rw [hidx, fodo_succ]
      by_cases hxS : x ∈ ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ)
      · exfalso
        exact hxS (by
          intro i
          have hxi := hc i
          simp only [Pi.zero_apply, mul_zero, zero_add]
          exact hxi)
      · rw [if_neg hxS]
        rw [if_pos]
        · rw [hf]
          ring
        · simp only [fconf]
          exact hthr'
    rw [hfodo1]
    exact hle1'
  · have hpos : 1 ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + t) x := by
      have hnn : (0 : ℤ) ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
          (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
            ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (T + t) x :=
        fodo_nonneg _ _ _
          (Set.indicator_nonneg (fun _ _ => zero_le_one)) (T + t) x
      omega
    exact le_trans (le_trans (redOdoUpAt_le_one n η i (t + 1) x) hpos)
      (fodo_mono_time' _ _ _ (T + t) (T + (t + 1)) x (by omega))

/-- The transport step: the layer-`i` constrained odometer is dominated by the frozen
odometer, once layer `i` is already toppled in the latter. -/
theorem fodo_dominates_redOdoUpAt (n : ℕ) (η : Site (d + 1) → ℤ)
    (i : ℤ) (T : ℕ)
    (hT : ∀ y ∈ cube d n, 1 ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
      (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
        (fun _ => (1 : ℤ))) T (cons i y)) :
    ∀ t x, redOdoUpAt i n η t x ≤
      fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + t) x := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [redOdoUpAt_zero]
    by_cases hxi : x 0 = i ∧ x ∈ cube (d + 1) n
    · rw [if_pos hxi]
      obtain ⟨h0, hmem⟩ := hxi
      have hxeq : x = cons i (fun l => x l.succ) := by
        funext j
        refine Fin.cases ?_ ?_ j
        · simpa [cons] using h0
        · intro k; simp [cons]
      rw [hxeq]
      have hmem' : (fun l => x l.succ) ∈ cube d n := by
        intro l
        have h := hmem l.succ
        simpa [cons] using h
      rw [show T + 0 = T from rfl]
      exact hT (fun l => x l.succ) hmem'
    · rw [if_neg hxi]
      exact fodo_nonneg _ _ _
        (Set.indicator_nonneg (fun _ _ => zero_le_one)) (T + 0) x
  | succ t ih =>
    intro x
    rw [redOdoUpAt_succ]
    by_cases hc : x ∉ cube (d + 1) n
    · rw [if_pos hc]
      exact le_trans (ih x) (fodo_mono_time' _ _ _ (T + t) (T + (t + 1)) x (by omega))
    · rw [if_neg hc]
      by_cases hle : x 0 ≤ i
      · rw [if_pos hle]
        exact le_trans (ih x) (fodo_mono_time' _ _ _ (T + t) (T + (t + 1)) x (by omega))
      · rw [if_neg hle]
        by_cases hlt : i + 1 < x 0
        · rw [if_pos hlt]
          exact le_trans (ih x) (fodo_mono_time' _ _ _ (T + t) (T + (t + 1)) x (by omega))
        · rw [if_neg hlt]
          by_cases h1 : redOdoUpAt i n η t x = 1
          · rw [if_pos h1]
            have hle1 : redOdoUpAt i n η t x ≤
                fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
                  (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
                    ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (T + t) x := ih x
            rw [h1] at hle1
            have hmono := fodo_mono_time' ((rboxShift (fun _ : Fin (d+1) => n)
              (0 : Site (d+1)))ᶜ) η
              (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
                ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (T + t) (T + (t + 1)) x (by omega)
            omega
          · rw [if_neg h1]
            have h0 : redOdoUpAt i n η t x = 0 := by
              rcases redOdoUpAt_zero_or_one n η i t x with h | h
              · exact h
              · exact absurd h h1
            by_cases hthr : 2 * ((d : ℤ) + 1) ≤ η x + lap (redOdoUpAt i n η t) x
            · have hstep : redOdoUpAt i n η (t + 1) x
                  = redOdoUpAt i n η t x + 1 := by
                rw [redOdoUpAt_succ]
                rw [if_neg hc, if_neg hle, if_neg hlt, if_neg h1, if_pos hthr]
              rw [if_pos hthr, ← hstep]
              exact fodo_fires_of_redOdoUpAt n η i T t x (fun y => ih y) h0 (not_not.mp hc) hthr
            · have hnext : redOdoUpAt i n η (t + 1) x = redOdoUpAt i n η t x := by
                rw [redOdoUpAt_succ]
                rw [if_neg hc, if_neg hle, if_neg hlt, if_neg h1, if_neg hthr]
                ring
              rw [if_neg hthr, h0, zero_add]
              exact fodo_nonneg _ _ _
                (Set.indicator_nonneg (fun _ _ => zero_le_one)) (T + (t + 1)) x

/-- The bootstrap odometer is monotone in time. -/
theorem spanOdo_mono_le (n : ℕ) (η : Site d → ℤ) {t t' : ℕ} (h : t ≤ t') (x : Site d) :
    spanOdo n η t x ≤ spanOdo n η t' x := by
  induction h with
  | refl => exact le_rfl
  | step h ih => exact le_trans ih (spanOdo_mono n η _ x)

/-- A uniform time at which the `d`-dimensional bootstrap odometer has toppled the whole
cube, when it is internally spanned. -/
theorem exists_uniform_span_time (n : ℕ) (η : Site d → ℤ)
    (hspan : InternallySpanned η n) :
    ∃ T : ℕ, ∀ y ∈ cube d n, spanOdo n η T y = 1 := by
  classical
  have hfin : (cube d n).Finite := by
    refine (Set.Finite.pi (fun _ : Fin d => Set.finite_Icc (0 : ℤ) (n : ℤ))).subset ?_
    intro x hx i _
    exact ⟨by have h := hx i; omega, (hx i).2⟩
  choose t ht using hspan
  refine ⟨hfin.toFinset.sup (fun y => if hy : y ∈ cube d n then t y hy else 0), ?_⟩
  intro y hy
  have hmem : y ∈ hfin.toFinset := by simpa using hy
  have hle : (if hy : y ∈ cube d n then t y hy else 0) ≤
      hfin.toFinset.sup (fun y => if hy : y ∈ cube d n then t y hy else 0) :=
    Finset.le_sup (f := fun y => if hy : y ∈ cube d n then t y hy else 0) hmem
  simp only [dif_pos hy] at hle
  have h1 := spanOdo_mono_le n η hle y
  rw [ht y hy] at h1
  have h2 : spanOdo n η (hfin.toFinset.sup fun y => if hy : y ∈ cube d n then t y hy else 0) y ≤ 1 :=
    spanOdo_le_one n η _ y
  omega

/-- The cube is finite. -/
theorem cube_finite' (n : ℕ) : (cube d n).Finite := by
  refine (Set.Finite.pi (fun _ : Fin d => Set.finite_Icc (0 : ℤ) (n : ℤ))).subset ?_
  intro x hx i _
  exact ⟨by have h := hx i; omega, (hx i).2⟩

/-- Two odometers that agree on the cube and vanish off it have the same Laplacian there. -/
theorem lap_congr_on_cube (n : ℕ) (u v : Site d → ℤ)
    (h : ∀ x ∈ cube d n, u x = v x) (hu : ∀ x ∉ cube d n, u x = 0)
    (hv : ∀ x ∉ cube d n, v x = 0) (x : Site d) (hx : x ∈ cube d n) :
    lap u x = lap v x := by
  simp only [lap]
  rw [nbrSumZ_congr (fun y => by
    by_cases hy : y ∈ cube d n
    · exact h y hy
    · rw [hu y hy, hv y hy]) x, h x hx]

/-- If no site of the cube topples at step `t + 1`, no site topples at any later step. -/
theorem spanOdo_stabilizes (n : ℕ) (η : Site d → ℤ) (t : ℕ)
    (h : ∀ x ∈ cube d n, spanOdo n η (t + 1) x = spanOdo n η t x) :
    ∀ s, t ≤ s → ∀ x ∈ cube d n, spanOdo n η s x = spanOdo n η t x := by
  intro s hs
  induction hs with
  | refl => intro x hx; rfl
  | step hs ih =>
    intro x hx
    rw [spanOdo_succ_eq]
    rw [if_neg (not_not.mpr hx)]
    have hlap : lap (spanOdo n η _) x = lap (spanOdo n η t) x :=
      lap_congr_on_cube n _ _ (fun y hy => ih y hy)
        (fun y hy => spanOdo_of_notMem n η _ hy)
        (fun y hy => spanOdo_of_notMem n η t hy) x hx
    rw [hlap, ih x hx]
    by_cases h1 : spanOdo n η t x = 1
    · rw [if_pos h1, h1]
    · rw [if_neg h1]
      by_cases hthr : 2 * (d : ℤ) ≤ η x + lap (spanOdo n η t) x
      · exfalso
        have hstep := h x hx
        rw [spanOdo_succ_eq] at hstep
        rw [if_neg (not_not.mpr hx), if_neg h1, if_pos hthr] at hstep
        omega
      · rw [if_neg hthr]
        ring

/-- **The counting bound.**  If the cube is internally spanned, then every site of the cube
has toppled by time `(cube d n).ncard`.  The set of untoppled sites is non-increasing; if it
ever failed to shrink while nonempty the process would be frozen, contradicting internal
spanning; so it shrinks at least once per step until it is empty. -/
theorem spanOdo_topples_by_ncard (n : ℕ) (η : Site d → ℤ)
    (hspan : InternallySpanned η n) :
    ∀ x ∈ cube d n, spanOdo n η ((cube d n).ncard) x = 1 := by
  classical
  have hfin := cube_finite' (d := d) n
  set g : ℕ → Finset (Site d) := fun t => hfin.toFinset.filter (fun y => spanOdo n η t y = 0)
    with hg
  have hg_sub : ∀ t, g (t + 1) ⊆ g t := by
    intro t y hy
    simp only [hg, Finset.mem_filter] at hy ⊢
    obtain ⟨h1, h2⟩ := hy
    refine ⟨h1, ?_⟩
    have hmono := spanOdo_mono n η t y
    have hnn := spanOdo_nonneg n η t y
    omega
  have hg_strict : ∀ t, g t ≠ ∅ → (g (t + 1)).card < (g t).card := by
    intro t hne
    have hss := hg_sub t
    have hproper : g (t + 1) ≠ g t := by
      intro heq
      obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hyc : y ∈ cube d n := hfin.mem_toFinset.mp (Finset.mem_filter.mp hy).1
      have hy0 : spanOdo n η t y = 0 := (Finset.mem_filter.mp hy).2
      have hfroz : ∀ s, t ≤ s → ∀ x ∈ cube d n, spanOdo n η s x = spanOdo n η t x := by
        apply spanOdo_stabilizes n η t
        intro x hx
        have hiff : x ∈ g (t + 1) ↔ x ∈ g t := by rw [heq]
        have h1 : spanOdo n η (t + 1) x = 0 ↔ spanOdo n η t x = 0 := by
          constructor
          · intro h
            exact (Finset.mem_filter.mp (hiff.mp (Finset.mem_filter.mpr
              ⟨hfin.mem_toFinset.mpr hx, h⟩))).2
          · intro h
            exact (Finset.mem_filter.mp (hiff.mpr (Finset.mem_filter.mpr
              ⟨hfin.mem_toFinset.mpr hx, h⟩))).2
        have hmono := spanOdo_mono n η t x
        have hle1 := spanOdo_le_one n η (t + 1) x
        have hnn := spanOdo_nonneg n η t x
        by_cases hz : spanOdo n η t x = 0
        · rw [h1.mpr hz, hz]
        · have hz1 : spanOdo n η (t + 1) x ≠ 0 := fun h => hz (h1.mp h)
          omega
      obtain ⟨tx, htx⟩ := hspan y hyc
      have hle : t ≤ tx := by
        by_contra hcon
        have hcon' : tx < t := Nat.lt_of_not_le hcon
        have hmono := spanOdo_mono_le n η (Nat.le_of_lt hcon') y
        rw [htx, hy0] at hmono
        omega
      rw [hfroz tx hle y hyc, hy0] at htx
      omega
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hss, hproper⟩)
  have hbound : ∀ t, g t ≠ ∅ → (g t).card + t ≤ (g 0).card := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ k ih =>
      intro hne
      have hk : g k ≠ ∅ := by
        intro h
        apply hne
        exact Finset.eq_empty_iff_forall_notMem.mpr (fun z hz =>
          Finset.eq_empty_iff_forall_notMem.mp h z (hg_sub k hz))
      have h1 := ih hk
      have h2 := hg_strict k hk
      omega
  have hcard0 : (g 0).card = (cube d n).ncard := by
    rw [hg]
    simp only
    have hfilter : hfin.toFinset.filter (fun y => spanOdo n η 0 y = 0) = hfin.toFinset :=
      Finset.filter_true_of_mem (fun y hy => rfl)
    rw [hfilter]
    exact (Set.ncard_eq_toFinset_card _ hfin).symm
  intro x hx
  by_contra hcon
  have hx0 : spanOdo n η ((cube d n).ncard) x = 0 := by
    have hnn := spanOdo_nonneg n η ((cube d n).ncard) x
    have hle := spanOdo_le_one n η ((cube d n).ncard) x
    omega
  have hmem : x ∈ g ((cube d n).ncard) :=
    Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hx, hx0⟩
  have hne : g ((cube d n).ncard) ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨x, hmem⟩
  have hb := hbound ((cube d n).ncard) hne
  rw [hcard0] at hb
  have hpos : 1 ≤ (g ((cube d n).ncard)).card := Finset.card_pos.mpr ⟨x, hmem⟩
  omega

/-- A uniform time, bounded by the number of sites, at which the `d`-dimensional bootstrap
odometer has toppled the whole cube, when it is internally spanned. -/
theorem exists_uniform_span_time_le (n : ℕ) (η : Site d → ℤ)
    (hspan : InternallySpanned η n) :
    ∃ T : ℕ, T ≤ n ^ d ∧ ∀ y ∈ cube d n, spanOdo n η T y = 1 := by
  refine ⟨(cube d n).ncard, ?_, spanOdo_topples_by_ncard n η hspan⟩
  rw [aux_ct_assemble_cube_ncard]

/-- The tile of the box at the origin is the box itself. -/
theorem rboxShift_zero_eq_cube (n : ℕ) :
    rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)) = cube (d + 1) n := by
  ext x
  simp only [rboxShift, cube, Set.mem_setOf_eq, Pi.zero_apply, mul_zero, zero_add]
  constructor <;> intro h i <;> exact h i

/-- The low face of the box is exactly the part of the closure at layer `0`. -/
theorem faceOut_eq_lowface (n : ℕ) :
    faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false
      = {x : Site (d + 1) | x 0 = 0 ∧ x ∈ closureN (cube (d + 1) n)} := by
  ext x
  simp only [faceOut, Set.mem_inter_iff, Set.mem_setOf_eq, rboxShift_zero_eq_cube]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨h1, h2⟩

/-- The floor-`0` constrained odometer with the low face of the box lit. -/
noncomputable def redOdoLow (n : ℕ) (η : Site (d + 1) → ℤ) : ℕ → Site (d + 1) → ℤ
  | 0 => fun x => if x 0 = 0 ∧ x ∈ closureN (cube (d + 1) n) then 1 else 0
  | t + 1 => fun x =>
      if x ∉ cube (d + 1) n then redOdoLow n η t x
      else if 1 < x 0 then redOdoLow n η t x
      else if redOdoLow n η t x = 1 then redOdoLow n η t x
      else redOdoLow n η t x +
        (if 2 * ((d : ℤ) + 1) ≤ η x + lap (redOdoLow n η t) x then 1 else 0)

theorem redOdoLow_succ (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (x : Site (d + 1)) :
    redOdoLow n η (t + 1) x =
      if x ∉ cube (d + 1) n then redOdoLow n η t x
      else if 1 < x 0 then redOdoLow n η t x
      else if redOdoLow n η t x = 1 then redOdoLow n η t x
      else redOdoLow n η t x +
        (if 2 * ((d : ℤ) + 1) ≤ η x + lap (redOdoLow n η t) x then 1 else 0) := rfl

theorem redOdoLow_zero (n : ℕ) (η : Site (d + 1) → ℤ) (x : Site (d + 1)) :
    redOdoLow n η 0 x = if x 0 = 0 ∧ x ∈ closureN (cube (d + 1) n) then 1 else 0 := rfl

/-- The low-face odometer is nonnegative. -/
theorem redOdoLow_nonneg (n : ℕ) (η : Site (d + 1) → ℤ) : ∀ t x, 0 ≤ redOdoLow n η t x := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [redOdoLow_zero]
    split <;> omega
  | succ t ih =>
    intro x
    have hih := ih x
    rw [redOdoLow_succ]
    split
    · exact hih
    · split
      · exact hih
      · split
        · exact hih
        · split <;> omega

/-- The low-face odometer is at most one. -/
theorem redOdoLow_le_one (n : ℕ) (η : Site (d + 1) → ℤ) : ∀ t x, redOdoLow n η t x ≤ 1 := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [redOdoLow_zero]
    split <;> omega
  | succ t ih =>
    intro x
    have hih := ih x
    rw [redOdoLow_succ]
    split
    · exact hih
    · split
      · exact hih
      · split
        · exact hih
        · split <;> omega

/-- The low-face odometer is zero or one. -/
theorem redOdoLow_zero_or_one (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (x : Site (d + 1)) :
    redOdoLow n η t x = 0 ∨ redOdoLow n η t x = 1 := by
  have hle := redOdoLow_le_one n η t x
  have hnn := redOdoLow_nonneg n η t x
  omega

/-- **The transport step for the low-face odometer.**  It is dominated by the frozen
odometer seeded on the low face, at every time and every site. -/
theorem fodo_dominates_redOdoLow (n : ℕ) (η : Site (d + 1) → ℤ) :
    ∀ t x, redOdoLow n η t x ≤
      fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) t x := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [redOdoLow_zero]
    by_cases h : x 0 = 0 ∧ x ∈ closureN (cube (d + 1) n)
    · rw [if_pos h]
      have hw : fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
          (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
            ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) 0 x
          = Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
              ⟨0, by omega⟩ false) (fun _ => (1 : ℤ)) x := rfl
      rw [hw]
      have hmem : x ∈ faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false := by
        rw [faceOut_eq_lowface]
        exact h
      rw [Set.indicator_of_mem hmem (fun _ => (1 : ℤ))]
    · rw [if_neg h]
      exact fodo_nonneg _ _ _
        (Set.indicator_nonneg (fun _ _ => zero_le_one)) 0 x
  | succ t ih =>
    intro x
    rw [redOdoLow_succ]
    by_cases hc : x ∉ cube (d + 1) n
    · rw [if_pos hc]
      exact le_trans (ih x) (fodo_mono_time' _ _ _ t (t + 1) x (by omega))
    · rw [if_neg hc]
      by_cases hlt : (1 : ℤ) < x 0
      · rw [if_pos hlt]
        exact le_trans (ih x) (fodo_mono_time' _ _ _ t (t + 1) x (by omega))
      · rw [if_neg hlt]
        by_cases h1 : redOdoLow n η t x = 1
        · rw [if_pos h1]
          have hle1 : redOdoLow n η t x ≤
              fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
                (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
                  ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) t x := ih x
          rw [h1] at hle1
          have hmono := fodo_mono_time' ((rboxShift (fun _ : Fin (d+1) => n)
            (0 : Site (d+1)))ᶜ) η
            (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
              ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) t (t + 1) x (by omega)
          omega
        · rw [if_neg h1]
          have h0 : redOdoLow n η t x = 0 := (redOdoLow_zero_or_one n η t x).resolve_right h1
          by_cases hthr : 2 * ((d : ℤ) + 1) ≤ η x + lap (redOdoLow n η t) x
          · have hstep : redOdoLow n η (t + 1) x = redOdoLow n η t x + 1 := by
              rw [redOdoLow_succ]
              rw [if_neg hc, if_neg hlt, if_neg h1, if_pos hthr]
            rw [if_pos hthr, ← hstep]
            -- the frozen odometer is at least one at `x` at time `t + 1`
            have hfodo : 1 ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n)
                (0 : Site (d+1)))ᶜ) η
                (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
                  ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (t + 1) x := by
              by_cases hf0 : fodo ((rboxShift (fun _ : Fin (d+1) => n)
                  (0 : Site (d+1)))ᶜ) η
                  (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
                    ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) t x = 0
              · -- `fodo` is still zero, so it fires at `x` too
                have hnbr : nbrSumZ (redOdoLow n η t) x ≤
                    nbrSumZ (fodo ((rboxShift (fun _ : Fin (d+1) => n)
                      (0 : Site (d+1)))ᶜ) η
                      (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
                        ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) t) x :=
                  nbrSumZ_mono (fun y => ih y) x
                have hthr' : 2 * ((d : ℤ) + 1) ≤ η x + nbrSumZ (redOdoLow n η t) x := by
                  have h := hthr
                  simp only [lap, nbrSumZ] at h ⊢
                  rw [h0] at h
                  simpa using h
                have hgoal : 2 * ((d : ℤ) + 1) ≤ η x +
                    nbrSumZ (fodo ((rboxShift (fun _ : Fin (d+1) => n)
                      (0 : Site (d+1)))ᶜ) η
                      (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
                        ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) t) x := by
                  linarith
                rw [fodo_succ]
                rw [if_neg (fun hcon => hcon (by
                  rw [rboxShift_zero_eq_cube]
                  exact not_not.mp hc))]
                rw [if_pos]
                · omega
                · simp only [fconf, lap, nbrSumZ] at hgoal ⊢
                  rw [hf0]
                  simp only [mul_zero, sub_zero]
                  omega
              · -- `fodo` is already at least one, and it is monotone in time
                have hpos : 1 ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n)
                    (0 : Site (d+1)))ᶜ) η
                    (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
                      ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) t x := by
                  have hnn := fodo_nonneg ((rboxShift (fun _ : Fin (d+1) => n)
                    (0 : Site (d+1)))ᶜ) η
                    (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
                      ⟨0, by omega⟩ false) (fun _ => (1 : ℤ)))
                    (Set.indicator_nonneg (fun _ _ => zero_le_one)) t x
                  omega
                exact le_trans hpos (fodo_mono_time' _ _ _ t (t + 1) x (by omega))
            exact le_trans (redOdoLow_le_one n η (t + 1) x) hfodo
          · have hnext : redOdoLow n η (t + 1) x = redOdoLow n η t x := by
              rw [redOdoLow_succ]
              rw [if_neg hc, if_neg hlt, if_neg h1, if_neg hthr]
              ring
            rw [if_neg hthr, h0, zero_add]
            exact fodo_nonneg _ _ _
              (Set.indicator_nonneg (fun _ _ => zero_le_one)) (t + 1) x

/-- Above layer `1` the low-face odometer is frozen at its initial value. -/
theorem redOdoLow_cons_high (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) (a : ℤ)
    (ha : 1 < a) : redOdoLow n η t (cons a y) = redOdoLow n η 0 (cons a y) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [redOdoLow_succ]
    by_cases hc : cons a y ∉ cube (d + 1) n
    · rw [if_pos hc]; exact ih
    · rw [if_neg hc, if_pos (by simpa [cons] using ha)]
      exact ih

/-- Two layers above the floor the low-face odometer is zero. -/
theorem redOdoLow_cons_high_zero (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) (a : ℤ)
    (ha : 1 < a) : redOdoLow n η t (cons a y) = 0 := by
  rw [redOdoLow_cons_high n η t y a ha, redOdoLow_zero]
  rw [if_neg]
  rintro ⟨h0, -⟩
  simp only [cons, Fin.cons_zero] at h0
  omega

/-- The low face of the box is lit in the low-face odometer. -/
theorem redOdoLow_floor (n : ℕ) (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d)
    (hy : cons 0 y ∈ closureN (cube (d + 1) n)) : redOdoLow n η t (cons 0 y) = 1 := by
  induction t with
  | zero =>
    rw [redOdoLow_zero, if_pos]
    exact ⟨rfl, hy⟩
  | succ t ih =>
    rw [redOdoLow_succ]
    by_cases hc : cons 0 y ∉ cube (d + 1) n
    · rw [if_pos hc]; exact ih
    · rw [if_neg hc]
      rw [if_neg (by simp only [cons, Fin.cons_zero]; omega)]
      rw [if_pos ih]
      exact ih

/-- **The low-face reduction.**  On layer `1`, the low-face constrained odometer equals the
`d`-dimensional constrained odometer of the background `η(1, ·) - 1`. -/
theorem redOdoLow_agree (n : ℕ) (hn : 1 ≤ n) (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) :
    redOdoLow n η t (cons 1 y) = redOdoDownAt 0 n η t y := by
  induction t generalizing y with
  | zero =>
    rw [redOdoLow_zero, redOdoDownAt_zero]
    rw [if_neg]
    rintro ⟨h0, -⟩
    simp only [cons, Fin.cons_zero] at h0
    omega
  | succ t ih =>
    rw [redOdoLow_succ, redOdoDownAt_succ]
    have hmem : (cons (1 : ℤ) y ∉ cube (d + 1) n) ↔ (y ∉ cube d n) := by
      have h := mem_cube_cons_succ (i := 0) (d := d) (n := n) (by omega) (by omega) y
      rw [show (0 : ℤ) + 1 = 1 from by ring] at h
      exact not_congr h
    have hnot : ¬ ((1 : ℤ) < (cons (1 : ℤ) y) 0) := by
      simp only [cons, Fin.cons_zero]; omega
    rw [if_neg hnot]
    by_cases hy : y ∉ cube d n
    · rw [if_pos (hmem.mpr hy), if_pos hy]
      exact ih y
    · rw [if_neg (fun h => hy (hmem.mp h)), if_neg hy]
      by_cases h1 : redOdoDownAt 0 n η t y = 1
      · rw [if_pos h1]
        rw [if_pos (by rw [ih y]; exact h1)]
        exact ih y
      · rw [if_neg h1]
        rw [if_neg (by rw [ih y]; exact h1)]
        have hhigh : redOdoLow n η t (cons (1 + 1) y) = 0 :=
          redOdoLow_cons_high_zero n η t y (1 + 1) (by omega)
        have hfloor : redOdoLow n η t (cons (1 - 1) y) = 1 := by
          rw [show (1 : ℤ) - 1 = 0 from by ring]
          exact redOdoLow_floor n η t y (by
            rw [closureN, Set.mem_union]
            right
            refine ⟨?_, ?_⟩
            · intro hcon
              have h0 := hcon 0
              simp only [cons, Fin.cons_zero] at h0
              omega
            · refine ⟨cons 1 y, (mem_cube_cons_succ (i := 0) (by omega) (by omega) y).mpr
                (not_not.mp hy), ?_⟩
              exact ⟨0, Or.inl (by
                funext j
                refine Fin.cases ?_ ?_ j
                · simp only [cons, Fin.cons_zero, Pi.add_apply, unit, Pi.single_eq_same]
                  norm_num
                · intro k
                  simp only [cons, Fin.cons_succ, Pi.add_apply, unit,
                    Pi.single_eq_of_ne (Fin.succ_ne_zero k)]
                  ring)⟩)
        have hlap : lap (redOdoLow n η t) (cons 1 y)
            = 1 + lap (redOdoDownAt 0 n η t) y - 2 * redOdoDownAt 0 n η t y := by
          simp only [lap, nbrSumZ_cons]
          rw [hhigh, hfloor]
          simp only [nbrSumZ]
          rw [Finset.sum_congr rfl (fun w _ => by rw [ih (y + unit w), ih (y - unit w)]),
            ih y]
          push_cast
          ring
        have h0 : redOdoDownAt 0 n η t y = 0 :=
          (redOdoDownAt_zero_or_one η t y).resolve_right h1
        rw [ih y, h0, hlap]
        rw [show (0 : ℤ) + 1 = 1 from by ring]
        congr 1
        by_cases h : 2 * (d : ℤ) ≤ η (cons 1 y) - 1 + lap (redOdoDownAt 0 n η t) y
        · rw [if_pos h, if_pos (by linarith)]
        · rw [if_neg h, if_neg (by linarith)]

/-- The layer chain: if every layer of the box is internally spanned, the frozen odometer
seeded on the low face topples the whole box by time `n ^ (d + 1)`. -/
theorem fodo_topples_box_of_layers (n : ℕ) (hn : 1 ≤ n) (η : Site (d + 1) → ℤ)
    (hspan : ∀ i ∈ Finset.Icc 1 n,
      InternallySpanned (fun w : Site d => η (cons (i : ℤ) w) - 1) n) :
    ∀ x ∈ cube (d + 1) n,
      1 ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (n ^ (d + 1)) x := by
  -- the layer chain: layer i topples by time i * n ^ d
  have hlayer : ∀ i ∈ Finset.Icc 1 n, ∀ y ∈ cube d n,
      1 ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (i * n ^ d) (cons (i : ℤ) y) := by
    intro i hi
    induction i with
    | zero => exact absurd (Finset.mem_Icc.mp hi).1 (by omega)
    | succ k ih =>
      intro y hy
      by_cases hk : k = 0
      · subst hk
        -- layer 1: the low-face odometer at floor 0, dominated by `fodo`
        obtain ⟨T₀, hT₀le, hT₀⟩ := exists_uniform_span_time_le n
          (fun w : Site d => η (cons (1 : ℤ) w) - 1)
          (hspan 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩))
        have hred : redOdoLow n η T₀ (cons (0 + 1) y) = 1 := by
          rw [show (0 : ℤ) + 1 = 1 from by ring]
          rw [redOdoLow_agree n hn η T₀ y, redOdoDownAt_eq_spanOdo]
          exact hT₀ y hy
        have hdom := fodo_dominates_redOdoLow n η T₀ (cons (0 + 1) y)
        rw [hred] at hdom
        have hmono := fodo_mono_time' ((rboxShift (fun _ : Fin (d+1) => n)
          (0 : Site (d+1)))ᶜ) η
          (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
            ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) T₀ (1 * n ^ d) (cons 1 y)
          (by
            have hTle : T₀ ≤ n ^ d := hT₀le
            rw [one_mul]
            exact hTle)
        exact le_trans hdom hmono
      · -- layer k+1: the inductive hypothesis at layer k
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
        have hkn : k ≤ n := by
          have := (Finset.mem_Icc.mp hi).2
          omega
        have hkIcc : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hk1, hkn⟩
        obtain ⟨T₀, hT₀le, hT₀⟩ := exists_uniform_span_time_le n
          (fun w : Site d => η (cons ((k : ℤ) + 1) w) - 1) (hspan (k + 1) hi)
        have hred : redOdoUpAt (k : ℤ) n η T₀ (cons ((k : ℤ) + 1) y) = 1 := by
          have hcastn : (k : ℤ) + 1 ≤ (n : ℤ) := by
            have hk' : k + 1 ≤ n := (Finset.mem_Icc.mp hi).2
            exact_mod_cast hk'
          rw [redOdoUpAt_agree η (by omega) (by omega) hcastn T₀ y,
            redOdoDownAt_eq_spanOdo]
          exact hT₀ y hy
        have hT : ∀ z ∈ cube d n, 1 ≤ fodo ((rboxShift (fun _ : Fin (d+1) => n)
            (0 : Site (d+1)))ᶜ) η
            (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
              ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (k * n ^ d) (cons (k : ℤ) z) :=
          fun z hz => ih hkIcc z hz
        have hdom := fodo_dominates_redOdoUpAt (d := d) n η (k : ℤ) (k * n ^ d)
          hT T₀ (cons ((k : ℤ) + 1) y)
        rw [hred] at hdom
        have hmono := fodo_mono_time' ((rboxShift (fun _ : Fin (d+1) => n)
          (0 : Site (d+1)))ᶜ) η
          (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
            ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (k * n ^ d + T₀) ((k + 1) * n ^ d)
          (cons ((k : ℤ) + 1) y) (by
            have hTle : T₀ ≤ n ^ d := hT₀le
            calc k * n ^ d + T₀ ≤ k * n ^ d + n ^ d := Nat.add_le_add_left hTle _
              _ = (k + 1) * n ^ d := by ring)
        exact le_trans hdom hmono
  -- assemble: every site of the box lies in some layer
  intro x hx
  have hx0 : 1 ≤ x 0 := (hx 0).1
  have hxn : x 0 ≤ (n : ℤ) := (hx 0).2
  set i : ℕ := (x 0).toNat with hi
  have hicast : (i : ℤ) = x 0 := Int.toNat_of_nonneg (by omega)
  have hiIcc : i ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hxeq : x = cons (i : ℤ) (fun l => x l.succ) := by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp only [cons, Fin.cons_zero]; exact hicast.symm
    · intro l; simp [cons]
  have hmem : (fun l => x l.succ) ∈ cube d n := by
    intro l
    have h := hx l.succ
    simpa [cons] using h
  rw [hxeq]
  have hlayer' := hlayer i hiIcc (fun l => x l.succ) hmem
  have hmono := fodo_mono_time' ((rboxShift (fun _ : Fin (d+1) => n)
    (0 : Site (d+1)))ᶜ) η
    (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
      ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (i * n ^ d) (n ^ (d + 1))
    (cons (i : ℤ) (fun l => x l.succ)) (by
      have hi_le : i ≤ n := (Finset.mem_Icc.mp hiIcc).2
      calc i * n ^ d ≤ n * n ^ d := Nat.mul_le_mul_right _ hi_le
        _ = n ^ (d + 1) := by ring)
  exact le_trans hlayer' hmono

/-- **The box-crossing core.**  If every layer of the box is internally spanned, the frozen
odometer seeded on the low face topples the whole box by time `n ^ (d + 1)`. -/
theorem box_crossing_core (n : ℕ) (hn : 1 ≤ n) (η : Site (d + 1) → ℤ)
    (hspan : ∀ i ∈ Finset.Icc 1 n,
      InternallySpanned (fun w : Site d => η (cons (i : ℤ) w) - 1) n) :
    CrossedInDirection η (fun _ : Fin (d + 1) => n) (0 : Site (d + 1))
      ⟨0, by omega⟩ false := by
  intro t ht x hx
  rw [rboxShift_zero_eq_cube] at hx
  have hbox := fodo_topples_box_of_layers n hn η hspan x hx
  have hmono := fodo_mono_time' ((rboxShift (fun _ : Fin (d+1) => n)
    (0 : Site (d+1)))ᶜ) η
    (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
      ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (n ^ (d + 1)) t x (by
      have hprod : (∏ l : Fin (d + 1), n) = n ^ (d + 1) := by
        simp [Finset.prod_const, Finset.card_univ]
      rw [hprod] at ht
      exact ht)
  exact le_trans hbox hmono

/-- The restriction of the product measure to a layer is again a product measure. -/
theorem layer_restrict_eq (d : ℕ) (ν : MeasureTheory.Measure ℤ)
    (hν : MeasureTheory.IsProbabilityMeasure ν) (i : ℤ) :
    (MeasureTheory.Measure.infinitePi fun _ : Site (d + 1) => ν).map
        (fun η : Site (d + 1) → ℤ => fun w : Site d => η (cons i w))
      = MeasureTheory.Measure.infinitePi fun _ : Site d => ν := by
  have hinj : Function.Injective (fun w : Site d => cons i w) := by
    intro a b h
    funext l
    have := congrFun h l.succ
    simpa [cons] using this
  haveI := hν
  have h := MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Site (d + 1) => ν) (f := fun w : Site d => cons i w) hinj
  simpa using h

/-- The one-site law of the layer, for the two-point law `chipLaw (2d-1) d p₀`: shifting
down by one gives `chipLaw (2d-2) (d-1) p₀`. -/
theorem layer_one_site_law (d : ℕ) (p : ℝ) :
    (chipLaw (2 * (d : ℤ) - 1) (d : ℤ) p).map (fun m : ℤ => m - 1)
      = chipLaw (2 * (d : ℤ) - 2) ((d : ℤ) - 1) p := by
  rw [chipLaw, chipLaw]
  ext s hs
  rw [MeasureTheory.Measure.map_apply (by fun_prop : Measurable (fun m : ℤ => m - 1)) hs]
  rw [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.smul_apply]
  have hpre : (fun m : ℤ => m - 1) ⁻¹' s = (fun m : ℤ => m + 1) '' s := by
    ext m
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hm
      exact ⟨m - 1, hm, by ring⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hpre]
  rw [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.smul_apply]
  simp only [MeasureTheory.Measure.dirac_apply]
  by_cases h1 : (2 * (d : ℤ) - 2) ∈ s <;> by_cases h2 : ((d : ℤ) - 1) ∈ s
  · have h3 : (2 * (d : ℤ) - 1) ∈ (fun m : ℤ => m + 1) '' s :=
      ⟨2 * (d : ℤ) - 2, h1, by ring⟩
    have h4 : (d : ℤ) ∈ (fun m : ℤ => m + 1) '' s :=
      ⟨(d : ℤ) - 1, h2, by ring⟩
    simp only [Set.indicator_of_mem h3, Set.indicator_of_mem h4,
      Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply]
  · have h3 : (2 * (d : ℤ) - 1) ∈ (fun m : ℤ => m + 1) '' s :=
      ⟨2 * (d : ℤ) - 2, h1, by ring⟩
    have h4 : (d : ℤ) ∉ (fun m : ℤ => m + 1) '' s := by
      rintro ⟨y, hy, hyeq⟩
      exact h2 (by
        have h5 : y = (d : ℤ) - 1 := by
          simp only at hyeq
          omega
        rw [h5] at hy
        exact hy)
    simp only [Set.indicator_of_mem h3, Set.indicator_of_notMem h4,
      Set.indicator_of_mem h1, Set.indicator_of_notMem h2, Pi.one_apply]
  · have h3 : (2 * (d : ℤ) - 1) ∉ (fun m : ℤ => m + 1) '' s := by
      rintro ⟨y, hy, hyeq⟩
      exact h1 (by
        have h5 : y = 2 * (d : ℤ) - 2 := by
          simp only at hyeq
          omega
        rw [h5] at hy
        exact hy)
    have h4 : (d : ℤ) ∈ (fun m : ℤ => m + 1) '' s :=
      ⟨(d : ℤ) - 1, h2, by ring⟩
    simp only [Set.indicator_of_notMem h3, Set.indicator_of_mem h4,
      Set.indicator_of_notMem h1, Set.indicator_of_mem h2, Pi.one_apply]
  · have h3 : (2 * (d : ℤ) - 1) ∉ (fun m : ℤ => m + 1) '' s := by
      rintro ⟨y, hy, hyeq⟩
      exact h1 (by
        have h5 : y = 2 * (d : ℤ) - 2 := by
          simp only at hyeq
          omega
        rw [h5] at hy
        exact hy)
    have h4 : (d : ℤ) ∉ (fun m : ℤ => m + 1) '' s := by
      rintro ⟨y, hy, hyeq⟩
      exact h2 (by
        have h5 : y = (d : ℤ) - 1 := by
          simp only at hyeq
          omega
        rw [h5] at hy
        exact hy)
    simp only [Set.indicator_of_notMem h3, Set.indicator_of_notMem h4,
      Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

end ReductionShift

end Exploding
