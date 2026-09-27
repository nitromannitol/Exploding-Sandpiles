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
    (hT : ∀ y ∈ cube d n, fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
      (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
        (fun _ => (1 : ℤ))) T (cons i y) = 1) :
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
      rw [show T + 0 = T from rfl, hT (fun l => x l.succ) hmem']
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

end ReductionShift

end Exploding
