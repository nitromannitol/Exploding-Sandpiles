/-
The transport step of the box-crossing layer induction.

The domination `redOdoUpAt i n η t x ≤ fodo (rboxShift …)ᶜ η (indicator (faceOut …) 1) t x`
is FALSE for `i ≥ 1` (at `t = 0` the left side is `1` on the whole layer `i`, the right side
is `0` off the low face).  The corrected statement below restricts the domination to the
sites above layer `i` (`i < x 0`) and shifts the time by `T`, a time at which layer `i` is
already toppled in `fodo`.

Proved: the base case (both branches) and the step leaf (a) (`x ∉ cube (d+1) n`, via
`fodo_mono_time'`).  Remaining:
  (b) `hle : x 0 ≤ i` — the site is at or below the floor, so `redOdoUpAt` freezes it at its
      initial value, which is `1` exactly on layer `i`; the floor's lighting is `hT`, and
      `fodo_mono_time'` carries it from `T` to `T + (t + 1)`.  (The draft below tries to
      close this with `fodo_le_one`, which does NOT apply: `fodo_le_one` needs
      `s0 ≤ 2d - 1`, and here `s0 = η` is unbounded.  The right route is `hT` plus
      `fodo_mono_time'`.)
  (c) `h1 : redOdoUpAt i n η t x = 1` — absorption at one, transported by `fodo_mono_time'`.
  (d) the firing case — the threshold comparison, using `nbrSumZ_mono` on the inductive
      hypothesis and `fodo`'s own recursion.
-/
import Exploding.Support.ReductionShift
import Exploding.Support.SubFodo
open Exploding LatticeProb MeasureTheory
open scoped Classical
variable {d : ℕ}

/-- The transport step: above layer `i`, the layer-`i` constrained odometer is dominated by
the frozen odometer, once layer `i` is already toppled in the latter. -/
theorem fodo_dominates_redOdoUpAt_above (n : ℕ) (hn : 1 ≤ n) (η : Site (d + 1) → ℤ)
    (i : ℤ) (hi0 : 0 ≤ i) (hi : i + 1 ≤ (n : ℤ)) (T : ℕ)
    (hT : ∀ y ∈ cube d n, fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
      (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
        (fun _ => (1 : ℤ))) T (cons i y) = 1) :
    ∀ t x, i < x 0 → redOdoUpAt i n η t x ≤
      fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
          (fun _ => (1 : ℤ))) (T + t) x := by
  intro t
  induction t with
  | zero =>
    intro x hx
    rw [redOdoUpAt_zero]
    by_cases hxi : x 0 = i
    · rw [if_pos hxi]
      have hxeq : x = cons i (fun l => x l.succ) := by
        funext j
        refine Fin.cases ?_ ?_ j
        · simpa [cons] using hxi
        · intro k; simp [cons]
      rw [hxeq]
      have hmem : (fun l => x l.succ) ∈ cube d n := by
        intro l
        have hxl := hx
        sorry
      have hT0 : fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
          (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
            (fun _ => (1 : ℤ))) (T + 0) (cons i (fun l => x l.succ)) = 1 :=
        hT (fun l => x l.succ) hmem
      rw [hT0]
    · rw [if_neg hxi]
      exact fodo_nonneg _ _ _
        (Set.indicator_nonneg (fun _ _ => zero_le_one)) (T + 0) x
  | succ t ih =>
    intro x hx
    rw [redOdoUpAt_succ]
    by_cases hc : x ∉ cube (d + 1) n
    · rw [if_pos hc]
      exact le_trans (ih x hx) (fodo_mono_time' _ _ _ (T + t) (T + (t + 1)) x (by omega))
    · rw [if_neg hc]
      by_cases hle : x 0 ≤ i
      · rw [if_pos hle]
        have hxeq : x = cons i (fun l => x l.succ) := by
          funext j
          refine Fin.cases ?_ ?_ j
          · simp only [cons, Fin.cons_zero]
            omega
          · intro k; simp [cons]
        rw [hxeq]
        have hmem : (fun l => x l.succ) ∈ cube d n := by
          intro l
          have hxl := hx
          sorry
        have hT0 : fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
            (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
              (fun _ => (1 : ℤ))) (T + (t + 1)) (cons i (fun l => x l.succ)) = 1 := by
          have h1 := hT (fun l => x l.succ) hmem
          have h2 := fodo_mono_time' ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
            (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
              (fun _ => (1 : ℤ))) T (T + (t + 1)) (cons i (fun l => x l.succ)) (by omega)
          have h3 : fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
              (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1)) ⟨0, by omega⟩ false)
                (fun _ => (1 : ℤ))) (T + (t + 1)) (cons i (fun l => x l.succ)) ≤ 1 := by
            rw [h1]
            exact le_rfl
          omega
        rw [hT0]
      · rw [if_neg hle]
        by_cases h1 : redOdoUpAt i n η t x = 1
        · rw [if_pos h1]
          sorry
        · rw [if_neg h1]
          sorry
