/-
The transport step of the box-crossing layer induction, assembled.

The domination `redOdoUpAt i n η t x ≤ fodo (rboxShift …)ᶜ η (indicator (faceOut …) 1) t x`
is FALSE for `i ≥ 1` (at `t = 0` the left side is `1` on the whole layer `i`, the right side
is `0` off the low face).  The corrected statement below restricts the domination to the
sites above layer `i` (`i < x 0`) and shifts the time by `T`, a time at which layer `i` is
already toppled in `fodo`.

All four step leaves are proved in `Exploding/Support/ReductionShift.lean`
(`fodo_fires_of_redOdoUpAt` is the firing case; the other three are inline below), and the
base case is proved.

REMAINING, precisely.  Chain the layers.  The natural statement is

```
theorem fodo_topples_box_of_layers (n : ℕ) (hn : 1 ≤ n) (η : Site (d + 1) → ℤ)
    (hspan : ∀ i ∈ Finset.Icc 1 n,
      InternallySpanned (fun w : Site d => η (cons (i : ℤ) w) - 1) n) :
    ∀ x ∈ cube (d + 1) n,
      1 ≤ fodo (rboxShift (fun _ => n) 0)ᶜ η (indicator (faceOut …) 1) (n ^ (d+1)) x
```

proved by induction on the layer index `i`, with layer `i` toppling by time `i * n ^ d`.

**The base case is the whole difficulty, and the reason is structural.**  `redOdoUpAt 0`
lights its floor at `x 0 = 0 ∧ x ∈ cube (d+1) n`, and `cube (d+1) n` requires `1 ≤ x 0`, so
that set is EMPTY: `redOdoUpAt 0` starts at zero everywhere and is useless for the box.  The
floor of layer `1` is layer `0`, which lies OUTSIDE the cube (it is the low face
`faceOut … ⟨0, …⟩ false`).  So the base case must use `redOdoUp` (whose floor at layer `0` is
lit everywhere, including outside the cube), and the induction invariant must therefore be
the box TOGETHER WITH its low face:

```
def lowSet (n : ℕ) : Set (Site (d + 1)) :=
  cube (d + 1) n ∪ {x | x 0 = 0 ∧ (fun l => x l.succ) ∈ cube d n}
```

with `nbr_mem_lowSet` (every neighbour of a point of `lowSet` lies in `lowSet`) and
`fodo_dominates_redOdoUp_on_lowSet` (the floor-`0` transport step on `lowSet`).  Both are
stated in `scratch/try381.lean`; the pieces they need are proved:
`mem_faceOut_of_low` (a point of the low face lies in `faceOut`), `redOdoUp_lowface`
(`redOdoUp` is `1` on the low face at every time), `fodo_lowface` (`fodo` is `1` there at
time `0`), and the counting bound `spanOdo_topples_by_ncard` /
`exists_uniform_span_time_le` (in the package) giving `T₀ ≤ n ^ d`.

The remaining work in the base case is the firing branch of
`fodo_dominates_redOdoUp_on_lowSet`: at a site `x` of the box where `redOdoUp` fires, the
frozen odometer must fire too, which needs the neighbour sum of `redOdoUp` at `x` to be
dominated by that of `fodo` — and that is exactly `nbr_mem_lowSet` plus the inductive
hypothesis at the neighbours.  With the base case done, the step case is the already-proved
`fodo_dominates_redOdoUpAt` at floor `i` with `layer_topples` supplying
`redOdoUpAt i n η T₀ (cons (i+1) y) = 1`, and the arithmetic `T + T₀ ≤ (i+1) * n ^ d` closes
with `T₀ ≤ n ^ d`.  Then unfold `CrossedInDirection` and bound the total time by `n ^ (d+1)`.
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
          omega
        rw [hT0]
        exact redOdoUpAt_le_one n η i t (cons i (fun l => x l.succ))
      · rw [if_neg hle]
        by_cases h1 : redOdoUpAt i n η t x = 1
        · rw [if_pos h1]
          have hle1 : redOdoUpAt i n η t x ≤
              fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
                (Set.indicator (faceOut (fun _ : Fin (d+1) => n) (0 : Site (d+1))
                  ⟨0, by omega⟩ false) (fun _ => (1 : ℤ))) (T + t) x := ih x hx
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
          · exact fodo_fires_of_redOdoUpAt n η i T t x (fun y => ih y (by omega)) h0 (not_not.mp hc) hthr
          · have hnext : redOdoUpAt i n η (t + 1) x = redOdoUpAt i n η t x := by
              rw [redOdoUpAt_succ]
              rw [if_neg hc, if_neg hle, if_neg h1, if_neg hthr]
              split_ifs <;> ring
            rw [hnext, h0]
            exact fodo_nonneg _ _ _
              (Set.indicator_nonneg (fun _ _ => zero_le_one)) (T + (t + 1)) x
