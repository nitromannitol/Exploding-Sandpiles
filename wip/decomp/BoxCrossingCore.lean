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

REMAINING, precisely.  The layer chain needs the bridge
`redOdoUpAt 0 n η t x = redOdoUp n η t x` for `x ∈ cube (d+1) n`, and that bridge is
FALSE.  `redOdoUp` (Reduction.lean) lights its floor at layer `0` EVERYWHERE, including
outside the cube, while `redOdoUpAt 0` lights it only inside the cube (the initial value is
`if x 0 = 0 ∧ x ∈ cube then 1 else 0`).  At `t = 1` and `x ∈ cube` with `x 0 = 1`, the
neighbour at `x - e_0` has layer `0` and lies outside the cube, so it contributes `1` to
`lap (redOdoUp …) x` and `0` to `lap (redOdoUpAt 0 …) x`: the two Laplacians differ by `1`
and the two processes fire at different thresholds.  The bridge is therefore not an
identity, and the layer chain must be run entirely inside the `redOdoUpAt` family (which is
what `layer_topples` already does) rather than by transporting to `redOdoUp`.

What is proved and in the package: the seed (`cons_zero_mem_faceOut`), the layer step
(`layer_topples`, with `redOdoUpAt_floor` supplying the permanent lighting of each floor),
time monotonicity (`fodo_mono_time`, `fodo_mono_time'`), the firing case
(`fodo_fires_of_redOdoUpAt`), the transport step
(`fodo_dominates_redOdoUpAt`, the whole of the layer induction's domination), and the
uniform span time (`exists_uniform_span_time`, `spanOdo_mono_le`).  Chaining the layers
with `fodo_dominates_redOdoUpAt` at each floor and unfolding `CrossedInDirection` is what
remains.
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
