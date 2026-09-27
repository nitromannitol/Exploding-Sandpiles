/-
The remaining assembly of `aux_box_crossing_core`.

FINDING (2026-09-27, route correction).  The domination
`redOdoUpAt i n η t x ≤ fodo (rboxShift …)ᶜ η (indicator (faceOut …) 1) t x`
is FALSE for `i ≥ 1`: at `t = 0` the left side is `1` on the whole layer `i`
(`redOdoUpAt_zero`), while the right side is the indicator of the low face
`faceOut … ⟨0,_⟩ false`, which is `0` off that face — and layer `i ≥ 1` is off
it.  So the layer chain cannot be run by dominating each layer's own
`redOdoUpAt` process by the single `fodo` seeded at the low face.

The correct route, which the proved ingredients support, is instead:

1. `layer_topples` (in `Exploding/Support/ReductionShift.lean`) gives, for each
   layer `i` with `0 ≤ i` and `i + 1 ≤ n`, a uniform time at which layer `i + 1`
   is fully toppled in the `redOdoUpAt i` process, once layer `i` is permanently
   lit and the layer's shadow is internally spanned (`hspan`).
2. `redOdoUpAt_floor` supplies the permanent lighting of the floor at each stage.
3. `fodo_mono_time` (same file) gives the monotonicity in time that transports a
   toppling at one time to all later times.

What is still needed is the *transport* step: from "layer `i` is fully toppled in
`fodo` at time `T`" conclude "layer `i + 1` is fully toppled in `fodo` at some
later time".  That is a comparison between `fodo` and `redOdoUpAt i` in which the
floor of the latter is the already-toppled layer `i` of the former — i.e. the
domination above restricted to the sites ABOVE layer `i`, with the floor's
lighting supplied by the inductive hypothesis rather than by the seed.  The
statement to prove is therefore

    ∀ t x, i < x 0 → redOdoUpAt i n η t x ≤
      fodo ((rboxShift (fun _ : Fin (d+1) => n) (0 : Site (d+1)))ᶜ) η
        (Set.indicator (faceOut … ⟨0,_⟩ false) (fun _ => (1 : ℤ))) (T + t) x

for `T` a time at which layer `i` is already toppled in `fodo`; the hypothesis
`i < x 0` is what makes the base case true (the seed covers layer `0`, and the
inductive hypothesis covers layer `i`).

The seed (`cons_zero_mem_faceOut`) and the layer step (`layer_topples`) are both
proved and in the package; only this transport remains.
-/
import Exploding.Support.ReductionShift
open Exploding LatticeProb MeasureTheory
open scoped Classical
variable {d : ℕ}

/-- The transport step described above. -/
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
      sorry
    · rw [if_neg hxi]
      sorry
  | succ t ih =>
    intro x hx
    sorry
