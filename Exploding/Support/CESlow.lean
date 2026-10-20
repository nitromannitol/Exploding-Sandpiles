/-
The slow front of the counterexample background of `paper/corrected-arxiv/exploding-corrected-arxiv.tex` Section 6,
Step 4: an explicit supersolution for parallel toppling.

A time-indexed family `w` which is nondecreasing in time, starts nonnegative, and
increases at every site that is unstable for the sandpile `s₀ + Δ w_t` dominates the
parallel toppling odometer (`cels_supsol`).  On the reflected cylinder, the odometer of
the pile `η̂` is explicit: after the first wave, every site topples with period `4`
(`cels_W`), and the toppling times repeat with period `4` in space and `6` in time
(`cels_tau`).  The unstable-implies-increases condition is a finite check
(`cels_ok`), verified by computation near the wall and propagated by the translations
`(c, t) ↦ (c, t + 4)` and `(c, t) ↦ (c + 4, t + 6)`.
-/
import Exploding.Support.CELow4

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- **Supersolution comparison.**  A nondecreasing, nonnegative-start family which
increases at every unstable site dominates the parallel toppling odometer. -/
theorem cels_supsol (s0 : Site d → ℤ) (w : ℕ → Site d → ℤ)
    (h0 : ∀ x, 0 ≤ w 0 x)
    (hmono : ∀ t x, w t x ≤ w (t + 1) x)
    (hstep : ∀ t x, 2 * (d : ℤ) ≤ s0 x + lap (w t) x → w t x + 1 ≤ w (t + 1) x) :
    ∀ t x, podo s0 t x ≤ w t x := by
  intro t
  induction t with
  | zero => intro x; simpa using h0 x
  | succ t ih =>
    intro x
    rw [podo_succ]
    have hx := ih x
    have hm := hmono t x
    by_cases hlt : podo s0 t x < w t x
    · have hind : (if 2 * (d : ℤ) ≤ pconf s0 t x then (1 : ℤ) else 0) ≤ 1 := by
        split <;> norm_num
      linarith
    · have heq : podo s0 t x = w t x := le_antisymm hx (not_lt.mp hlt)
      by_cases hc : 2 * (d : ℤ) ≤ pconf s0 t x
      · have hmono' : nbrSumZ (podo s0 t) x ≤ nbrSumZ (w t) x :=
          nbrSumZ_mono (fun y => ih y) x
        have hc' : 2 * (d : ℤ) ≤ s0 x + lap (w t) x := by
          unfold pconf lap at hc
          unfold lap
          rw [← heq]
          linarith
        have := hstep t x hc'
        rw [if_pos hc]
        linarith
      · rw [if_neg hc]
        linarith

end Exploding
