/-
Upper bounds on the arrival times `T(n e₁)` of the counterexample background of
`paper/exploding.tex` Section 6: a comparison principle for parallel toppling
(`cel_subsol`) by which an explicit legal toppling schedule bounds the parallel
odometer from below.
-/
import Exploding.Support.SubRelay

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- **Schedule comparison.**  A time-indexed family `p` which starts at `0` (or
below) and whose increments are always legal (`p_{t+1}(x) ≤ p_t(x) + 1` and the
increment occurs only at a site that is unstable for the sandpile
`s₀ + Δ p_t`) lies below the parallel toppling odometer. -/
theorem cel_subsol (s0 : Site d → ℤ) (p : ℕ → Site d → ℤ)
    (h0 : ∀ x, p 0 x ≤ 0)
    (hstep : ∀ t x, p (t + 1) x ≤
      p t x + (if 2 * (d : ℤ) ≤ s0 x + lap (p t) x then 1 else 0)) :
    ∀ t x, p t x ≤ podo s0 t x := by
  intro t
  induction t with
  | zero => intro x; simpa using h0 x
  | succ t ih =>
    intro x
    rw [podo_succ]
    have hs := hstep t x
    have hx := ih x
    have hind : (0 : ℤ) ≤ (if 2 * (d : ℤ) ≤ pconf s0 t x then 1 else 0) := by
      split <;> norm_num
    have hind' : (if 2 * (d : ℤ) ≤ s0 x + lap (p t) x then (1 : ℤ) else 0) ≤ 1 := by
      split <;> norm_num
    by_cases hlt : p t x < podo s0 t x
    · linarith
    · have heq : p t x = podo s0 t x := le_antisymm hx (not_lt.mp hlt)
      by_cases hc : 2 * (d : ℤ) ≤ s0 x + lap (p t) x
      · have hmono : nbrSumZ (p t) x ≤ nbrSumZ (podo s0 t) x :=
          nbrSumZ_mono (fun y => ih y) x
        have hc' : 2 * (d : ℤ) ≤ pconf s0 t x := by
          unfold pconf lap
          unfold lap at hc
          rw [← heq]
          linarith
        rw [if_pos hc']
        rw [if_pos hc] at hs
        linarith
      · rw [if_neg hc] at hs
        linarith

end Exploding
