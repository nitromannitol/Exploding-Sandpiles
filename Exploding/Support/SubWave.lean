/-
The comparison of Section 4 of `paper/exploding.tex`: off the frozen set, the
frozen parallel toppling odometer dominates the last wave.

This is the paper's `u'_t |_{P(0)^c} ≥ u_t |_{P(0)^c}`: the frozen odometer
starts at `1` on the frozen set and at `0` off it, the background is at most the
frozen sandpile, and the wave is at most `1` on the inner boundary of the frozen
set.
-/
import Exploding.Support.SubNbr
import Exploding.Support.SubArithPos
import Exploding.Support.SubArithNeg
import Exploding.Support.SubFodo
import Exploding.Support.SubFConf

set_option linter.unusedVariables false

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- Off the frozen set, the frozen odometer dominates the wave: the induction of
the paper's check of `(4.1)`. -/
theorem wave_le_fodo (S : Set (Site d)) (s0 w0 : Site d → ℤ) (η : Site d → ℤ)
    (hd : 1 ≤ d) (n : ℕ) (z : Site d)
    (hS : ∀ x, x ∉ S → w0 x = 0)
    (hw0 : ∀ x, w0 x ≤ 1) (hw0nn : ∀ x, 0 ≤ w0 x)
    (hw0b : ∀ x ∈ innerBoundary S, 1 ≤ w0 x)
    (hs0 : ∀ x, s0 x ≤ 2 * (d : ℤ) - 1)
    (hη : ∀ x, η x ≤ s0 x)
    (hz : z ∈ S) (hn : (n : ℤ) ≤ w0 z)
    (hbd : ∀ t : ℕ, ∀ y ∈ innerBoundary S, wave η n z t y ≤ 1)
    (t : ℕ) {x : Site d} (hx : x ∉ S) :
    wave η n z t x ≤ fodo S s0 w0 t x := by
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
    linarith
  induction t generalizing x with
  | zero =>
    have hxz : x ≠ z := fun h => hx (h ▸ hz)
    simp [wave_zero, hxz, hS x hx]
  | succ t ih =>
    have hxz : x ≠ z := fun h => hx (h ▸ hz)
    rw [wave_of_ne η n z x t hxz, fodo_succ, if_neg hx]
    have hBA : nbrSumZ (wave η n z t) x + η x ≤ nbrSumZ (fodo S s0 w0 t) x + s0 x := by
      have h1 : nbrSumZ (wave η n z t) x ≤ nbrSumZ (fodo S s0 w0 t) x := by
        refine nbrSumZ_le_of_adj _ _ x ?_
        intro y hy
        by_cases hyS : y ∈ S
        · have hb : y ∈ innerBoundary S := ⟨hyS, x, hx, hy⟩
          rw [fodo_of_mem S s0 w0 t hyS]
          linarith [hbd t y hb, hw0b y hb]
        · exact ih hyS
      linarith [hη x]
    have hA := nbrSumZ_add_s0_le S s0 w0 hs0 hw0 hw0nn t x
    have hw0' := fodo_nonneg S s0 w0 hw0nn t x
    have hw1' := fodo_le_one S s0 w0 hs0 hw0 hw0nn t x
    by_cases hc : 2 * (d : ℤ) ≤ fconf S s0 w0 t x
    · rw [if_pos hc]
      exact Exploding.ediv_step_ge_pos d hd (nbrSumZ (fodo S s0 w0 t) x + s0 x) (nbrSumZ (wave η n z t) x + η x) (fodo S s0 w0 t x) hBA hw0' hw1' hA (by have hh := hc; simp only [fconf, lap] at hh; linarith)
    · rw [if_neg hc, add_zero]
      exact Exploding.ediv_step_ge_neg d hd (nbrSumZ (fodo S s0 w0 t) x + s0 x) (nbrSumZ (wave η n z t) x + η x) (fodo S s0 w0 t x) hBA hw0' hw1' hA (by have hh := hc; simp only [fconf, lap] at hh; linarith)

end Exploding
