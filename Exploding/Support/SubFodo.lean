/-
The comparison lemmas of Section 4 of `paper/exploding.tex` between the frozen
parallel toppling odometer and the last wave.

The paper's `(4.2)` bound: if the initial sandpile is at most `2d - 1` and the
frozen odometer starts in `[0, 1]`, then it stays at most `1` everywhere.  The
cap in the frozen recursion is inactive precisely because the value is already
`1`: then the frozen sandpile is at most `2d - 1`.
-/
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The paper's `(4.2)` bound: a frozen odometer that starts in `[0, 1]`, on a
background of at most `2d - 1` chips, stays at most `1` everywhere. -/
theorem fodo_le_one (S : Set (Site d)) (s0 w0 : Site d → ℤ)
    (hs0 : ∀ x, s0 x ≤ 2 * (d : ℤ) - 1)
    (hw0 : ∀ x, w0 x ≤ 1) (hw0nn : ∀ x, 0 ≤ w0 x)
    (t : ℕ) (x : Site d) :
    fodo S s0 w0 t x ≤ 1 := by
  have key : ∀ t : ℕ, ∀ x : Site d, 0 ≤ fodo S s0 w0 t x ∧ fodo S s0 w0 t x ≤ 1 := by
    intro t
    induction t with
    | zero => intro x; exact ⟨hw0nn x, hw0 x⟩
    | succ t ih =>
      intro x
      obtain ⟨hge, hle⟩ := ih x
      rw [Exploding.fodo_succ]
      by_cases hx : x ∈ S
      · rw [if_pos hx]; exact ⟨hw0nn x, hw0 x⟩
      · rw [if_neg hx]
        by_cases h1 : fodo S s0 w0 t x = 1
        · by_cases hc : 2 * (d:ℤ) ≤ fconf S s0 w0 t x
          · exfalso
            have h1' : nbrSumZ (fodo S s0 w0 t) x ≤ nbrSumZ (fun _ : Site d => (1:ℤ)) x :=
              Exploding.nbrSumZ_mono (fun y => (ih y).2) x
            have h2 : nbrSumZ (fun _ : Site d => (1:ℤ)) x = 2 * (d:ℤ) := by
              simp [Exploding.nbrSumZ]; ring
            simp only [fconf, lap, h1] at hc
            rw [h2] at h1'
            have h4 := hs0 x
            nlinarith
          · rw [if_neg hc]; exact ⟨by linarith, by linarith⟩
        · have h0 : fodo S s0 w0 t x = 0 := by omega
          by_cases hc : 2 * (d:ℤ) ≤ fconf S s0 w0 t x
          · rw [if_pos hc]; exact ⟨by omega, by omega⟩
          · rw [if_neg hc]; exact ⟨by omega, by omega⟩
  exact (key t x).2

/-- A frozen odometer started from a nonnegative initial condition stays
nonnegative. -/
theorem fodo_nonneg (S : Set (Site d)) (s0 w0 : Site d → ℤ)
    (hw0nn : ∀ x, 0 ≤ w0 x) (t : ℕ) (x : Site d) :
    0 ≤ fodo S s0 w0 t x := by
  induction t generalizing x with
  | zero => exact hw0nn x
  | succ t ih =>
    rw [Exploding.fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx]; exact hw0nn x
    · rw [if_neg hx]
      have := ih x
      split_ifs <;> linarith

end Exploding
