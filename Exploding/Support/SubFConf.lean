/-
The frozen sandpile of Section 4 of `paper/corrected-arxiv/exploding-corrected-arxiv.tex` is at most `4d - 1`
when the frozen odometer is in `[0, 1]` and the background is at most `2d - 1`.
-/
import Exploding.Support.SubFodo

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The frozen sandpile is at most `4d - 1` when the frozen odometer is in
`[0, 1]` and the background is at most `2d - 1`. -/
theorem fconf_le (S : Set (Site d)) (s0 w0 : Site d → ℤ)
    (hs0 : ∀ x, s0 x ≤ 2 * (d : ℤ) - 1)
    (hw0 : ∀ x, w0 x ≤ 1) (hw0nn : ∀ x, 0 ≤ w0 x)
    (t : ℕ) (x : Site d) :
    fconf S s0 w0 t x ≤ 4 * (d : ℤ) - 1 := by
  have h1 : nbrSumZ (fodo S s0 w0 t) x ≤ nbrSumZ (fun _ : Site d => (1:ℤ)) x :=
    Exploding.nbrSumZ_mono (fun y => Exploding.fodo_le_one S s0 w0 hs0 hw0 hw0nn t y) x
  have h2 : nbrSumZ (fun _ : Site d => (1:ℤ)) x = 2 * (d:ℤ) := by
    simp [Exploding.nbrSumZ]; ring
  have h3 : 0 ≤ fodo S s0 w0 t x := Exploding.fodo_nonneg S s0 w0 hw0nn t x
  simp only [fconf, lap]
  have h4 := hs0 x
  rw [h2] at h1
  nlinarith


/-- The neighbour sum of a frozen odometer in `[0, 1]` is at most `2d`. -/
theorem nbrSumZ_fodo_le (S : Set (Site d)) (s0 w0 : Site d → ℤ)
    (hs0 : ∀ x, s0 x ≤ 2 * (d : ℤ) - 1)
    (hw0 : ∀ x, w0 x ≤ 1) (hw0nn : ∀ x, 0 ≤ w0 x)
    (t : ℕ) (x : Site d) :
    nbrSumZ (fodo S s0 w0 t) x ≤ 2 * (d : ℤ) := by
  have h1 : nbrSumZ (fodo S s0 w0 t) x ≤ nbrSumZ (fun _ : Site d => (1:ℤ)) x :=
    Exploding.nbrSumZ_mono (fun y => Exploding.fodo_le_one S s0 w0 hs0 hw0 hw0nn t y) x
  have h2 : nbrSumZ (fun _ : Site d => (1:ℤ)) x = 2 * (d:ℤ) := by
    simp [Exploding.nbrSumZ]; ring
  linarith


/-- The frozen sandpile bound in the form the recursion uses: the neighbour sum
plus the background is at most `4d - 1`. -/
theorem nbrSumZ_add_s0_le (S : Set (Site d)) (s0 w0 : Site d → ℤ)
    (hs0 : ∀ x, s0 x ≤ 2 * (d : ℤ) - 1)
    (hw0 : ∀ x, w0 x ≤ 1) (hw0nn : ∀ x, 0 ≤ w0 x)
    (t : ℕ) (x : Site d) :
    nbrSumZ (fodo S s0 w0 t) x + s0 x ≤ 4 * (d : ℤ) - 1 := by
  have h1 : nbrSumZ (fodo S s0 w0 t) x ≤ nbrSumZ (fun _ : Site d => (1:ℤ)) x :=
    Exploding.nbrSumZ_mono (fun y => Exploding.fodo_le_one S s0 w0 hs0 hw0 hw0nn t y) x
  have h2 : nbrSumZ (fun _ : Site d => (1:ℤ)) x = 2 * (d:ℤ) := by
    simp [Exploding.nbrSumZ]; ring
  have h3 := hs0 x
  linarith

end Exploding
