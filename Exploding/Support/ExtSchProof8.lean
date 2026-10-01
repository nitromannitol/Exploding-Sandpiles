/-
The renormalization recursion for the Schonmann bound.

Partition `Q_{2n}^d` into its `2^d` corner sub-cubes `Q_n^d`.  If at most one
sub-cube fails to be internally spanned, then the other `2^d - 1` topple it: the
chosen face of the missing sub-cube in each direction is adjacent to a good
sub-cube, and the mixed-face corner growth `xsch8_corner_growth` fills the cube.
Hence `a (2n) ≤ C a n ^ 2` where `a n = P(Q_n^d not spanned)` and `C = 2^(2d)`,
and the sub-cubes are independent because they are disjoint.

Iterating this recursion from a scale `n0` at which `C a n0 < 1` gives
`a n ≤ (1/C) exp(-c n)`.  The recursion and the existence of the base scale
`n0` are the two remaining claims, isolated below.
-/
import Exploding.Support.ExtSchProof7

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The failure probability at scale `n`. -/
noncomputable def xsch8_a (d : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  (xsch_mu d p).real {η : Site d → ℤ |
    ¬ xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η}

/-- **The renormalization recursion (remaining claim).**  Splitting `Q_{2n}` into
corner sub-cubes, at most one of which is bad, gives `a (2n) ≤ C a n ^ 2`. -/
def xsch8_Recursion (d : ℕ) (p : ℝ) : Prop :=
  ∀ n : ℕ, xsch8_a d p (2 * n) ≤ (2 : ℝ) ^ (2 * d) * (xsch8_a d p n) ^ 2

/-- **The base scale (remaining claim).**  Some scale has `C a n0 < 1`. -/
def xsch8_Base (d : ℕ) (p : ℝ) : Prop :=
  ∃ n0 : ℕ, (2 : ℝ) ^ (2 * d) * xsch8_a d p n0 < 1

/-- **Iteration.**  A recursion `a (2n) ≤ C a n ^ 2` bounds `a` at the dyadic
scales through `n0` by the powers of `C a n0`; when `C a n0 < 1` this decays
doubly fast, and hence exponentially along the scale. -/
theorem xsch8_dyadic_bound {a : ℕ → ℝ} {C : ℝ} {n0 : ℕ} (hC : 0 < C)
    (ha : ∀ n : ℕ, 0 ≤ a n)
    (hrec : ∀ n : ℕ, a (2 * n) ≤ C * (a n) ^ 2) :
    ∀ k : ℕ, a (2 ^ k * n0) ≤ (1 / C) * (C * a n0) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero =>
    rw [pow_zero, one_mul]
    rw [show (1 / C) * (C * a n0) ^ 1 = a n0 by field_simp]
  | succ k ih =>
    have h2 : 2 ^ (k + 1) * n0 = 2 * (2 ^ k * n0) := by ring
    have h1 : a (2 ^ k * n0) ^ 2 ≤ ((1 / C) * (C * a n0) ^ (2 ^ k)) ^ 2 :=
      pow_le_pow_left₀ (ha _) ih 2
    calc a (2 ^ (k + 1) * n0)
        = a (2 * (2 ^ k * n0)) := by rw [h2]
      _ ≤ C * a (2 ^ k * n0) ^ 2 := hrec (2 ^ k * n0)
      _ ≤ C * ((1 / C) * (C * a n0) ^ (2 ^ k)) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 hC.le
      _ = (1 / C) * (C * a n0) ^ (2 ^ (k + 1)) := by
          rw [pow_succ, pow_succ]
          field_simp
          ring

end Exploding
