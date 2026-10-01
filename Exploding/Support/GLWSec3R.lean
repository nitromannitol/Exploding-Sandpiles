/-
Proposition 5.1 of the paper (generalized last wave): the lighting of a box of tiles around a target
from a lit tile of `C_∞`, with explicit time bounds.

The key lemma takes the scales as parameters satisfying the size conditions of
`glws_asymp_ln`: two walks of `C_∞`, one from the lit tile `j` to a far point `M_f` and one from
`M_f` to a point `M_o` on the other side of the target `ν`, light the tiles around `ν` within
`A (|j| + |ν|) + B Z^d` steps, where `Z` is the macroscopic radius.
-/
import Exploding.Support.GLWSec3Q
import Exploding.Support.PUBProofB
import Exploding.Support.PCloseProofPath

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

theorem glws_mnorm_le_coord (v : Site d) (R : ℤ) (h : ∀ m, |v m| ≤ R) :
    mnorm v ≤ (d : ℤ) * R := by
  unfold mnorm
  calc ∑ m, |v m| ≤ ∑ _m : Fin d, R := Finset.sum_le_sum fun m _ => h m
    _ = (d : ℤ) * R := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem glws_walk_mnorm (c : ℕ → Site d) {m : ℕ}
    (hadj : ∀ s, s < m → (lattice d).Adj (c s) (c (s + 1))) :
    ∀ s, s ≤ m → mnorm (c s - c 0) ≤ (s : ℤ) := by
  intro s
  induction s with
  | zero => intro _; simp [mnorm]
  | succ s ih =>
    intro hs
    have h1 := ih (by omega)
    have h2 := pclose_mnorm_of_adj (hadj s (by omega))
    have h3 : mnorm (c (s + 1) - c 0) ≤ mnorm (c (s + 1) - c s) + mnorm (c s - c 0) :=
      pub_mnorm_sub_le (c (s + 1)) (c s) (c 0)
    push_cast
    linarith

/-- The sites of a tile have coordinates at most `∑ k` times the norm of the tile index, plus one. -/
theorem glws_tile_coord_le (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j y : Site d)
    (hy : y ∈ rboxShift k j) (m : Fin d) :
    |y m| ≤ ((∑ i, k i : ℕ) : ℤ) * (mnorm j + 1) := by
  have hym := hy m
  have hkm : (1 : ℤ) ≤ (k m : ℤ) := by exact_mod_cast hk m
  have hjm : |j m| ≤ mnorm j := abs_coord_le_mnorm j m
  have hkk : (k m : ℤ) ≤ ((∑ i, k i : ℕ) : ℤ) := by
    have : k m ≤ ∑ i, k i := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ m)
    exact_mod_cast this
  have hn0 : 0 ≤ mnorm j := by unfold mnorm; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [abs_le]
  have hjabs : -|j m| ≤ j m ∧ j m ≤ |j m| := ⟨neg_abs_le _, le_abs_self _⟩
  have h1 : (k m : ℤ) * j m ≤ (k m : ℤ) * |j m| := mul_le_mul_of_nonneg_left hjabs.2 (by linarith)
  have h2 : (k m : ℤ) * (-|j m|) ≤ (k m : ℤ) * j m :=
    mul_le_mul_of_nonneg_left hjabs.1 (by linarith)
  have h3 : (k m : ℤ) * (|j m| + 1) ≤ ((∑ i, k i : ℕ) : ℤ) * (mnorm j + 1) := by
    apply mul_le_mul hkk (by linarith) (by positivity) (by linarith)
  constructor <;> nlinarith [hym.1, hym.2, abs_nonneg (j m)]

/-- The arithmetic of the time bound of the lighting. -/
theorem glws_time_arith (Cn K d kmax Z Λ m1 m2 aj av : ℕ) (hd : 1 ≤ d) (hZ1 : 1 ≤ Z)
    (hΛ3 : Λ ≤ 3 * Z) (hm1 : m1 ≤ Cn * (aj + av + d * Λ)) (hm2 : m2 ≤ Cn * (d * (2 * Λ))) :
    (m1 + m2) * K + ((m2 + 1) * kmax ^ d) ^ d ≤
      Cn * K * (aj + av) + (9 * Cn * K * d + ((6 * Cn * d + 1) * kmax ^ d) ^ d) * Z ^ d := by
  have hZd : Z ≤ Z ^ d := Nat.le_self_pow (by omega) Z
  have h1 : (m1 + m2) * K ≤ (Cn * (aj + av) + 3 * (Cn * d * Λ)) * K := by
    apply Nat.mul_le_mul_right
    nlinarith
  have h2 : 3 * (Cn * d * Λ) ≤ 9 * (Cn * d) * Z := by
    have : Cn * d * Λ ≤ Cn * d * (3 * Z) := Nat.mul_le_mul_left _ hΛ3
    nlinarith
  have h3 : (m2 + 1) * kmax ^ d ≤ ((6 * Cn * d + 1) * kmax ^ d) * Z := by
    have : m2 + 1 ≤ (6 * Cn * d + 1) * Z := by nlinarith
    calc (m2 + 1) * kmax ^ d ≤ ((6 * Cn * d + 1) * Z) * kmax ^ d :=
          Nat.mul_le_mul_right _ this
      _ = ((6 * Cn * d + 1) * kmax ^ d) * Z := by ring
  have h4 : ((m2 + 1) * kmax ^ d) ^ d ≤ ((6 * Cn * d + 1) * kmax ^ d) ^ d * Z ^ d := by
    calc ((m2 + 1) * kmax ^ d) ^ d ≤ (((6 * Cn * d + 1) * kmax ^ d) * Z) ^ d :=
          Nat.pow_le_pow_left h3 d
      _ = ((6 * Cn * d + 1) * kmax ^ d) ^ d * Z ^ d := mul_pow _ _ _
  have h5 : (Cn * (aj + av) + 3 * (Cn * d * Λ)) * K ≤
      Cn * K * (aj + av) + 9 * Cn * K * d * Z ^ d := by
    have : 3 * (Cn * d * Λ) * K ≤ 9 * (Cn * d) * Z * K := Nat.mul_le_mul_right _ h2
    have h6 : 9 * (Cn * d) * Z * K ≤ 9 * (Cn * d) * Z ^ d * K := by
      apply Nat.mul_le_mul_right
      exact Nat.mul_le_mul_left _ hZd
    nlinarith
  nlinarith [h1, h4, h5]

end Exploding
