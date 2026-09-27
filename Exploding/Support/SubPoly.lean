import Exploding.Support.Vocab

/-!
# Polylogarithmic bounds

Polylogarithmic bounds used by the penultimate-cluster arguments of
`paper/exploding.tex`: a power of `Real.log` is eventually dominated by a
polynomial, and the centred box `cent d m` has exactly `(2m+1)^d` points.
-/
namespace Exploding

open LatticeProb

/-- A power of the logarithm is eventually dominated by the polynomial
`(2m+1)^d`, for `d ≥ 2`.  This is the comparison the paper uses when it says
that a component of volume smaller than `(log n)^{5/2}` is much smaller than a
box of side `n`. -/
theorem log_rpow_le_poly (d : ℕ) (hd : 2 ≤ d) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → Real.log m ^ ((5 : ℝ) / 2) ≤ ((2 * m + 1 : ℕ) ^ d : ℝ) := by
  refine ⟨256, fun m hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hlog : Real.log (m : ℝ) ≤ 4 * (m : ℝ) ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_rpow_div hm0.le (show (0 : ℝ) < (1 : ℝ) / 4 by norm_num)
    have h4 : (m : ℝ) ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4) = 4 * (m : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [div_eq_mul_inv]; ring
    linarith [h4 ▸ h]
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have h1 : Real.log (m : ℝ) ^ ((5 : ℝ) / 2) ≤
      (4 * (m : ℝ) ^ ((1 : ℝ) / 4)) ^ ((5 : ℝ) / 2) :=
    Real.rpow_le_rpow hlog0 hlog (by norm_num)
  have h2 : (4 * (m : ℝ) ^ ((1 : ℝ) / 4)) ^ ((5 : ℝ) / 2) =
      32 * (m : ℝ) ^ ((5 : ℝ) / 8) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hm0.le _), ← Real.rpow_mul hm0.le]
    have h4 : (4 : ℝ) ^ ((5 : ℝ) / 2) = 32 := by norm_num [Real.rpow_def_of_pos]
    rw [h4]
    norm_num
  have h3 : (m : ℝ) ^ ((5 : ℝ) / 8) ≤ (m : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have h4 : 32 * (m : ℝ) ^ ((3 : ℝ) / 4) ≤ (m : ℝ) ^ (2 : ℝ) := by
    have h5 : (32 : ℝ) ≤ (m : ℝ) ^ ((5 : ℝ) / 4) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 256)
        (by exact_mod_cast hm : (256 : ℝ) ≤ (m : ℝ)) (by norm_num : (0 : ℝ) ≤ (5 : ℝ) / 4)
      norm_num [Real.rpow_def_of_pos] at h
      linarith
    have h6 : (m : ℝ) ^ ((3 : ℝ) / 4) * (m : ℝ) ^ ((5 : ℝ) / 4) = (m : ℝ) ^ (2 : ℝ) := by
      rw [← Real.rpow_add hm0]; norm_num
    have h7 : (0 : ℝ) ≤ (m : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hm0.le _
    nlinarith [mul_le_mul_of_nonneg_right h5 h7, h6]
  have h5 : (m : ℝ) ^ (2 : ℝ) ≤ ((2 * m + 1 : ℕ) ^ d : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    show (m : ℝ) ^ 2 ≤ ((2 * m + 1 : ℕ) ^ d : ℝ)
    have hbase : (1 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 2 * m + 1 := by omega
      exact_mod_cast this
    have hpow : ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * m + 1 : ℕ) : ℝ) ^ d :=
      pow_le_pow_right₀ hbase hd
    have hcast2 : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
    have hcast : (((2 * m + 1 : ℕ) : ℝ) ^ d) = ((2 * m + 1 : ℕ) ^ d : ℝ) := by
      push_cast
      ring
    rw [hcast] at hpow
    rw [hcast2] at hpow
    rw [hcast2]
    have hsq : (m : ℝ) ^ 2 ≤ (2 * (m : ℝ) + 1) ^ 2 := by nlinarith [hm1]
    exact le_trans hsq hpow
  rw [h2] at h1
  have h8 : 32 * (m : ℝ) ^ ((5 : ℝ) / 8) ≤ 32 * (m : ℝ) ^ ((3 : ℝ) / 4) := by
    have : (0 : ℝ) ≤ 32 := by norm_num
    exact mul_le_mul_of_nonneg_left h3 this
  linarith

/-- The centred box `cent d m` is finite with exactly `(2m+1)^d` points. -/
theorem cent_finite_ncard (d m : ℕ) :
    (cent d m : Set (Site d)).Finite ∧ (cent d m : Set (Site d)).ncard = (2 * m + 1) ^ d := by
  have h_fin : (cent d m : Set (Site d)).Finite := by
    have h_each (i : Fin d) : {x : ℤ | |x| ≤ (m : ℤ)}.Finite := by
      have h_eq : {x : ℤ | |x| ≤ (m : ℤ)} = (Finset.Icc (-(m : ℤ)) (m : ℤ) : Set ℤ) := by
        ext x; simp [abs_le]
      rw [h_eq]
      exact Finset.finite_toSet _
    have h_eq : (cent d m : Set (Site d)) =
        Set.pi Set.univ (fun (_ : Fin d) => {x : ℤ | |x| ≤ (m : ℤ)}) := by
      ext f; simp [cent, Set.mem_pi, Set.mem_setOf_eq]
    rw [h_eq]
    exact Set.Finite.pi h_each
  have h_card : (cent d m : Set (Site d)).ncard = (2 * m + 1) ^ d := by
    have h_finset_eq : (cent d m : Set (Site d)) =
        (Fintype.piFinset (fun (_ : Fin d) => Finset.Icc (-(m : ℤ)) (m : ℤ)) : Set (Site d)) := by
      ext f
      simp [cent, abs_le, Pi.le_def, forall_and]
    have h_card_Icc : (Finset.Icc (-(m : ℤ)) (m : ℤ)).card = 2 * m + 1 := by
      rw [Int.card_Icc]
      have h : (m : ℤ) + 1 - (-(m : ℤ)) = 2 * (m : ℤ) + 1 := by ring
      rw [h]
      have hpos : 0 ≤ 2 * (m : ℤ) + 1 := by omega
      apply (Nat.cast_inj (R := ℤ)).mp
      simpa using Int.toNat_of_nonneg hpos
    rw [h_finset_eq]
    rw [Set.ncard_coe_finset]
    rw [Fintype.card_piFinset_const]
    rw [h_card_Icc]
  exact ⟨h_fin, h_card⟩

/-- The box `cube d k` is finite. -/
theorem cube_finite (d k : ℕ) : (cube d k : Set (Site d)).Finite := by
  have h_eq : (cube d k : Set (Site d)) =
      (Fintype.piFinset (fun (_ : Fin d) => Finset.Icc (1 : ℤ) (k : ℤ)) : Set (Site d)) := by
    ext x
    simp only [cube, Set.mem_setOf_eq, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc,
      forall_and]
  rw [h_eq]
  exact Finset.finite_toSet _

end Exploding
