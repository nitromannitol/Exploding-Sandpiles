import Exploding.Support.ArxivBondFiniteHoleSeries

/-!
# Geometric bound for the bond-hole series term

For `K ≥ 1` and a density parameter `b` with `(2·3^d·K)^(3^d) · b ≤ 1`, the term
`(2m+1)^d K^m b^(m/3^d)` is at most `(2·3^d·K)^(3^d-1) (1/2)^m`. The proof bounds
`2m+1 ≤ 3^m`, writes `m = 3^d·n + j` with `j < 3^d`, and absorbs the `n` full blocks by the
smallness hypothesis. Only natural-number division and ENNReal arithmetic occur.
-/

namespace Exploding

/-- `2m + 1 ≤ 3^m` for every natural number `m`. -/
private theorem two_mul_add_one_le_three_pow (m : ℕ) : 2 * m + 1 ≤ 3 ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    omega

/-- For `A = 2·D·K ≥ 1` with `A^D · b ≤ 1` and `j < D`, the product `A^(D·n+j) · b^n` is at
most `A^(D-1)`. -/
private theorem bond_hole_block_le (D K : ℕ) (hD : 1 ≤ D) (hK : 1 ≤ K) (b : ENNReal)
    (hb : ((2 * D * K : ℕ) : ENNReal) ^ D * b ≤ 1) (n j : ℕ) (hj : j < D) :
    ((2 * D * K : ℕ) : ENNReal) ^ (D * n + j) * b ^ n ≤
      ((2 * D * K : ℕ) : ENNReal) ^ (D - 1) := by
  have hA : 1 ≤ 2 * D * K := by nlinarith
  have hA' : (1 : ENNReal) ≤ ((2 * D * K : ℕ) : ENNReal) := Nat.one_le_cast.mpr hA
  have hpow : (((2 * D * K : ℕ) : ENNReal) ^ D * b) ^ n ≤ 1 := by
    calc (((2 * D * K : ℕ) : ENNReal) ^ D * b) ^ n ≤ 1 ^ n :=
          pow_le_pow_left₀ zero_le hb n
      _ = 1 := one_pow n
  calc ((2 * D * K : ℕ) : ENNReal) ^ (D * n + j) * b ^ n
      = ((2 * D * K : ℕ) : ENNReal) ^ j *
          (((2 * D * K : ℕ) : ENNReal) ^ D * b) ^ n := by
        rw [pow_add, pow_mul, mul_pow]
        ring
    _ ≤ ((2 * D * K : ℕ) : ENNReal) ^ j * 1 := by gcongr
    _ = ((2 * D * K : ℕ) : ENNReal) ^ j := mul_one _
    _ ≤ ((2 * D * K : ℕ) : ENNReal) ^ (D - 1) := pow_le_pow_right₀ hA' (by omega)

/-- With `A = 2·D·K` and `A^D · b ≤ 1`, the term `(D·K)^m · b^(m/D)` is at most
`A^(D-1) · (1/2)^m`. -/
private theorem bond_hole_term_le_block_geometric (D K : ℕ) (hD : 1 ≤ D) (hK : 1 ≤ K)
    (b : ENNReal) (hb : ((2 * D * K : ℕ) : ENNReal) ^ D * b ≤ 1) (m : ℕ) :
    ((D * K : ℕ) : ENNReal) ^ m * b ^ (m / D) ≤
      ((2 * D * K : ℕ) : ENNReal) ^ (D - 1) * (1 / 2 : ENNReal) ^ m := by
  have hblock := bond_hole_block_le D K hD hK b hb (m / D) (m % D) (Nat.mod_lt m (by omega))
  rw [Nat.div_add_mod] at hblock
  have h2 : (2 : ENNReal) * (1 / 2) = 1 := by
    rw [one_div]
    exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  have hfac : ((D * K : ℕ) : ENNReal) = ((2 * D * K : ℕ) : ENNReal) * (1 / 2 : ENNReal) := by
    push_cast
    calc (D : ENNReal) * K = (2 * (1 / 2 : ENNReal)) * ((D : ENNReal) * K) := by
          rw [h2, one_mul]
      _ = 2 * (D : ENNReal) * K * (1 / 2 : ENNReal) := by ring
  calc ((D * K : ℕ) : ENNReal) ^ m * b ^ (m / D)
      = (((2 * D * K : ℕ) : ENNReal) ^ m * b ^ (m / D)) * (1 / 2 : ENNReal) ^ m := by
        rw [hfac, mul_pow]
        ring
    _ ≤ ((2 * D * K : ℕ) : ENNReal) ^ (D - 1) * (1 / 2 : ENNReal) ^ m := by gcongr

/-- The bond-hole series term `(2m+1)^d K^m b^(m/3^d)` is bounded by the geometric term
`(2·3^d·K)^(3^d-1) (1/2)^m`, under `K ≥ 1` and the smallness condition
`(2·3^d·K)^(3^d) · b ≤ 1`. -/
theorem arxiv_bond_hole_term_le_geometric
    (d K : ℕ) (hK : 1 ≤ K) (b : ENNReal)
    (hb : (((2 * (3 ^ d) * K : ℕ) : ENNReal) ^ (3 ^ d)) * b ≤ 1)
    (m : ℕ) :
    (((2 * m + 1) ^ d : ℕ) : ENNReal) * (K : ENNReal) ^ m *
        b ^ (m / 3 ^ d) ≤
      (((2 * (3 ^ d) * K : ℕ) : ENNReal) ^ (3 ^ d - 1)) *
        (1 / 2 : ENNReal) ^ m := by
  have hD : 1 ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have hnat : (2 * m + 1) ^ d ≤ (3 ^ d) ^ m :=
    calc (2 * m + 1) ^ d ≤ (3 ^ m) ^ d :=
          Nat.pow_le_pow_left (two_mul_add_one_le_three_pow m) d
      _ = (3 ^ d) ^ m := pow_right_comm 3 m d
  have hlead : (((2 * m + 1) ^ d : ℕ) : ENNReal) ≤ ((3 ^ d : ℕ) : ENNReal) ^ m := by
    rw [← Nat.cast_pow]
    exact Nat.cast_le.mpr hnat
  calc (((2 * m + 1) ^ d : ℕ) : ENNReal) * (K : ENNReal) ^ m * b ^ (m / 3 ^ d)
      ≤ ((3 ^ d : ℕ) : ENNReal) ^ m * (K : ENNReal) ^ m * b ^ (m / 3 ^ d) := by gcongr
    _ = ((3 ^ d * K : ℕ) : ENNReal) ^ m * b ^ (m / 3 ^ d) := by
        rw [Nat.cast_mul, mul_pow]
    _ ≤ (((2 * (3 ^ d) * K : ℕ) : ENNReal) ^ (3 ^ d - 1)) * (1 / 2 : ENNReal) ^ m :=
        bond_hole_term_le_block_geometric (3 ^ d) K hD hK b hb m

end Exploding
