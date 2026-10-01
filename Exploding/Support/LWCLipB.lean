/-
Support for the far Lipschitz bound of Proposition 3.1, packet LIP: the polynomial bookkeeping.
The total polylogarithmic overhead of the far case, written in the scale `Z`, is at most a fixed
power of `Z`.
-/
import Exploding.Support.LWCLipA

namespace Exploding

open LatticeProb

/-- The polylogarithmic overhead of the far case: the first fired cube costs
`(2 L + 1)^d + k^d` with `L = (k (Z + 2))^d`, and lighting the target site from it costs
`Cc k^d (L + d + 10 Z) + k (d + Z) + 2`. -/
def lwclE (d k Cc Z : ℕ) : ℕ :=
  (2 * (k * (Z + 2)) ^ d + 1) ^ d + k ^ d + Cc * k ^ d * ((k * (Z + 2)) ^ d + d + 10 * Z) +
    k * (d + Z) + 2

/-- **The overhead is a fixed power of the scale.** -/
theorem lwcl_E_le (d : ℕ) (hd : 1 ≤ d) : ∃ E : ℕ, ∀ Z k Cc : ℕ, 2 ≤ Z → k ≤ Z → Cc ≤ Z →
    d ≤ Z → lwclE d k Cc Z ≤ Z ^ E := by
  refine ⟨(3 * d + 10) * d + 10 + 4, ?_⟩
  intro Z k Cc hZ hk hCc hdZ
  have hZ1 : 1 ≤ Z := by omega
  have e1 : (3 * d + 2) * d ≤ (3 * d + 10) * d + 10 := by nlinarith
  have e2 : 1 * d ≤ (3 * d + 10) * d + 10 := by nlinarith
  have e3 : (1 + 1 * d) + (3 * d + 6) ≤ (3 * d + 10) * d + 10 := by nlinarith
  have e4 : 1 + 2 ≤ (3 * d + 10) * d + 10 := by nlinarith
  have e5 : 1 ≤ (3 * d + 10) * d + 10 := by nlinarith
  generalize (3 * d + 10) * d + 10 = E0 at e1 e2 e3 e4 e5 ⊢
  set L := (k * (Z + 2)) ^ d with hLdef
  have hL : L ≤ Z ^ (3 * d) := pclose_L_le d k Z hZ hk
  have hZp : Z ≤ Z ^ 1 := by simp
  have hkp : k ≤ Z ^ 1 := by simpa using hk
  have hCcp : Cc ≤ Z ^ 1 := by simpa using hCc
  have hdp : d ≤ Z ^ 1 := by simpa using hdZ
  have h1p : 1 ≤ Z ^ 0 := by simp
  have h2p : 2 ≤ Z ^ 1 := by simpa using hZ
  have h10 : 10 ≤ Z ^ 4 := by
    calc 10 ≤ 2 ^ 4 := by norm_num
      _ ≤ Z ^ 4 := Nat.pow_le_pow_left hZ 4
  -- `(2 L + 1)^d`
  have hLL : L + L ≤ Z ^ (3 * d + 1) := pclose_pb_add hZ hL hL
  have h2L1 : 2 * L + 1 ≤ Z ^ (3 * d + 2) := by
    have := pclose_pb_add (a := L + L) (b := 1) (e := 3 * d + 1) hZ hLL
      (pclose_pb_mono hZ1 (by omega) h1p)
    calc 2 * L + 1 = L + L + 1 := by ring
      _ ≤ Z ^ (3 * d + 1 + 1) := this
  have hB1 : (2 * L + 1) ^ d ≤ Z ^ ((3 * d + 2) * d) := pclose_pb_pow h2L1 d
  have hkd : k ^ d ≤ Z ^ (1 * d) := pclose_pb_pow hkp d
  -- `L + d + 10 Z`
  have h10Z : 10 * Z ≤ Z ^ 5 := by
    calc 10 * Z ≤ Z ^ 4 * Z := Nat.mul_le_mul_right _ h10
      _ = Z ^ 5 := by ring
  have hs1 : L + d ≤ Z ^ (3 * d + 1) :=
    pclose_pb_add hZ (pclose_pb_mono hZ1 (by omega) hL) (pclose_pb_mono hZ1 (by omega) hdp)
  have hs2 : L + d + 10 * Z ≤ Z ^ (3 * d + 6) :=
    pclose_pb_add (e := 3 * d + 5) hZ (pclose_pb_mono hZ1 (by omega) hs1)
      (pclose_pb_mono hZ1 (by omega) h10Z)
  have hprod1 : Cc * k ^ d ≤ Z ^ (1 + 1 * d) := pclose_pb_mul hCcp hkd
  have hprod : Cc * k ^ d * (L + d + 10 * Z) ≤ Z ^ ((1 + 1 * d) + (3 * d + 6)) :=
    pclose_pb_mul hprod1 hs2
  -- `k (d + Z)`
  have hdZ2 : d + Z ≤ Z ^ 2 := by
    have := pclose_pb_add (a := d) (b := Z) (e := 1) hZ hdp hZp
    simpa using this
  have hkdZ : k * (d + Z) ≤ Z ^ (1 + 2) := pclose_pb_mul hkp hdZ2
  -- the sum
  unfold lwclE
  rw [← hLdef]
  have a1 : (2 * L + 1) ^ d ≤ Z ^ E0 := pclose_pb_mono hZ1 e1 hB1
  have a2 : k ^ d ≤ Z ^ E0 := pclose_pb_mono hZ1 e2 hkd
  have a3 : Cc * k ^ d * (L + d + 10 * Z) ≤ Z ^ E0 := pclose_pb_mono hZ1 e3 hprod
  have a4 : k * (d + Z) ≤ Z ^ E0 := pclose_pb_mono hZ1 e4 hkdZ
  have a5 : 2 ≤ Z ^ E0 := le_trans h2p (pclose_pb_mono hZ1 e5 (le_refl (Z ^ 1)))
  have s1 := pclose_pb_add hZ a1 a2
  have s2 := pclose_pb_add (e := E0 + 1) hZ s1 (pclose_pb_mono hZ1 (by omega) a3)
  have s3 := pclose_pb_add (e := E0 + 2) hZ s2 (pclose_pb_mono hZ1 (by omega) a4)
  have s4 := pclose_pb_add (e := E0 + 3) hZ s3 (pclose_pb_mono hZ1 (by omega) a5)
  refine le_trans (le_of_eq ?_) (pclose_pb_mono hZ1 (by omega) s4)
  ring

end Exploding
