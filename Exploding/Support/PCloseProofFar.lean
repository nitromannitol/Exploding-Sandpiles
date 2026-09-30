/-
The far case of the second inequality of Lemma 3.7: if the last wave is positive at a
site `x` far from the centre, then it is positive on the box of radius `R` about `x`
after polynomially many further steps.  This combines the first fired good cube
(`pclose_first_cube`) with the spreading step (`pclose_spread`), and bounds the total
time by a power of the scale `Z`.
-/
import Exploding.Support.PCloseProofFirst
import Exploding.Support.PCloseProofSpread

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The total time of the far case. -/
def pcloseT (d k Cc Z L : ℕ) : ℕ :=
  (2 * L + 1) ^ d + k ^ d + pcloseW d Cc Z L * k ^ d + (2 * pcloseR2 d k Cc Z L + 1) ^ d

/-- **The far case.** -/
theorem pclose_far (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d))
    (hgood : ∀ j ∈ Cinf, GoodAt η k j)
    (Z n1 Cc R : ℕ) (hRZ : R ≤ Z)
    (hhole : ∀ y ∈ (cent d n1 : Set (Site d)), y ∉ Cinf →
      (componentIn Cinfᶜ y).Finite ∧ (componentIn Cinfᶜ y).ncard < Z)
    (hchem : ∀ y ∈ Cinf, ∀ y' ∈ Cinf, mnorm y ≤ (n1 : ℤ) → (Z : ℤ) ≤ mnorm (y - y') →
      ∃ m : ℕ, chemDist Cinf y y' = (m : ℕ∞) ∧ (m : ℤ) ≤ (Cc : ℤ) * mnorm (y - y'))
    (x : Site d) (t : ℕ) (hx : 0 < wave η N 0 t x)
    (L : ℕ) (hL : L = (k * (Z + 2)) ^ d) (hxL : (L : ℤ) ≤ mnorm x)
    (hn1 : mnorm x + ((L + Z + Z + d + 3 : ℕ) : ℤ) ≤ (n1 : ℤ)) :
    ∀ w : Site d, (∀ l, |w l - x l| ≤ (R : ℤ)) →
      0 < wave η N 0 (t + pcloseT d k Cc Z L) w := by
  intro w hw
  have hL1 : 1 ≤ L := by
    rw [hL]; exact Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (by omega))
  obtain ⟨Q, hQ, hfired, hQd⟩ := pclose_first_cube hd η hlow hhigh N hN k hk Cinf hgood Z n1
    hhole x t hx L hL hxL (by push_cast at hn1 ⊢; linarith)
  have h := pclose_spread hd η hlow hhigh N hN k hk Cinf hgood Z n1 Cc R hRZ hhole hchem
    x Q hQ L hL1 hQd _ hfired (by push_cast at hn1 ⊢; linarith) w hw
  have he : t + pcloseT d k Cc Z L =
      t + (2 * L + 1) ^ d + k ^ d + pcloseW d Cc Z L * k ^ d +
        (2 * pcloseR2 d k Cc Z L + 1) ^ d := by
    unfold pcloseT; ring
  rw [he]
  exact h

/-! ### The polynomial bound on the total time -/

theorem pclose_pb_add {Z a b e : ℕ} (hZ : 2 ≤ Z) (ha : a ≤ Z ^ e) (hb : b ≤ Z ^ e) :
    a + b ≤ Z ^ (e + 1) := by
  calc a + b ≤ Z ^ e + Z ^ e := Nat.add_le_add ha hb
    _ = 2 * Z ^ e := by ring
    _ ≤ Z * Z ^ e := Nat.mul_le_mul_right _ hZ
    _ = Z ^ (e + 1) := by ring

theorem pclose_pb_mono {Z a e f : ℕ} (hZ : 1 ≤ Z) (hef : e ≤ f) (ha : a ≤ Z ^ e) :
    a ≤ Z ^ f :=
  le_trans ha (Nat.pow_le_pow_right hZ hef)

theorem pclose_pb_mul {Z a b e f : ℕ} (ha : a ≤ Z ^ e) (hb : b ≤ Z ^ f) :
    a * b ≤ Z ^ (e + f) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

theorem pclose_pb_pow {Z a e : ℕ} (ha : a ≤ Z ^ e) (n : ℕ) : a ^ n ≤ Z ^ (e * n) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left ha n

/-- The scale `L = (k (Z + 2))^d` is at most `Z^(3d)`. -/
theorem pclose_L_le (d k Z : ℕ) (hZ : 2 ≤ Z) (hk : k ≤ Z) :
    (k * (Z + 2)) ^ d ≤ Z ^ (3 * d) := by
  have h1 : k ≤ Z ^ 1 := by simpa using hk
  have h2 : Z + 2 ≤ Z ^ 2 := by nlinarith
  have h3 : k * (Z + 2) ≤ Z ^ (1 + 2) := pclose_pb_mul h1 h2
  have h4 := pclose_pb_pow h3 d
  have : (1 + 2) * d = 3 * d := by ring
  rwa [this] at h4

/-- **The total time of the far case is a fixed power of `Z`.** -/
theorem pclose_T_le (d : ℕ) (hd : 1 ≤ d) : ∃ E : ℕ, ∀ Z k Cc : ℕ, 2 ≤ Z → k ≤ Z → Cc ≤ Z →
    d ≤ Z → pcloseT d k Cc Z ((k * (Z + 2)) ^ d) ≤ Z ^ E := by
  refine ⟨(3 * d + 10) * d + 3, ?_⟩
  intro Z k Cc hZ hk hCc hdZ
  have hZ1 : 1 ≤ Z := by omega
  set L := (k * (Z + 2)) ^ d with hLdef
  have hL : L ≤ Z ^ (3 * d) := pclose_L_le d k Z hZ hk
  have hZp : Z ≤ Z ^ 1 := by simp
  have hkp : k ≤ Z ^ 1 := by simpa using hk
  have hCcp : Cc ≤ Z ^ 1 := by simpa using hCc
  have hdp : d ≤ Z ^ 1 := by simpa using hdZ
  have h1p : 1 ≤ Z ^ 0 := by simp
  -- `2L + 1`
  have hLL : L + L ≤ Z ^ (3 * d + 1) := pclose_pb_add hZ hL hL
  have h2L1 : 2 * L + 1 ≤ Z ^ (3 * d + 2) := by
    have := pclose_pb_add (a := L + L) (b := 1) (e := 3 * d + 1) hZ hLL
      (pclose_pb_mono hZ1 (by omega) h1p)
    calc 2 * L + 1 = L + L + 1 := by ring
      _ ≤ Z ^ (3 * d + 1 + 1) := this
  have hB1 : (2 * L + 1) ^ d ≤ Z ^ ((3 * d + 2) * d) := pclose_pb_pow h2L1 d
  have hkd : k ^ d ≤ Z ^ (1 * d) := pclose_pb_pow hkp d
  -- the walk length
  have hLZ : L + Z ≤ Z ^ (3 * d + 1) :=
    pclose_pb_add hZ (pclose_pb_mono hZ1 (by omega) hL) (pclose_pb_mono hZ1 (by omega) hZp)
  have hLZZ : (L + Z) + Z ≤ Z ^ (3 * d + 2) :=
    pclose_pb_add hZ hLZ (pclose_pb_mono hZ1 (by omega) hZp)
  have hdLZ : d * ((L + Z) + Z) ≤ Z ^ (1 + (3 * d + 2)) := pclose_pb_mul hdp hLZZ
  have hsum : d * ((L + Z) + Z) + L ≤ Z ^ (3 * d + 4) :=
    pclose_pb_add hZ (pclose_pb_mono hZ1 (by omega) hdLZ) (pclose_pb_mono hZ1 (by omega) hL)
  have hW : pcloseW d Cc Z L ≤ Z ^ (1 + (3 * d + 4)) := pclose_pb_mul hCcp hsum
  have hWL : pcloseW d Cc Z L + L ≤ Z ^ (3 * d + 6) :=
    pclose_pb_add hZ (pclose_pb_mono hZ1 (by omega) hW) (pclose_pb_mono hZ1 (by omega) hL)
  have hkWL : k * (pcloseW d Cc Z L + L) ≤ Z ^ (1 + (3 * d + 6)) := pclose_pb_mul hkp hWL
  have h2k : 2 * k ≤ Z ^ 2 := by
    have : 2 * k ≤ 2 * Z := by omega
    calc 2 * k ≤ 2 * Z := this
      _ ≤ Z * Z := Nat.mul_le_mul_right _ hZ
      _ = Z ^ 2 := by ring
  have hR2 : pcloseR2 d k Cc Z L ≤ Z ^ (3 * d + 8) := by
    have h7 : k * (pcloseW d Cc Z L + L) ≤ Z ^ (3 * d + 7) := pclose_pb_mono hZ1 (by omega) hkWL
    have h7' : 2 * k ≤ Z ^ (3 * d + 7) := pclose_pb_mono hZ1 (by omega) h2k
    exact pclose_pb_add hZ h7 h7'
  have h2R2 : 2 * pcloseR2 d k Cc Z L + 1 ≤ Z ^ (3 * d + 10) := by
    have h1 : 2 * pcloseR2 d k Cc Z L ≤ Z ^ (3 * d + 9) := by
      calc 2 * pcloseR2 d k Cc Z L ≤ Z * Z ^ (3 * d + 8) := Nat.mul_le_mul hZ hR2
        _ = Z ^ (3 * d + 9) := by ring
    exact pclose_pb_add hZ h1 (pclose_pb_mono hZ1 (by omega) h1p)
  have hB2 : (2 * pcloseR2 d k Cc Z L + 1) ^ d ≤ Z ^ ((3 * d + 10) * d) := pclose_pb_pow h2R2 d
  have hWk : pcloseW d Cc Z L * k ^ d ≤ Z ^ ((1 + (3 * d + 4)) + 1 * d) := pclose_pb_mul hW hkd
  -- the sum of the four terms
  unfold pcloseT
  have a1 : (2 * L + 1) ^ d ≤ Z ^ ((3 * d + 10) * d) :=
    pclose_pb_mono hZ1 (by nlinarith) hB1
  have a2 : k ^ d ≤ Z ^ ((3 * d + 10) * d) := pclose_pb_mono hZ1 (by nlinarith) hkd
  have a3 : pcloseW d Cc Z L * k ^ d ≤ Z ^ ((3 * d + 10) * d + 1) :=
    pclose_pb_mono hZ1 (by nlinarith) hWk
  have a4 : (2 * pcloseR2 d k Cc Z L + 1) ^ d ≤ Z ^ ((3 * d + 10) * d + 2) :=
    pclose_pb_mono hZ1 (by omega) hB2
  have s1 := pclose_pb_add hZ a1 a2
  have s2 := pclose_pb_add hZ s1 a3
  have s3 := pclose_pb_add hZ s2 a4
  simpa [add_assoc] using s3

end Exploding
