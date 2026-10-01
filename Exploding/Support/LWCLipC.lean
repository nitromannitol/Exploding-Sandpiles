/-
Support for the far Lipschitz bound of Proposition 3.1: the deterministic core.  On a
background carrying an infinite cluster of good cubes with small holes and a linear chemical
distance, if the last wave reaches `x` at time `a`, it reaches every site `x'` of the box by time
`a + C |x - x'| + Z^{E1}`, where `Z` is a polylogarithmic scale: a good cube of the cluster near
`x` fires polylogarithmically later (`pclose_first_cube`), and from it the cluster carries the
wave to `x'` at a cost linear in the distance (`lwcl_light_site`).
-/
import Exploding.Support.LWCLipB

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- **The deterministic core of the far Lipschitz bound.** -/
theorem lwcl_lip_core (hd : 2 ≤ d) {η : Site d → ℤ} {k : ℕ} {Cinf : Set (Site d)}
    {n0h n0c : ℕ} {Cr : ℝ}
    (S : pub_Setup d η (waveThreshold η (0 : Site d)) k Cinf n0h n0c Cr)
    (m Z Cc Cn E E1 : ℕ) (hZ2 : 2 ≤ Z) (hkZ : k ≤ Z) (hCnZ : Cn ≤ Z) (hdZ : d ≤ Z)
    (hCr : Cr ≤ (Cc : ℝ))
    (hE : lwclE d k Cc Z ≤ Z ^ E) (hEE : E ≤ E1) (hE3 : 3 * d + 3 ≤ E1)
    (hsize : 8 * Z ^ E1 ≤ m) (hn0h : n0h ≤ 2 * m) (hn0c : n0c ≤ 2 * m)
    (hρ : Real.log (2 * (m : ℝ)) ^ ((5 : ℝ) / 2) ≤ (Z : ℝ))
    (hholeZ : ∀ y ∈ (cent d (2 * m) : Set (Site d)), y ∉ Cinf →
      (componentIn Cinfᶜ y).Finite ∧ (componentIn Cinfᶜ y).ncard < Z)
    (C6 ℓ6 : ℝ) (hC60 : 0 ≤ C6) (hC6 : C6 ≤ Cn) (hℓ6 : ℓ6 ≤ Z)
    (hub : ∀ w : Site d, mnorm w ≤ (m : ℤ) →
      ∃ m' : ℕ, lastArrival η (0 : Site d) w = (m' : ℕ∞) ∧ (m' : ℝ) ≤ C6 * mnorm w + ℓ6)
    (x x' : Site d) (hx : mnorm x ≤ (m : ℤ)) (hx' : mnorm x' ≤ (m : ℤ)) (a : ℕ)
    (ha : lastArrival η (0 : Site d) x = (a : ℕ∞)) :
    ∃ τ : ℕ, 1 ≤ τ ∧ 0 < lastWave η (0 : Site d) τ x' ∧
      (τ : ℝ) ≤ a + max ((k : ℝ) ^ d * Cr) C6 * (mnorm (x - x') : ℝ) + (Z : ℝ) ^ E1 := by
  have hk2 := S.hk
  have hk1 : 1 ≤ k := by omega
  have hZ1 : 1 ≤ Z := by omega
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ha1, hapos⟩ := pclose_attained η x a ha
  set L := (k * (Z + 2)) ^ d with hL
  have hL3 : L ≤ Z ^ (3 * d) := pclose_L_le d k Z hZ2 hkZ
  have hLZ : L ≤ Z ^ E1 := le_trans hL3 (Nat.pow_le_pow_right hZ1 (by omega))
  have hZZ : Z ≤ Z ^ E1 := by
    calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ Z ^ E1 := Nat.pow_le_pow_right hZ1 (by omega)
  have hpos1 : 1 ≤ Z ^ E1 := Nat.one_le_pow _ _ hZ1
  have hnn : (0 : ℝ) ≤ (mnorm (x - x') : ℝ) := by exact_mod_cast pub_mnorm_nonneg (x - x')
  have hPnn : (0 : ℝ) ≤ (k : ℝ) ^ d * Cr := by have := S.hCr; positivity
  by_cases hfar : (L : ℤ) ≤ mnorm x
  · -- the far case
    have hgood : ∀ j ∈ Cinf, GoodAt η k j := fun j hj => S.hCinf.2.1 hj
    have hn1 : mnorm x + ((L + 3 : ℕ) : ℤ) ≤ ((2 * m : ℕ) : ℤ) := by
      have : L + 3 ≤ m := by omega
      have h2 : ((L + 3 : ℕ) : ℤ) ≤ (m : ℤ) := by exact_mod_cast this
      push_cast
      linarith
    obtain ⟨Q, hQ, hfired, hQd⟩ := pclose_first_cube hd η S.hlow S.hhigh
      (waveThreshold η (0 : Site d)) S.hN k hk1 Cinf hgood Z (2 * m) hholeZ x a hapos L rfl hfar
      hn1
    -- the scale `ρ`
    set ρ : ℕ := Nat.ceil (Real.log ((2 * m : ℕ) : ℝ) ^ ((5 : ℝ) / 2)) with hρdef
    have hρZ : ρ ≤ Z := by
      refine Nat.ceil_le.mpr ?_
      push_cast
      exact hρ
    have hmq : mnorm Q ≤ (L : ℤ) + (m : ℤ) + d := by
      have h1 : Q = (Q - Exploding.macroIdx k x) + Exploding.macroIdx k x := by abel
      have h2 := pclose_mnorm_add_le (Q - Exploding.macroIdx k x) (Exploding.macroIdx k x)
      rw [← h1] at h2
      have h3 := pclose_mnorm_macro_le k hk1 x
      linarith
    have hroom : mnorm Q + 4 * (ρ : ℤ) ≤ ((2 * m : ℕ) : ℤ) := by
      have h1 : L + d + 4 * Z ≤ m := by omega
      have h2 : ((L + d + 4 * Z : ℕ) : ℤ) ≤ (m : ℤ) := by exact_mod_cast h1
      have h3 : (ρ : ℤ) ≤ (Z : ℤ) := by exact_mod_cast hρZ
      push_cast at h2 ⊢
      linarith
    have hn3 : 3 ≤ 2 * m := by omega
    obtain ⟨τ, hτ1, hτpos, hτle⟩ := lwcl_light_site S Q hQ _ hfired (2 * m) hn0h hn0c hn3
      hroom x' (by push_cast; linarith)
    refine ⟨τ, hτ1, hτpos, ?_⟩
    -- the distance from `Q` to the cube of `x'`
    have hQx' : mnorm (Q - Exploding.macroIdx k x') ≤ (L : ℤ) + mnorm (x - x') + d := by
      have h1 : Q - Exploding.macroIdx k x' = (Q - Exploding.macroIdx k x) +
          (Exploding.macroIdx k x - Exploding.macroIdx k x') := by abel
      rw [h1]
      have h2 := pclose_mnorm_add_le (Q - Exploding.macroIdx k x)
        (Exploding.macroIdx k x - Exploding.macroIdx k x')
      have h3 := lwcl_mnorm_macro_sub_le k hk1 x x'
      linarith
    have hQx'R : (mnorm (Q - Exploding.macroIdx k x') : ℝ) ≤ (L : ℝ) + (mnorm (x - x') : ℝ) + d := by
      exact_mod_cast hQx'
    have hρR : (ρ : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hρZ
    have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
    set P : ℝ := (k : ℝ) ^ d * Cr with hP
    have hPC : P ≤ (Cc : ℝ) * (k : ℝ) ^ d := by
      calc P = Cr * (k : ℝ) ^ d := by rw [hP]; ring
        _ ≤ (Cc : ℝ) * (k : ℝ) ^ d := mul_le_mul_of_nonneg_right hCr (by positivity)
    have hdist : (mnorm (Q - Exploding.macroIdx k x') : ℝ) + 10 * ρ ≤
        (mnorm (x - x') : ℝ) + ((L : ℝ) + d + 10 * Z) := by linarith
    have hdist0 : (0 : ℝ) ≤ (mnorm (Q - Exploding.macroIdx k x') : ℝ) + 10 * ρ := by
      have : (0 : ℝ) ≤ (mnorm (Q - Exploding.macroIdx k x') : ℝ) := by
        exact_mod_cast pub_mnorm_nonneg _
      linarith
    have hstep1 : P * ((mnorm (Q - Exploding.macroIdx k x') : ℝ) + 10 * ρ) ≤
        P * (mnorm (x - x') : ℝ) + (Cc : ℝ) * (k : ℝ) ^ d * ((L : ℝ) + d + 10 * Z) := by
      have h1 : P * ((mnorm (Q - Exploding.macroIdx k x') : ℝ) + 10 * ρ) ≤
          P * ((mnorm (x - x') : ℝ) + ((L : ℝ) + d + 10 * Z)) :=
        mul_le_mul_of_nonneg_left hdist hPnn
      have h2 : P * ((L : ℝ) + d + 10 * Z) ≤ (Cc : ℝ) * (k : ℝ) ^ d * ((L : ℝ) + d + 10 * Z) :=
        mul_le_mul_of_nonneg_right hPC (by positivity)
      nlinarith
    have hstep2 : (k : ℝ) * ((d : ℝ) + ρ) ≤ (k : ℝ) * ((d : ℝ) + Z) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hEcast : ((lwclE d k Cc Z : ℕ) : ℝ) ≤ (Z : ℝ) ^ E1 := by
      have h1 : lwclE d k Cc Z ≤ Z ^ E1 :=
        le_trans hE (Nat.pow_le_pow_right hZ1 hEE)
      exact_mod_cast h1
    have hEexp : ((lwclE d k Cc Z : ℕ) : ℝ) =
        ((2 * (L : ℝ) + 1) ^ d + (k : ℝ) ^ d + (Cc : ℝ) * (k : ℝ) ^ d * ((L : ℝ) + d + 10 * Z) +
          (k : ℝ) * ((d : ℝ) + Z) + 2) := by
      unfold lwclE
      rw [← hL]
      push_cast
      ring
    have hmax : P * (mnorm (x - x') : ℝ) ≤ max P C6 * (mnorm (x - x') : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
    have hT1 : ((a + (2 * L + 1) ^ d + k ^ d : ℕ) : ℝ) =
        (a : ℝ) + (2 * (L : ℝ) + 1) ^ d + (k : ℝ) ^ d := by push_cast; ring
    rw [hT1] at hτle
    linarith [hstep1, hstep2, hEexp, hEcast, hmax, hτle]
  · -- the near case
    push Not at hfar
    have hxx : mnorm x' ≤ (L : ℤ) + mnorm (x - x') := by
      have h1 : x' = x + (x' - x) := by abel
      have h2 := pclose_mnorm_add_le x (x' - x)
      rw [← h1] at h2
      have h3 : mnorm (x' - x) = mnorm (x - x') := pub_mnorm_sub_comm x' x
      linarith
    obtain ⟨m', hm', hmle⟩ := hub x' hx'
    obtain ⟨hm1, hmpos⟩ := pclose_attained η x' m' hm'
    refine ⟨m', hm1, hmpos, ?_⟩
    have hxxR : (mnorm x' : ℝ) ≤ (L : ℝ) + (mnorm (x - x') : ℝ) := by exact_mod_cast hxx
    have hCnZ1 : Cn ≤ Z ^ 1 := by rw [pow_one]; exact hCnZ
    have hZp1 : Z ≤ Z ^ 1 := (pow_one Z).symm.le
    have hbig : Cn * L + Z ≤ Z ^ E1 := by
      have h1 : Cn * L ≤ Z ^ (1 + 3 * d) := pclose_pb_mul hCnZ1 hL3
      have h2 : Cn * L + Z ≤ Z ^ (1 + 3 * d + 1) :=
        pclose_pb_add (e := 1 + 3 * d) hZ2 h1 (pclose_pb_mono hZ1 (by omega) hZp1)
      exact le_trans h2 (Nat.pow_le_pow_right hZ1 (by omega))
    have hbigR : (Cn : ℝ) * (L : ℝ) + Z ≤ (Z : ℝ) ^ E1 := by exact_mod_cast hbig
    have hLR : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have h1 : C6 * (mnorm x' : ℝ) ≤ C6 * ((L : ℝ) + (mnorm (x - x') : ℝ)) :=
      mul_le_mul_of_nonneg_left hxxR hC60
    have h2 : C6 * (L : ℝ) ≤ (Cn : ℝ) * (L : ℝ) := mul_le_mul_of_nonneg_right hC6 hLR
    have hmax : C6 * (mnorm (x - x') : ℝ) ≤ max ((k : ℝ) ^ d * Cr) C6 * (mnorm (x - x') : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hnn
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hmR : (m' : ℝ) ≤ C6 * (mnorm (x - x') : ℝ) + ((Cn : ℝ) * (L : ℝ) + Z) := by
      linarith
    linarith

end Exploding
