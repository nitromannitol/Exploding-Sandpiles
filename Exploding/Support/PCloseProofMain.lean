/-
The second inequality of Lemma 3.7 (`exploding-corrected-arxiv.tex:830-837`), assembled from the far case
(`pclose_far`), the linear bound of Lemma 3.6 for the near case, and the polylogarithmic
size of the penultimate cluster from Lemma 3.5.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubPub
import Exploding.Support.PCloseProofFar
import Exploding.Support.PCloseProofAsymp
import Exploding.Frozen.PenultimateUpperBound
import Exploding.Frozen.PenultimateCluster
import Exploding.Frozen.Renormalization

open Exploding LatticeProb MeasureTheory

namespace Exploding

variable {d : ℕ}

/-- `lastArrival` is attained at the natural number it equals, at a time `≥ 1`. -/
theorem pclose_attained (η : Site d → ℤ) (x : Site d) (a : ℕ)
    (haeq : lastArrival η (0 : Site d) x = (a : ℕ∞)) :
    1 ≤ a ∧ 0 < lastWave η (0 : Site d) a x := by
  have hne : ∃ n : ℕ, 1 ≤ n ∧ 0 < lastWave η (0 : Site d) n x := by
    by_contra h
    have htop := sInf_coe_top
      (P := fun n : ℕ => 1 ≤ n ∧ 0 < lastWave η (0 : Site d) n x) h
    have : lastArrival η (0 : Site d) x = ⊤ := htop
    rw [this] at haeq
    exact absurd haeq (by simp)
  obtain ⟨n, ⟨hn1, hpos⟩, hn_eq⟩ := sInf_coe_attained
    (P := fun n : ℕ => 1 ≤ n ∧ 0 < lastWave η (0 : Site d) n x) hne
  have hn_eq' : (n : ℕ∞) = (a : ℕ∞) := by
    have : lastArrival η (0 : Site d) x = (n : ℕ∞) := hn_eq
    rw [← this, haeq]
  have hn_a : n = a := (Nat.cast_inj (R := ℕ∞)).mp hn_eq'
  subst hn_a
  exact ⟨hn1, hpos⟩

/-- A wave that is positive somewhere has positive mass. -/
theorem pclose_mass_pos (η : Site d → ℤ) (hhigh : ∀ y, η y ≤ 2 * (d : ℤ) - 1)
    (hd0 : (0 : ℤ) < 2 * (d : ℤ)) (N : ℕ) (z : Site d) (t : ℕ) (x : Site d)
    (h : 0 < wave η N z t x) : 1 ≤ N := by
  by_contra hN
  have hN0 : N = 0 := by omega
  subst hN0
  have := wave_le_n η hhigh hd0 0 z t x
  simp only [Nat.cast_zero] at this
  omega

/-- A nonnegative integer bounded by a real is bounded by its floor. -/
theorem pclose_abs_le_floor (γ5 ℓ : ℝ) (u : ℤ) (h : ((|u| : ℤ) : ℝ) ≤ ℓ ^ γ5) :
    |u| ≤ ((⌊ℓ ^ γ5⌋₊ : ℕ) : ℤ) := by
  have h0 : (0 : ℤ) ≤ |u| := abs_nonneg u
  have hm : (((|u|).toNat : ℕ) : ℤ) = |u| := Int.toNat_of_nonneg h0
  have h1' : (((|u|).toNat : ℤ) : ℝ) ≤ ℓ ^ γ5 := by rw [hm]; exact h
  have h1 : (((|u|).toNat : ℕ) : ℝ) ≤ ℓ ^ γ5 := by exact_mod_cast h1'
  have h2 : (|u|).toNat ≤ ⌊ℓ ^ γ5⌋₊ := Nat.le_floor h1
  rw [← hm]
  exact_mod_cast h2

/-- The scale facts used in the assembly. -/
theorem pclose_scale_facts (e0 : ℝ) (he0 : 5 / 2 ≤ e0) (K0 n : ℕ) (hl : 1 ≤ Real.log (n : ℝ))
    (hn : 2 ≤ n) (γ5 : ℝ) (hγ5 : γ5 ≤ e0) :
    K0 ≤ pcloseZ e0 K0 n ∧
    Real.log (2 * (n : ℝ)) ^ ((5 : ℝ) / 2) ≤ (pcloseZ e0 K0 n : ℝ) ∧
    Real.log (2 * (n : ℝ)) ^ (2 : ℕ) ≤ (pcloseZ e0 K0 n : ℝ) ∧
    Real.log (n : ℝ) ^ γ5 ≤ (pcloseZ e0 K0 n : ℝ) := by
  have he0' : (0 : ℝ) ≤ e0 := by linarith
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hℓ0 : (0 : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hℓ2 : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hℓ21 : (1 : ℝ) ≤ Real.log (2 * (n : ℝ)) := le_trans hl hℓ2
  have hceil : Real.log (2 * (n : ℝ)) ^ e0 ≤ (pcloseZ e0 K0 n : ℝ) := by
    unfold pcloseZ
    push_cast
    have := Nat.le_ceil (Real.log (2 * (n : ℝ)) ^ e0)
    have hK : (0 : ℝ) ≤ (K0 : ℝ) := Nat.cast_nonneg K0
    linarith
  refine ⟨by unfold pcloseZ; omega, ?_, ?_, ?_⟩
  · exact le_trans (Real.rpow_le_rpow_of_exponent_le hℓ21 he0) hceil
  · have : Real.log (2 * (n : ℝ)) ^ (2 : ℕ) = Real.log (2 * (n : ℝ)) ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [this]
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hℓ21 (by linarith)) hceil
  · calc Real.log (n : ℝ) ^ γ5 ≤ Real.log (n : ℝ) ^ e0 :=
          Real.rpow_le_rpow_of_exponent_le hl hγ5
      _ ≤ Real.log (2 * (n : ℝ)) ^ e0 := Real.rpow_le_rpow hℓ0 hℓ2 he0'
      _ ≤ _ := hceil

/-- **The second inequality, for a fixed scale.**  Every site of the penultimate cluster `P` of
`x` is positive for the last wave at time `a + Z^E1`, where `a = T̂(x)`: for `x` far from the
centre by the far case, and for `x` near the centre by the linear bound on `T̂`. -/
theorem pclose_core_det (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d)) (hgood : ∀ j ∈ Cinf, GoodAt η k j)
    (n Z Cc Cn R E E1 : ℕ) (hZ2 : 2 ≤ Z) (hkZ : k ≤ Z) (hCnZ : Cn ≤ Z)
    (hdZ : d ≤ Z) (hRZ : R ≤ Z)
    (hE : pcloseT d k Cc Z ((k * (Z + 2)) ^ d) ≤ Z ^ E)
    (hEE : E ≤ E1) (hE3 : 3 * d + 3 ≤ E1) (hsize : 5 * Z ^ E1 ≤ n)
    (hhole : ∀ y ∈ (cent d (2 * n) : Set (Site d)), y ∉ Cinf →
      (componentIn Cinfᶜ y).Finite ∧ (componentIn Cinfᶜ y).ncard < Z)
    (hchem : ∀ y ∈ Cinf, ∀ y' ∈ Cinf, mnorm y ≤ ((2 * n : ℕ) : ℤ) → (Z : ℤ) ≤ mnorm (y - y') →
      ∃ m : ℕ, chemDist Cinf y y' = (m : ℕ∞) ∧ (m : ℤ) ≤ (Cc : ℤ) * mnorm (y - y'))
    (C6 ℓ6 : ℝ) (hC6 : C6 ≤ Cn) (hℓ6 : ℓ6 ≤ Z)
    (hub : ∀ w : Site d, mnorm w ≤ (n : ℤ) →
      ∃ m : ℕ, lastArrival η (0 : Site d) w = (m : ℕ∞) ∧ (m : ℝ) ≤ C6 * mnorm w + ℓ6)
    (x : Site d) (hxn : mnorm x ≤ (n : ℤ)) (a : ℕ)
    (ha : lastArrival η (0 : Site d) x = (a : ℕ∞))
    (P : Set (Site d)) (hP : ∀ w ∈ P, ∀ i, |w i - x i| ≤ (R : ℤ)) :
    ∀ w ∈ P, 0 < lastWave η (0 : Site d) (a + Z ^ E1) w := by
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hη0 : ∀ y, 0 ≤ η y := fun y => by linarith [hlow y]
  have hZ1 : 1 ≤ Z := by omega
  obtain ⟨ha1, hapos⟩ := pclose_attained η x a ha
  have hN : 1 ≤ waveThreshold η (0 : Site d) :=
    pclose_mass_pos η hhigh hd0 _ 0 a x hapos
  set L := (k * (Z + 2)) ^ d with hL
  -- the size bounds
  have hLZ : L ≤ Z ^ E1 :=
    le_trans (pclose_L_le d k Z hZ2 hkZ) (Nat.pow_le_pow_right hZ1 (by omega))
  have hZZ : Z ≤ Z ^ E1 := by
    calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ Z ^ E1 := Nat.pow_le_pow_right hZ1 (by omega)
  have hZ2E : Z ^ 2 ≤ Z ^ E1 := Nat.pow_le_pow_right hZ1 (by omega)
  have hdZZ : d * Z ≤ Z ^ E1 := by
    calc d * Z ≤ Z * Z := Nat.mul_le_mul_right _ hdZ
      _ = Z ^ 2 := by ring
      _ ≤ Z ^ E1 := hZ2E
  have h4 : 4 ≤ Z ^ E1 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ Z ^ 2 := Nat.pow_le_pow_left hZ2 2
      _ ≤ Z ^ E1 := hZ2E
  have hsize' : (L + Z + Z + d + 3 : ℕ) ≤ n := by omega
  intro w hw
  by_cases hfar : (L : ℤ) ≤ mnorm x
  · -- the far case
    have hn1 : mnorm x + ((L + Z + Z + d + 3 : ℕ) : ℤ) ≤ ((2 * n : ℕ) : ℤ) := by
      have : ((L + Z + Z + d + 3 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hsize'
      push_cast; linarith
    have hfarres := pclose_far hd η hlow hhigh _ hN k hk Cinf hgood Z (2 * n) Cc R hRZ hhole
      hchem x a hapos L hL hfar hn1 w (hP w hw)
    have hle : a + pcloseT d k Cc Z L ≤ a + Z ^ E1 :=
      Nat.add_le_add_left (le_trans hE (Nat.pow_le_pow_right hZ1 hEE)) a
    exact pclose_pos_mono hd0 η hη0 _ 0 hle hfarres
  · -- the near case
    push Not at hfar
    have hwx : mnorm (w - x) ≤ (d : ℤ) * (R : ℤ) :=
      pclose_mnorm_le_of_coord w x R (fun l => hP w hw l)
    have hwn : mnorm w ≤ (L : ℤ) + (d : ℤ) * (R : ℤ) := by
      have h1 : w = x + (w - x) := by abel
      have h2 := pclose_mnorm_add_le x (w - x)
      rw [← h1] at h2
      linarith
    have hdR : d * R ≤ d * Z := Nat.mul_le_mul_left _ hRZ
    have hwn' : mnorm w ≤ (n : ℤ) := by
      have : (L : ℤ) + (d : ℤ) * (R : ℤ) ≤ (n : ℤ) := by
        have : L + d * R ≤ n := by omega
        exact_mod_cast this
      linarith
    obtain ⟨m, hm, hmle⟩ := hub w hwn'
    obtain ⟨hm1, hmpos⟩ := pclose_attained η w m hm
    -- `m ≤ Z ^ E1`
    have hmZ : m ≤ Z ^ E1 := by
      have hw0 : 0 ≤ mnorm w := pclose_mnorm_nonneg w
      have hwn2 : mnorm w ≤ (((L + d * Z : ℕ)) : ℤ) := by
        have : (d : ℤ) * (R : ℤ) ≤ (d : ℤ) * (Z : ℤ) := by exact_mod_cast hdR
        push_cast; linarith
      have hreal : (m : ℝ) ≤ ((Cn * (L + d * Z) + Z : ℕ) : ℝ) := by
        have h1 : C6 * mnorm w ≤ (Cn : ℝ) * ((L + d * Z : ℕ) : ℝ) := by
          have h2 : (mnorm w : ℝ) ≤ ((L + d * Z : ℕ) : ℝ) := by exact_mod_cast hwn2
          have h3 : (0 : ℝ) ≤ (mnorm w : ℝ) := by exact_mod_cast hw0
          calc C6 * (mnorm w : ℝ) ≤ (Cn : ℝ) * (mnorm w : ℝ) :=
                mul_le_mul_of_nonneg_right hC6 h3
            _ ≤ (Cn : ℝ) * ((L + d * Z : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
        push_cast at h1 ⊢
        linarith
      have hnat : m ≤ Cn * (L + d * Z) + Z := by exact_mod_cast hreal
      have hCn1 : Cn ≤ Z ^ 1 := by simpa using hCnZ
      have hL3 : L ≤ Z ^ (3 * d) := pclose_L_le d k Z hZ2 hkZ
      have hdZ2 : d * Z ≤ Z ^ (3 * d) := by
        calc d * Z ≤ Z * Z := Nat.mul_le_mul_right _ hdZ
          _ = Z ^ 2 := by ring
          _ ≤ Z ^ (3 * d) := Nat.pow_le_pow_right hZ1 (by omega)
      have hsum : L + d * Z ≤ Z ^ (3 * d + 1) := pclose_pb_add hZ2 hL3 hdZ2
      have hprod : Cn * (L + d * Z) ≤ Z ^ (1 + (3 * d + 1)) := pclose_pb_mul hCn1 hsum
      have hfin : Cn * (L + d * Z) + Z ≤ Z ^ (3 * d + 3) :=
        pclose_pb_add hZ2 (pclose_pb_mono hZ1 (by omega) hprod)
          (pclose_pb_mono hZ1 (by omega) (by simp : Z ≤ Z ^ 1))
      exact le_trans hnat (le_trans hfin (Nat.pow_le_pow_right hZ1 hE3))
    have hle : m ≤ a + Z ^ E1 := by omega
    exact pclose_pos_mono hd0 η hη0 _ 0 hle hmpos

end Exploding
