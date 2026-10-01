/-
Proposition 5.1 of the paper (generalized last wave): the last wave from the origin lights a tile of
the infinite cluster at some finite time.
-/
import Exploding.Support.GLWSec3V

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- **The first lit tile.**  The last wave from the origin, which does not stabilize, lights some
tile of `C_∞` at some finite time. -/
theorem glws_first_lit (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (Cinf : Set (Site d)) (hinf : Cinf.Infinite)
    (hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j)
    (hconn : ∀ x ∈ Cinf, ∀ y ∈ Cinf, y ∈ componentIn Cinf x)
    (n0h : ℕ) (hole : ∀ n : ℕ, n0h ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧ ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (γp : ℝ) (hγp : 0 < γp) (hpf : glws_PF d γp η) :
    ∃ j ∈ Cinf, ∃ τ0 : ℕ, glws_Fired η (waveThreshold η (0 : Site d)) k 0 τ0 j := by
  classical
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hlast := glws_finite_exploding hd η hlow hhigh k hk Cinf hinf hgood hconn (0 : Site d)
  have hne : {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)}.Nonempty := hlast
  have hmem : 1 ≤ waveThreshold η (0 : Site d) ∧
      ¬ WaveStabilizable η (waveThreshold η (0 : Site d)) (0 : Site d) := Nat.sInf_mem hne
  set N : ℕ := waveThreshold η (0 : Site d) with hN
  set kmax : ℕ := ∑ i, k i with hkmax
  obtain ⟨n0pt, hpt⟩ := glws_path_to_tile hd η hlow hhigh k hk Cinf hgood n0h hole γp hpf
  obtain ⟨n1, hn1⟩ := glws_asymp_Pn γp hγp kmax d
  set n : ℕ := max n1 n0pt with hn
  have hn1' : n1 ≤ n := le_max_left _ _
  have hn0pt : n0pt ≤ n := le_max_right _ _
  obtain ⟨h3, hPn⟩ := hn1 n hn1'
  set r : ℕ := glws_r2 n with hr
  set Pn : ℕ := glws_Pn γp kmax d n with hPn_def
  have hkmax1 : 1 ≤ kmax := by
    have h0 : 0 < d := by omega
    exact le_trans (hk ⟨0, h0⟩)
      (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  have hPn_ge : (kmax * (r + 2)) ^ d ≤ Pn := Nat.le_add_right _ _
  have hPn_ge2 : ⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ ≤ Pn := Nat.le_add_left _ _
  have hPn1 : 1 ≤ Pn := by
    have : 1 ≤ (kmax * (r + 2)) ^ d := Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (by omega))
    omega
  obtain ⟨t, y', hpos, hdev⟩ := glws_unbounded_of_not_stab hd η hlow hhigh N 0 hmem.2 Pn
  obtain ⟨p, z, hz0, hpD, hlit, hinj, hadj, hbd⟩ :=
    glws_exit_path η hlow hhigh hd0 N 0 t y' Pn hPn1 hpos hdev
  have hcent : ∀ i, i ≤ p → z i ∈ cent d (2 * n) := by
    intro i hi m
    have h1 := hbd i hi m
    simp only [Pi.zero_apply, sub_zero] at h1
    have h2 : (Pn : ℤ) ≤ (n : ℤ) := by exact_mod_cast hPn
    have h3 : (n : ℤ) ≤ ((2 * n : ℕ) : ℤ) := by push_cast; omega
    linarith
  have hlenR : Real.log ((2 * n : ℕ) : ℝ) ^ γp ≤ ((p + 1 : ℕ) : ℝ) := by
    have h1 : Real.log ((2 * n : ℕ) : ℝ) ^ γp ≤ ((⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ ≤ p + 1 := by omega
    exact le_trans h1 (by exact_mod_cast h2)
  have hS : ((∑ i, k i) * (r + 2)) ^ d ≤ p + 1 := by
    have h2 : (kmax * (r + 2)) ^ d ≤ p + 1 := by omega
    exact h2
  obtain ⟨j, hj, hfired, _⟩ := hpt (2 * n) (le_trans hn0pt (by omega)) r (Nat.le_ceil _) N
    (by omega) 0 t p z hcent (fun i j hi hj h => hinj i j hi hj h) hadj
    (fun i hi => hlit i hi) hlenR hS
  exact ⟨j, hj, _, hfired⟩

end Exploding
