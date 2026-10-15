/-
Support for the far Lipschitz bound of Proposition 3.1: the almost sure statement.
The last-wave arrival times are Lipschitz up to a polylogarithm, `T̂(x') ≤ T̂(x) + C |x - x'| +
(log n)^γ` for `|x|, |x'| ≤ n` and `n` large (`lwcl_lastArrival_lip`); and then, through
Lemma 3.7, the same for the penultimate-cluster arrival times in the form needed by Proposition 3.1
(`lwcl_far_lipschitz`).
-/
import Exploding.Support.LWCLipC
import Exploding.Support.LWCProof

namespace Exploding

open LatticeProb MeasureTheory

/-- **The Lipschitz bound for the last-wave arrival times.** -/
theorem lwcl_lastArrival_lip (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x x' : Site d, mnorm x ≤ (n : ℤ) → mnorm x' ≤ (n : ℤ) →
        ∃ a a' : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
          lastArrival η (0 : Site d) x' = (a' : ℕ∞) ∧
            (a' : ℝ) ≤ (a : ℝ) + C * (mnorm (x - x') : ℝ) + Real.log n ^ γ := by
  obtain ⟨γ6, C6, hγ6, hC6, hub⟩ :=
    Exploding.Frozen.penultimate_upper_bound d hd p hp hp1 hLSSB hHole hChem
  obtain ⟨kb, hkb⟩ := Exploding.Frozen.renormalization_properties d hd p hp hp1 hLSSB hHole hChem
  obtain ⟨c, Cr, hc, hCr, hae⟩ := hkb (max kb 2) (le_max_left kb 2)
  have hd1 : 1 ≤ d := by omega
  set k : ℕ := max kb 2 with hkdef
  have hk2 : 2 ≤ k := le_max_right _ _
  set Cc : ℕ := ⌈Cr⌉₊ with hCcdef
  set Cn : ℕ := ⌈C6⌉₊ with hCndef
  set K0 : ℕ := k + Cc + Cn + d + 2 with hK0def
  set e0 : ℝ := max (5 / 2) γ6 with he0def
  have he0 : (5 / 2 : ℝ) ≤ e0 := le_max_left _ _
  have hγ6e : γ6 ≤ e0 := le_max_right _ _
  obtain ⟨E, hE⟩ := lwcl_E_le d hd1
  set E1 : ℕ := max E (3 * d + 3) with hE1def
  obtain ⟨nstar, hnstar⟩ := pclose_eventually e0 he0 K0 (E1 + 1)
  have he00 : (0 : ℝ) ≤ e0 * ((E1 + 1 : ℕ) : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  refine ⟨e0 * ((E1 + 1 : ℕ) : ℝ) + 1, max ((k : ℝ) ^ d * Cr) C6, by linarith,
    lt_max_of_lt_right hC6, ?_⟩
  filter_upwards [hae, hub, aux_pub_reach_eta_bounds d p hp hp1,
    Exploding.Frozen.finite_exploding d hd p hp hp1.le hLSSB hHole hChem] with
    η hη hubη hetabd hexplode
  obtain ⟨Cinf, hCinf, ⟨n0h, hhole⟩, ⟨n0c, hchem⟩⟩ := hη
  obtain ⟨n06, hn6⟩ := hubη
  have hMmem := Nat.sInf_mem hexplode
  have hS : pub_Setup d η (waveThreshold η (0 : Site d)) k Cinf n0h n0c Cr :=
    { hd := hd
      hlow := fun x => (hetabd x).1
      hhigh := fun x => (hetabd x).2
      hN := hMmem.1
      hns := hMmem.2
      hk := hk2
      hCinf := hCinf
      hhole := hhole
      hCr := hCr
      hchem := fun n hn x hx y hy hxn hfar => by
        obtain ⟨m, hm, -, hm2⟩ := hchem n hn x hx y hy hxn hfar
        exact ⟨m, hm, hm2⟩ }
  refine ⟨max n06 (max n0h (max n0c nstar)), fun n hn x x' hx hx' => ?_⟩
  have hn06 : n06 ≤ n := le_trans (le_max_left _ _) hn
  have hn0h : n0h ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn0c : n0c ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hn
  have hnst : nstar ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hn
  obtain ⟨hn2, hℓ1, hZpow, hsz⟩ := hnstar n hnst
  set Z : ℕ := pcloseZ e0 K0 n with hZdef
  obtain ⟨hK0Z, hhole5, -, hℓ6⟩ := pclose_scale_facts e0 he0 K0 n hℓ1 hn2 γ6 hγ6e
  have hZ2 : 2 ≤ Z := by omega
  have hkZ : k ≤ Z := by omega
  have hCcZ : Cc ≤ Z := by omega
  have hCnZ : Cn ≤ Z := by omega
  have hdZ : d ≤ Z := by omega
  have hZ1 : 1 ≤ Z := by omega
  have hsize : 8 * Z ^ E1 ≤ n := by
    have h1 : Z ^ (E1 + 1) = Z * Z ^ E1 := by ring
    have h2 : 2 * Z ^ E1 ≤ Z ^ (E1 + 1) := by
      rw [h1]; exact Nat.mul_le_mul_right _ hZ2
    omega
  have hholeZ : ∀ y ∈ (cent d (2 * n) : Set (Site d)), y ∉ Cinf →
      (componentIn Cinfᶜ y).Finite ∧ (componentIn Cinfᶜ y).ncard < Z := by
    intro y hy hyC
    obtain ⟨hfin, hcard⟩ := hhole (2 * n) (by omega) y hy hyC
    refine ⟨hfin, ?_⟩
    have h1 : ((componentIn Cinfᶜ y).ncard : ℝ) < (Z : ℝ) := by
      calc ((componentIn Cinfᶜ y).ncard : ℝ) < Real.log (((2 * n : ℕ) : ℝ)) ^ ((5 : ℝ) / 2) :=
          hcard
        _ = Real.log (2 * (n : ℝ)) ^ ((5 : ℝ) / 2) := by push_cast; rfl
        _ ≤ (Z : ℝ) := hhole5
    exact_mod_cast h1
  obtain ⟨a, ha, -⟩ := hn6 n hn06 x hx
  obtain ⟨a', ha', -⟩ := hn6 n hn06 x' hx'
  have hubn : ∀ w : Site d, mnorm w ≤ (n : ℤ) → ∃ m : ℕ, lastArrival η (0 : Site d) w = (m : ℕ∞) ∧
      (m : ℝ) ≤ C6 * (mnorm w : ℝ) + Real.log (n : ℝ) ^ γ6 :=
    fun w hw => hn6 n hn06 w hw
  obtain ⟨τ, hτ1, hτpos, hτle⟩ := lwcl_lip_core hd hS n Z Cc Cn E E1 hZ2 hkZ hCnZ hdZ
    (Nat.le_ceil Cr) (hE Z k Cc hZ2 hkZ hCcZ hdZ) (le_max_left _ _) (le_max_right _ _) hsize
    (by omega) (by omega) hhole5 hholeZ C6 (Real.log (n : ℝ) ^ γ6) hC6.le (Nat.le_ceil C6)
    hℓ6 hubn x x' hx hx' a ha
  refine ⟨a, a', ha, ha', ?_⟩
  have hle : lastArrival η (0 : Site d) x' ≤ (τ : ℕ∞) := lastArrival_le η (0 : Site d) x' τ hτ1 hτpos
  rw [ha'] at hle
  have hle' : a' ≤ τ := by exact_mod_cast hle
  have hleR : (a' : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hle'
  have hZE : (Z : ℝ) ^ E1 ≤ (Z : ℝ) ^ (E1 + 1) :=
    pow_le_pow_right₀ (by exact_mod_cast hZ1) (Nat.le_succ E1)
  linarith

end Exploding
