/-
The second inequality of Lemma 3.7 (`exploding.tex:828-835`): almost surely, for all large
`n` and `|x| ≤ n`, the penultimate-cluster arrival time `T̃(x)` is at most `T̂(x) + (log n)^γ`.

It rests on Lemma 3.5 (the penultimate cluster lies in a polylogarithmic box about `x`),
Lemma 3.6 (the linear bound on `T̂`, used near the origin) and Proposition 2.2 (the infinite
cluster of good cubes, with small holes and a linear chemical distance), all of which are
frozen statements used here as inputs.
-/
import Exploding.Support.PCloseProofMain

open Exploding LatticeProb MeasureTheory

namespace Exploding

/-- **The second inequality of Lemma 3.7.** -/
theorem pclose_second (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
          clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ := by
  obtain ⟨γ5, hγ5, hclu⟩ :=
    Exploding.Frozen.last_penultimate_cluster d hd p hp hp1.le hLSSB hHole hChem
  obtain ⟨γ6, C6, hγ6, hC6, hub⟩ :=
    Exploding.Frozen.penultimate_upper_bound d hd p hp hp1 hLSSB hHole hChem
  obtain ⟨k0, hk0⟩ := Exploding.Frozen.renormalization_properties d hd p hp hp1 hLSSB hHole hChem
  obtain ⟨c, C, hc, hC, hren⟩ := hk0 (max k0 1) (le_max_left _ _)
  have hk : 1 ≤ max k0 1 := le_max_right _ _
  obtain ⟨E, hE⟩ := pclose_T_le d (by omega)
  set k : ℕ := max k0 1 with hkdef
  set Cc : ℕ := ⌈C⌉₊ with hCcdef
  set Cn : ℕ := ⌈C6⌉₊ with hCndef
  set K0 : ℕ := k + Cc + Cn + d + 2 with hK0def
  set e0 : ℝ := max (5 / 2) (max γ5 γ6) with he0def
  have he0 : (5 / 2 : ℝ) ≤ e0 := le_max_left _ _
  have hγ5e : γ5 ≤ e0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hγ6e : γ6 ≤ e0 := le_trans (le_max_right _ _) (le_max_right _ _)
  set E1 : ℕ := max E (3 * d + 3) with hE1def
  obtain ⟨nstar, hnstar⟩ := pclose_eventually e0 he0 K0 E1
  have hE1pos : (1 : ℝ) ≤ (E1 : ℝ) := by
    have : 1 ≤ E1 := le_trans (by omega : 1 ≤ 3 * d + 3) (le_max_right _ _)
    exact_mod_cast this
  refine ⟨e0 * E1 + 1, by nlinarith, ?_⟩
  filter_upwards [hclu, hub, hren, aux_pub_reach_eta_bounds d p hp hp1] with
    η hη5 hη6 hηren hηbd
  obtain ⟨Cinf, hCinf, ⟨n0h, hhole⟩, ⟨n0c, hchem⟩⟩ := hηren
  obtain ⟨_, hCsub, _⟩ := hCinf
  obtain ⟨n05, hn5⟩ := hη5
  obtain ⟨n06, hn6⟩ := hη6
  refine ⟨max n05 (max n06 (max n0h (max n0c nstar))), fun n hn x hx => ?_⟩
  have hn05 : n05 ≤ n := le_trans (le_max_left _ _) hn
  have hn06 : n06 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn0h : n0h ≤ n := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hn
  have hn0c : n0c ≤ n := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hn
  have hnst : nstar ≤ n := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hn
  obtain ⟨hn2, hℓ1, hZpow, hsz⟩ := hnstar n hnst
  set Z : ℕ := pcloseZ e0 K0 n with hZdef
  obtain ⟨hK0Z, hhole5, hchem2, hℓ5⟩ := pclose_scale_facts e0 he0 K0 n hℓ1 hn2 γ5 hγ5e
  obtain ⟨-, -, -, hℓ6⟩ := pclose_scale_facts e0 he0 K0 n hℓ1 hn2 γ6 hγ6e
  have hZ2 : 2 ≤ Z := by omega
  have hkZ : k ≤ Z := by omega
  have hCcZ : Cc ≤ Z := by omega
  have hCnZ : Cn ≤ Z := by omega
  have hdZ : d ≤ Z := by omega
  -- the hole hypothesis at scale `2 n`
  have hholeZ : ∀ y ∈ (cent d (2 * n) : Set (Site d)), y ∉ Cinf →
      (componentIn Cinfᶜ y).Finite ∧ (componentIn Cinfᶜ y).ncard < Z := by
    intro y hy hyC
    obtain ⟨hfin, hcard⟩ := hhole (2 * n) (by omega) y hy hyC
    refine ⟨hfin, ?_⟩
    have h1 : ((componentIn Cinfᶜ y).ncard : ℝ) < (Z : ℝ) := by
      calc ((componentIn Cinfᶜ y).ncard : ℝ) < Real.log (((2 * n : ℕ) : ℝ)) ^ ((5 : ℝ) / 2) := hcard
        _ = Real.log (2 * (n : ℝ)) ^ ((5 : ℝ) / 2) := by push_cast; rfl
        _ ≤ (Z : ℝ) := hhole5
    exact_mod_cast h1
  -- the chemical distance hypothesis at scale `2 n`
  have hchemZ : ∀ y ∈ Cinf, ∀ y' ∈ Cinf, mnorm y ≤ ((2 * n : ℕ) : ℤ) → (Z : ℤ) ≤ mnorm (y - y') →
      ∃ m : ℕ, chemDist Cinf y y' = (m : ℕ∞) ∧ (m : ℤ) ≤ (Cc : ℤ) * mnorm (y - y') := by
    intro y hy y' hy' hyn hZd
    have hlog : Real.log (((2 * n : ℕ) : ℝ)) ^ (2 : ℕ) ≤ ((mnorm (y - y') : ℤ) : ℝ) := by
      calc Real.log (((2 * n : ℕ) : ℝ)) ^ (2 : ℕ) = Real.log (2 * (n : ℝ)) ^ (2 : ℕ) := by
            push_cast; rfl
        _ ≤ (Z : ℝ) := hchem2
        _ ≤ ((mnorm (y - y') : ℤ) : ℝ) := by exact_mod_cast hZd
    obtain ⟨m, hm, -, hmC⟩ := hchem (2 * n) (by omega) y hy y' hy' hyn hlog
    refine ⟨m, hm, ?_⟩
    have hnn : (0 : ℝ) ≤ ((mnorm (y - y') : ℤ) : ℝ) := by
      exact_mod_cast pclose_mnorm_nonneg (y - y')
    have h1 : (m : ℝ) ≤ (Cc : ℝ) * ((mnorm (y - y') : ℤ) : ℝ) :=
      le_trans hmC (mul_le_mul_of_nonneg_right (Nat.le_ceil C) hnn)
    exact_mod_cast h1
  -- the linear bound at scale `n`
  have hubn : ∀ w : Site d, mnorm w ≤ (n : ℤ) → ∃ m : ℕ, lastArrival η (0 : Site d) w = (m : ℕ∞) ∧
      (m : ℝ) ≤ C6 * (mnorm w : ℝ) + Real.log (n : ℝ) ^ γ6 :=
    fun w hw => hn6 n hn06 w hw
  obtain ⟨a, ha, -⟩ := hn6 n hn06 x hx
  obtain ⟨ha1, -⟩ := pclose_attained η x a ha
  -- the penultimate cluster lies in a box
  set R : ℕ := ⌊Real.log (n : ℝ) ^ γ5⌋₊ with hRdef
  have hℓ0 : (0 : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hRZ : R ≤ Z := by
    have h1 : (R : ℝ) ≤ Real.log (n : ℝ) ^ γ5 := Nat.floor_le (Real.rpow_nonneg hℓ0 γ5)
    exact_mod_cast le_trans h1 hℓ5
  have hP : ∀ w ∈ penultimateCluster η x, ∀ i, |w i - x i| ≤ (R : ℤ) := fun w hw i =>
    pclose_abs_le_floor γ5 _ _ (hn5 n hn05 x hx w hw i)
  have hcov := pclose_core_det hd η (fun y => (hηbd y).1) (fun y => (hηbd y).2) k hk Cinf
    (fun j hj => hCsub hj) n Z Cc Cn R E E1 hZ2 hkZ hCnZ hdZ hRZ
    (hE Z k Cc hZ2 hkZ hCcZ hdZ) (le_max_left _ _) (le_max_right _ _) hsz hholeZ hchemZ
    C6 (Real.log (n : ℝ) ^ γ6) (Nat.le_ceil C6) hℓ6 hubn x hx a ha
    (penultimateCluster η x) hP
  have hcl : clusterArrival η (0 : Site d) x ≤ ((a + Z ^ E1 : ℕ) : ℕ∞) :=
    clusterArrival_le η (0 : Site d) x (a + Z ^ E1) (by omega) hcov
  have hne : clusterArrival η (0 : Site d) x ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.coe_ne_top) hcl
  obtain ⟨b, -, -, hbeq⟩ := clusterArrival_exists η (0 : Site d) x hne
  refine ⟨a, b, ha, hbeq, ?_⟩
  have hbnat : b ≤ a + Z ^ E1 := by
    rw [hbeq] at hcl
    exact_mod_cast hcl
  have hbreal : (b : ℝ) ≤ (a : ℝ) + (Z : ℝ) ^ E1 := by exact_mod_cast hbnat
  linarith [hZpow]

end Exploding
