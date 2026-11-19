import Exploding.Support.PenultimateClusterUnconditional
import Exploding.Support.PenultimateUpperBoundUnconditional

/-!
# Comparison of arrival times

The arrival times of the full process and the last wave differ by bounded
amounts almost surely.
-/

open Exploding LatticeProb MeasureTheory
open scoped Classical

/-- The penultimate cluster of the origin is almost surely finite. -/
theorem Exploding.as_penultimateCluster_finite_unconditional
    (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    :
    ∀ᵐ η ∂(toyLaw d p), (penultimateCluster η (0 : Site d)).Finite := by
  obtain ⟨γ, _hγ, hren⟩ :=
    Exploding.last_penultimate_cluster_unconditional d hd p hp hp1.le
  filter_upwards [hren] with η hη
  obtain ⟨n0, hn0⟩ := hη
  set n : ℕ := max n0 1 with hn
  have hn0le : n0 ≤ n := le_max_left _ _
  have hmnorm : mnorm (0 : Site d) ≤ (n : ℤ) := by
    have h0 : mnorm (0 : Site d) = 0 := by simp [mnorm]
    rw [h0]
    exact_mod_cast Nat.zero_le n
  refine as_coord_bdd_finite (0 : Site d) (Real.log n ^ γ) _ ?_
  intro y hy i
  simpa using hn0 n hn0le (0 : Site d) hmnorm y hy i

/-- The last wave reaches the auxiliary finite set at one time. -/
theorem Exploding.as3_hlastreach_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    :
    ∀ᵐ η ∂(toyLaw d p), ∃ c : ℕ, ∀ x ∈ as_tildeP η, 1 ≤ lastWave η (0 : Site d) c x := by
  obtain ⟨γ, C, _hγ, _hC, hae⟩ :=
    pub_penultimate_upper_bound_unconditional d hd p hp hp1
  filter_upwards [hae, as_eta_bounds d hd p hp hp1] with η hreach hb
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hb x).2
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [(hb x).1]
  have hfin : (as_tildeP η).Finite := as3_tildeP_finite η hhigh
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have h1 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  obtain ⟨n0, hn0⟩ := hreach
  set B : ℕ := hfin.toFinset.sup (fun x => (mnorm x).toNat) with hB
  set n : ℕ := max n0 B with hn
  have hn0n : n0 ≤ n := le_max_left _ _
  have hmem_bound : ∀ x ∈ as_tildeP η, mnorm x ≤ (n : ℤ) := by
    intro x hx
    have hxB : mnorm x ≤ (B : ℤ) := by
      have h1 : (mnorm x).toNat ≤ B :=
        Finset.le_sup (f := fun x => (mnorm x).toNat) (hfin.mem_toFinset.mpr hx)
      have h2 := pub_mnorm_nonneg x
      rw [← Int.toNat_of_nonneg h2]
      exact_mod_cast h1
    have hBle : (B : ℤ) ≤ (n : ℤ) := by exact_mod_cast le_max_right n0 B
    linarith
  have hex : ∀ x : Site d, x ∈ as_tildeP η →
      ∃ m : ℕ, 1 ≤ m ∧ 0 < lastWave η (0 : Site d) m x := by
    intro x hx
    obtain ⟨m, hm, _⟩ := hn0 n hn0n x (hmem_bound x hx)
    have hla : lastArrival η (0 : Site d) x = (m : ℕ∞) := hm
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have htop : lastArrival η (0 : Site d) x = ⊤ := by
      unfold lastArrival
      exact sInf_coe_top (by rintro ⟨m', hm'⟩; exact hcon m' hm'.1 hm'.2)
    rw [htop] at hla
    exact (by simp : (m : ℕ∞) ≠ ⊤) hla.symm
  let mOf : Site d → ℕ := fun x =>
    if hx : x ∈ as_tildeP η then Classical.choose (hex x hx) else 0
  have hmOf : ∀ x (hx : x ∈ as_tildeP η),
      1 ≤ mOf x ∧ 0 < lastWave η (0 : Site d) (mOf x) x := by
    intro x hx
    simp only [mOf, dite_eq_left hx]
    exact Classical.choose_spec (hex x hx)
  refine ⟨hfin.toFinset.sup mOf, fun x hx => ?_⟩
  have h1 : mOf x ≤ hfin.toFinset.sup mOf :=
    Finset.le_sup (f := mOf) (hfin.mem_toFinset.mpr hx)
  have h2 : (1 : ℤ) ≤ lastWave η (0 : Site d) (mOf x) x := by
    have hpos := (hmOf x hx).2
    omega
  have h3 : lastWave η (0 : Site d) (mOf x) x ≤
      lastWave η (0 : Site d) (hfin.toFinset.sup mOf) x :=
    wave_mono_time η hlow0 hd0 (waveThreshold η (0 : Site d)) (0 : Site d) h1 x
  linarith


/-- The last wave almost surely reaches every site. -/
theorem Exploding.asd_reach_ae_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, ∃ m : ℕ, 0 < lastWave η (0 : Site d) m x := by
  obtain ⟨γ, C, _hγ, _hC, hae⟩ :=
    pub_penultimate_upper_bound_unconditional d hd p hp hp1
  filter_upwards [hae] with η hreach x
  obtain ⟨n0, hn0⟩ := hreach
  have hxnn : 0 ≤ mnorm x := pub_mnorm_nonneg x
  have hxle : mnorm x ≤ ((max n0 (mnorm x).toNat : ℕ) : ℤ) := by
    have h1 : mnorm x ≤ (((mnorm x).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hxnn]
    have h2 : (((mnorm x).toNat : ℕ) : ℤ) ≤ ((max n0 (mnorm x).toNat : ℕ) : ℤ) := by
      exact_mod_cast le_max_right n0 (mnorm x).toNat
    linarith
  obtain ⟨m, hm, _⟩ := hn0 (max n0 (mnorm x).toNat) (le_max_left _ _) x hxle
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have htop : lastArrival η (0 : Site d) x = ⊤ := by
    unfold lastArrival
    exact sInf_coe_top (by rintro ⟨m', hm'⟩; have := hcon m'; have := hm'.2; omega)
  rw [htop] at hm
  exact (by simp : (m : ℕ∞) ≠ ⊤) hm.symm

/-- The arrival-time comparison for strict parameters. -/
theorem Exploding.asd_approximate_subadditive_unconditional
    (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    :
    ∀ᵐ η ∂(toyLaw d p), ∃ C1 C2 : ℕ, ∀ x : Site d,
      arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
        lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞) := by
  filter_upwards [as_eta_bounds d hd p hp hp1,
    Exploding.finite_exploding_unconditional d hd p hp hp1.le,
    as_penultimateCluster_finite_unconditional d hd p hp hp1,
    as3_hlastreach_unconditional d hd p hp hp1,
    asd_reach_ae_unconditional d hd p hp hp1] with η hbounds hlast hPfin hlastreach hreach
  have hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x := fun x => (hbounds x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hbounds x).2
  have hnotrobust : ¬ Robust η := by
    intro hrob
    obtain ⟨n, hn1, hnstab⟩ := hlast
    exact hnstab (as4_hrobust d hd η hlow hhigh hrob n hn1)
  have hexp1 : 1 ≤ explosionThreshold η := (as_explosionThreshold_spec η hnotrobust).1
  obtain ⟨C1, hC1⟩ := as_ineq1 hd η hlow hhigh hlast
    (asd_hpodo_of_reach hd η hlow hhigh hnotrobust hlast hPfin hreach)
  obtain ⟨C2, hC2⟩ := as_ineq2 hd η hlow hhigh hlast hexp1
    hlastreach (as3_tildeP_finite η hhigh) (assp_special d hd η hlow hhigh)
  exact ⟨C1, C2, fun x => ⟨hC1 x, hC2 x⟩⟩

/-- The arrival times differ by finite random constants. -/
theorem Exploding.approximate_subadditive_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    :
    ∀ᵐ η ∂(toyLaw d p), ∃ C1 C2 : ℕ, ∀ x : Site d,
      arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
        lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞)
:= by
  rcases lt_or_eq_of_le hp1 with h | rfl
  · exact asd_approximate_subadditive_unconditional d hd p hp h
  · exact Exploding.approximate_subadditive_p1 d hd
