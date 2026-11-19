import Exploding.Support.FiniteExplodingUnconditional

/-!
# Upper bounds for last-wave arrival times

Almost surely, last-wave arrival times grow at most linearly with a
polylogarithmic correction.
-/

open Exploding LatticeProb MeasureTheory

/-- The linear arrival-time bound for strict toy-law parameters. -/
theorem Exploding.pub_penultimate_upper_bound_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∃ m : ℕ, lastArrival η (0 : Site d) x = (m : ℕ∞) ∧
          (m : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ := by
  obtain ⟨kb, hkb⟩ := Exploding.renormalization_properties_unconditional d hd p hp hp1.le
  obtain ⟨c, Cr, hc, hCr, hae⟩ := hkb (max kb 2) (le_max_left kb 2)
  refine ⟨4, ((max kb 2 : ℕ) : ℝ) ^ d * Cr, by norm_num, ?_, ?_⟩
  · have : (0 : ℝ) < ((max kb 2 : ℕ) : ℝ) := by
      have : 0 < max kb 2 := lt_of_lt_of_le (by norm_num) (le_max_right kb 2)
      exact_mod_cast this
    positivity
  filter_upwards [hae, aux_pub_reach_eta_bounds d p hp hp1,
    Exploding.finite_exploding_unconditional d hd p hp hp1.le] with η hη hetabd hexplode
  obtain ⟨Cinf, hCinf, ⟨n0h, hn0h⟩, ⟨n0c, hn0c⟩, -, -⟩ := hη
  have hMmem := Nat.sInf_mem hexplode
  have hS : pub_Setup d η (waveThreshold η (0 : Site d)) (max kb 2) Cinf n0h n0c Cr :=
    { hd := hd
      hlow := fun x => (hetabd x).1
      hhigh := fun x => (hetabd x).2
      hN := hMmem.1
      hns := hMmem.2
      hk := le_max_right kb 2
      hCinf := hCinf
      hhole := hn0h
      hCr := hCr
      hchem := fun n hn x hx y hy hxn hfar => by
        obtain ⟨m, hm, -, hm2⟩ := hn0c n hn x hx y hy hxn hfar
        exact ⟨m, hm, hm2⟩ }
  obtain ⟨K, hK0, n1, hn1⟩ := pub_core hS
  set C2 : ℝ := 2 * (10 * (((max kb 2 : ℕ) : ℝ) ^ d * Cr) + ((max kb 2 : ℕ) : ℝ)) with hC2
  have hC20 : 0 ≤ C2 := by
    have : (0 : ℝ) ≤ ((max kb 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have := hCr.le
    positivity
  obtain ⟨N2, hN2⟩ := pub_eventually_final (max K C2) (le_trans hK0 (le_max_left _ _))
  refine ⟨max n1 N2, fun n hn x hx => ?_⟩
  obtain ⟨τ, hτ1, hτpos, hτle⟩ := hn1 n (le_trans (le_max_left _ _) hn) x hx
  have hfin := hN2 n (le_trans (le_max_right _ _) hn)
  have hex : ∃ t : ℕ, 1 ≤ t ∧ 0 < lastWave η (0 : Site d) t x := ⟨τ, hτ1, hτpos⟩
  obtain ⟨m, ⟨hm1, hm2⟩, hmeq⟩ := sInf_coe_attained
    (P := fun t : ℕ => 1 ≤ t ∧ 0 < lastWave η (0 : Site d) t x) hex
  have hmτ : m ≤ τ := by
    have := lastArrival_le η (0 : Site d) x τ hτ1 hτpos
    rw [lastArrival, hmeq] at this
    exact_mod_cast this
  refine ⟨m, hmeq, ?_⟩
  have h4 : Real.log n ^ (4 : ℝ) = Real.log n ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  rw [h4]
  have hmR : (m : ℝ) ≤ τ := by exact_mod_cast hmτ
  have hL3 : (0 : ℝ) ≤ Real.log n ^ 3 := pow_nonneg (Real.log_natCast_nonneg n) 3
  have hmax1 : K ≤ max K C2 := le_max_left _ _
  have hmax2 : C2 ≤ max K C2 := le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_right hmax2 hL3]

/-- Last-wave arrival times satisfy the linear bound. -/
theorem Exploding.penultimate_upper_bound_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∃ m : ℕ, lastArrival η (0 : Site d) x = (m : ℕ∞) ∧
          (m : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ
:= by
  rcases lt_or_eq_of_le hp1 with hlt | heq
  · exact Exploding.pub_penultimate_upper_bound_unconditional d hd p hp hlt
  · subst heq
    exact Exploding.penultimate_upper_bound_p1 d hd
