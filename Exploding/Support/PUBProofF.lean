/-
Support for Lemma 3.6 of `paper/exploding.tex`: the almost sure statement.  On the
almost sure event of Proposition 2.2, on which the last wave is well defined, the deterministic core
gives the linear bound on the last-wave arrival times.
-/
import Exploding.Support.PUBProofE
import Exploding.Frozen.Renormalization
import Exploding.Frozen.FiniteExploding
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

namespace Exploding

open LatticeProb MeasureTheory

/-- The statement of Lemma 3.6, proved from Proposition 2.2 and Lemma 3.2. -/
theorem pub_penultimate_upper_bound (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∃ m : ℕ, lastArrival η (0 : Site d) x = (m : ℕ∞) ∧
          (m : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ := by
  obtain ⟨kb, hkb⟩ := Exploding.Frozen.renormalization_properties d hd p hp hp1 hLSSB hHole hChem
  obtain ⟨c, Cr, hc, hCr, hae⟩ := hkb (max kb 2) (le_max_left kb 2)
  refine ⟨4, ((max kb 2 : ℕ) : ℝ) ^ d * Cr, by norm_num, ?_, ?_⟩
  · have : (0 : ℝ) < ((max kb 2 : ℕ) : ℝ) := by
      have : 0 < max kb 2 := lt_of_lt_of_le (by norm_num) (le_max_right kb 2)
      exact_mod_cast this
    positivity
  filter_upwards [hae, aux_pub_reach_eta_bounds d p hp hp1,
    Exploding.Frozen.finite_exploding d hd p hp hp1 hLSSB hHole hChem] with η hη hetabd hexplode
  obtain ⟨Cinf, hCinf, ⟨n0h, hn0h⟩, ⟨n0c, hn0c⟩⟩ := hη
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

end Exploding
