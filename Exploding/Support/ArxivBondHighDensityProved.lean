import Exploding.Support.ArxivBondHaloDistance
import Exploding.Support.ExtAPProof12

/-!
# The high-density chemical-distance bound

A confined-walk bound and the geometric halo tail imply an exponential
chemical-distance estimate at high bond density.
-/

open LatticeProb MeasureTheory

namespace Exploding

private theorem half_pow_le_exp (n : ℕ) :
    (1 / 2 : ENNReal) ^ (n + 1) ≤
      ENNReal.ofReal (Real.exp (-(Real.log 2 * (n : ℝ)))) := by
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    rw [one_div, one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hexp : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have heq : (1 / 2 : ENNReal) ^ n =
      ENNReal.ofReal (Real.exp (-(Real.log 2 * (n : ℝ)))) := by
    have he : Real.exp (-(Real.log 2 * (n : ℝ))) = (1 / 2 : ℝ) ^ n := by
      calc
        _ = Real.exp ((n : ℝ) * -Real.log 2) := by congr 1; ring
        _ = (Real.exp (-Real.log 2)) ^ n := Real.exp_nat_mul _ _
        _ = _ := by rw [hexp]
    rw [he, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), hhalf]
  calc
    (1 / 2 : ENNReal) ^ (n + 1) = (1 / 2 : ENNReal) ^ n * (1 / 2) := by rw [pow_succ]
    _ ≤ (1 / 2 : ENNReal) ^ n * 1 := by
      gcongr
      norm_num
    _ = _ := by simpa only [mul_one] using heq

/-- The chemical-distance bound holds uniformly at sufficiently high bond density. -/
theorem xap12_high_density_bound :
    xap12_HighDensityBound := by
  intro d hd
  obtain ⟨q0, _, hq0, htail⟩ := bond_bad_cluster_halo_tail d (by omega)
  refine ⟨q0, hq0, fun q hq hq1 => ?_⟩
  let B : ℕ := 3 ^ d
  let C : ℕ := B ^ 2
  have hB : 1 ≤ B := Nat.one_le_pow d 3 (by omega)
  have hC : 1 ≤ C := Nat.one_le_pow 2 B hB
  refine ⟨(4 * B * C : ℕ), Real.log 2, ?_, Real.log_pos (by norm_num), 1,
    fun y hy => ?_⟩
  · exact_mod_cast (show 1 ≤ 4 * B * C by nlinarith)
  have hynonneg : (0 : ℤ) ≤ mnorm y := by omega
  have hncast : (((mnorm y).toNat : ℕ) : ℤ) = mnorm y := Int.toNat_of_nonneg hynonneg
  have hn : 1 ≤ (mnorm y).toNat := by omega
  have hnorm : mnorm ((0 : Site d) - y) = mnorm y := by
    simp only [zero_sub, mnorm, Pi.neg_apply, abs_neg]
  obtain ⟨P, h0, hyP, hP, hPnn, _, hprob⟩ := htail 0 y
  rw [hnorm] at hprob
  have hsubset : {ω | xap12_BigDistance d (4 * B * C : ℕ) ω y} ⊆
      {ω | ((2 * B * ((mnorm y).toNat + 1) : ℕ) : ℕ∞) ≤
        (bondBadClusterHalo ω P).encard} := by
    intro ω hω
    obtain ⟨m, hm, hlarge⟩ := hω
    have hreach : (openBondGraph ω).Reachable 0 y := by
      apply SimpleGraph.reachable_of_edist_ne_top
      rw [hm]
      exact ENat.natCast_ne_top m
    have hdist := open_bond_edist_le_bad_cluster_halo (by omega) h0 hyP hP hreach
    rw [hm] at hdist
    by_contra hsize
    have hlt : (bondBadClusterHalo ω P).encard <
        ((2 * B * ((mnorm y).toNat + 1) : ℕ) : ℕ∞) := lt_of_not_ge hsize
    have hle : (bondBadClusterHalo ω P).encard ≤
        ((2 * B * ((mnorm y).toNat + 1) : ℕ) : ℕ∞) := le_of_lt hlt
    have hdist' : (m : ℕ∞) ≤
        (((2 * B * ((mnorm y).toNat + 1)) * C : ℕ) : ℕ∞) := by
      apply hdist.trans
      calc
        (bondBadClusterHalo ω P).encard * (((3 ^ d) ^ 2 : ℕ) : ℕ∞) ≤
            ((2 * B * ((mnorm y).toNat + 1) : ℕ) : ℕ∞) *
              (((3 ^ d) ^ 2 : ℕ) : ℕ∞) := by gcongr
        _ = _ := by simp only [B, C, Nat.cast_mul]
    have hnat : m ≤ (2 * B * ((mnorm y).toNat + 1)) * C := by exact_mod_cast hdist'
    have harith : (2 * B * ((mnorm y).toNat + 1)) * C ≤
        (4 * B * C) * (mnorm y).toNat := by nlinarith
    have hreal : (m : ℝ) ≤ (4 * B * C : ℕ) * (mnorm y : ℝ) := by
      have hmnat := le_trans hnat harith
      have hmc : (((mnorm y).toNat : ℕ) : ℝ) = (mnorm y : ℝ) := by exact_mod_cast hncast
      have hcast : (m : ℝ) ≤ (4 * B * C : ℕ) * (((mnorm y).toNat : ℕ) : ℝ) := by
        exact_mod_cast hmnat
      simpa only [hmc] using hcast
    exact (not_lt_of_ge hreal) hlarge
  calc
    bondPercolation d q {ω | xap12_BigDistance d (4 * B * C : ℕ) ω y} ≤
        bondPercolation d q {ω | ((2 * B * ((mnorm y).toNat + 1) : ℕ) : ℕ∞) ≤
          (bondBadClusterHalo ω P).encard} := measure_mono hsubset
    _ ≤ (1 / 2 : ENNReal) ^ ((mnorm y).toNat + 1) := hprob q (le_of_lt hq) hq1
    _ ≤ ENNReal.ofReal (Real.exp (-(Real.log 2 * ((mnorm y).toNat : ℝ)))) :=
      half_pow_le_exp _
    _ = ENNReal.ofReal (Real.exp (-(Real.log 2 * (mnorm y : ℝ)))) := by
      have hmc : (((mnorm y).toNat : ℕ) : ℝ) = (mnorm y : ℝ) := by exact_mod_cast hncast
      rw [hmc]

end Exploding
