import Exploding.Support.ArxivBondClusterHalo
import Exploding.Support.ArxivBondAnimalThreshold

/-!
# A geometric tail for the bad-cluster halo

At high bond density, the halo along a short reference path has an
exponentially decaying size tail at the endpoint distance scale.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- A short reference set has a halo whose size has a geometric tail at high density. -/
theorem bond_bad_cluster_halo_tail (d : ℕ) (hd : 1 ≤ d) :
    ∃ q0 : ℝ, 0 ≤ q0 ∧ q0 < 1 ∧ ∀ (x y : Site d),
      ∃ P : Finset (Site d), x ∈ P ∧ y ∈ P ∧ xmh_SConn (P : Set (Site d)) ∧
        ((lattice d).induce (P : Set (Site d))).Connected ∧
        P.card ≤ (mnorm (x - y)).toNat + 1 ∧
        ∀ q : ℝ, q0 ≤ q → q ≤ 1 →
          bondPercolation d q
            {ω | ((2 * 3 ^ d * ((mnorm (x - y)).toNat + 1) : ℕ) : ℕ∞) ≤
              (bondBadClusterHalo ω P).encard} ≤
            (1 / 2 : ENNReal) ^ ((mnorm (x - y)).toNat + 1) := by
  obtain ⟨q0, hq0, hq01, htail⟩ := bond_connected_bad_cubes_geometric_at_high_density d
  refine ⟨q0, hq0, hq01, fun x y => ?_⟩
  obtain ⟨P, hx, hy, hconn, hlattice, hcard⟩ := exists_short_star_connected_set hd x y
  refine ⟨P, hx, hy, hconn, hlattice, hcard, fun q hq hq1 => ?_⟩
  have hpow : 1 ≤ 3 ^ d := Nat.one_le_pow d 3 (by omega)
  have hcard' : P.card ≤ 3 ^ d * ((mnorm (x - y)).toNat + 1) := by
    calc
      _ ≤ (mnorm (x - y)).toNat + 1 := hcard
      _ ≤ 3 ^ d * ((mnorm (x - y)).toNat + 1) := by
        simpa using Nat.mul_le_mul_right ((mnorm (x - y)).toNat + 1) hpow
  refine (measure_mono ?_).trans
    (htail q hq hq1 x P ((mnorm (x - y)).toNat + 1) (by omega) hcard')
  intro ω hsize
  exact ⟨bondBadClusterHalo ω P, bond_bad_cluster_halo_star_connected hconn,
    subset_bond_bad_cluster_halo ω P hx, hsize,
    fun z hz hzP => bad_of_mem_bond_bad_cluster_halo hz hzP⟩

end Exploding
