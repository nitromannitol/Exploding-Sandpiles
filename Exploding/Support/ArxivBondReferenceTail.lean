import Exploding.Support.ArxivBondReferencePath
import Exploding.Support.ArxivBondClusterUnionTail

/-!
# Bad-cluster tail along a short reference set

A shortest lattice path supplies a star-connected reference set with linear
size, to which the high-density estimate for unions of bad cube clusters applies.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- At high density, bad star-connected sets touching a short reference set
have a union whose size has a geometric tail at the endpoint distance scale. -/
theorem bond_bad_cluster_union_tail_along_reference (d : ℕ) (hd : 1 ≤ d) :
    ∃ q0 : ℝ, 0 ≤ q0 ∧ q0 < 1 ∧ ∀ (x y : Site d),
      ∃ P : Finset (Site d), x ∈ P ∧ y ∈ P ∧ xmh_SConn (P : Set (Site d)) ∧
        P.card ≤ (mnorm (x - y)).toNat + 1 ∧
        ∀ q : ℝ, q0 ≤ q → q ≤ 1 →
          bondPercolation d q
            {ω | ∃ G : Set (Set (Site d)),
              (∀ A ∈ G, xmh_SConn A ∧ (∃ z ∈ P, z ∈ A) ∧
                ∀ z ∈ A, ¬ xap_Good ω z) ∧
              ((2 * 3 ^ d * ((mnorm (x - y)).toNat + 1) : ℕ) : ℕ∞) ≤
                ((P : Set (Site d)) ∪ ⋃ A ∈ G, A).encard} ≤
            (1 / 2 : ENNReal) ^ ((mnorm (x - y)).toNat + 1) := by
  obtain ⟨q0, hq0, hq01, htail⟩ := bond_bad_cluster_union_geometric_at_high_density d
  refine ⟨q0, hq0, hq01, fun x y => ?_⟩
  obtain ⟨P, hx, hy, hconn, hcard⟩ := exists_short_star_connected_set hd x y
  refine ⟨P, hx, hy, hconn, hcard, fun q hq hq1 => ?_⟩
  apply htail q hq hq1 x P hx hconn ((mnorm (x - y)).toNat + 1) (by omega)
  have hpow : 1 ≤ 3 ^ d := Nat.one_le_pow d 3 (by omega)
  calc
    P.card ≤ (mnorm (x - y)).toNat + 1 := hcard
    _ ≤ 3 ^ d * ((mnorm (x - y)).toNat + 1) := by
      simpa using Nat.mul_le_mul_right ((mnorm (x - y)).toNat + 1) hpow

end Exploding
