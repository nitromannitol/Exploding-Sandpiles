import Exploding.Support.ArxivP1RenormGeometry
import Exploding.Support.ArxivAllHighCrossing
import Exploding.Support.RNProofCore

open Exploding LatticeProb

namespace Exploding

/-- If every macroscopic site is good, the full lattice is an infinite connected good set,
has no holes, has exact Manhattan chemical distance, and is its own good-site component. -/
theorem arxiv_all_good_renorm_geometry (d : ℕ) (hd : 2 ≤ d)
    (η : Site d → ℤ) (k : ℕ)
    (hgood : goodSites η k = Set.univ) (z : Site d) :
    IsInfiniteConnectedGoodSet η k Set.univ ∧
      RnHoleProp d Set.univ ∧
      RnChemClause d 1 Set.univ ∧
      componentIn (goodSites η k) z = Set.univ := by
  have hunivInfinite : (Set.univ : Set (Site d)).Infinite := by
    rw [← arxivAllHigh_goodSitesOne d hd]
    exact arxivAllHigh_goodSitesOne_infinite d hd
  have hcomponent : ∀ x y : Site d,
      y ∈ componentIn (Set.univ : Set (Site d)) x := by
    intro x y
    let m : ℕ := max (mnorm x).toNat (mnorm y).toNat
    have hxnonneg : 0 ≤ mnorm x := by
      unfold mnorm
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hynonneg : 0 ≤ mnorm y := by
      unfold mnorm
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hxm : mnorm x ≤ (m : ℤ) := by
      rw [(Int.toNat_of_nonneg hxnonneg).symm]
      exact_mod_cast (Nat.le_max_left (mnorm x).toNat (mnorm y).toNat)
    have hym : mnorm y ≤ (m : ℤ) := by
      rw [(Int.toNat_of_nonneg hynonneg).symm]
      exact_mod_cast (Nat.le_max_right (mnorm x).toNat (mnorm y).toNat)
    have hxcent : x ∈ cent d m := by
      intro i
      have hcoord : |x i| ≤ mnorm x := by
        unfold mnorm
        exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
      exact le_trans hcoord hxm
    have hycent : y ∈ cent d m := by
      intro i
      have hcoord : |y i| ≤ mnorm y := by
        unfold mnorm
        exact Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ i)
      exact le_trans hcoord hym
    exact cent_connected_in Set.univ m (Set.subset_univ _) x y hxcent hycent
  have hgoodSubset : (Set.univ : Set (Site d)) ⊆ goodSites η k := by
    rw [hgood]
  have hconnected : ∀ x ∈ (Set.univ : Set (Site d)),
      ∀ y ∈ (Set.univ : Set (Site d)), y ∈ componentIn Set.univ x := by
    intro x _ y _
    exact hcomponent x y
  have hInfiniteGood : IsInfiniteConnectedGoodSet η k Set.univ :=
    ⟨hunivInfinite, hgoodSubset, hconnected⟩
  have hholes : RnHoleProp d (Set.univ : Set (Site d)) := by
    refine ⟨0, ?_⟩
    intro n hn x hxcent hxnot
    exact (hxnot (Set.mem_univ x)).elim
  have hchemical : RnChemClause d 1 (Set.univ : Set (Site d)) := by
    refine ⟨0, ?_⟩
    intro n hn x hx y hy hxn hlog
    have hdist : chemDist (Set.univ : Set (Site d)) x y =
        ((mnorm (x - y)).toNat : ℕ∞) := by
      rw [arxivAllHigh_chemDist_eq_graphEdist, lattice_edist_eq_mnorm]
    have hnormNonneg : 0 ≤ mnorm (x - y) := by
      unfold mnorm
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hmcast : ((mnorm (x - y)).toNat : ℝ) = (mnorm (x - y) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnormNonneg
    refine ⟨(mnorm (x - y)).toNat, hdist, ?_, ?_⟩
    · rw [one_mul, hmcast]
    · rw [hmcast, one_mul]
  have hmaximal : componentIn (goodSites η k) z = Set.univ := by
    rw [hgood]
    exact Set.eq_univ_iff_forall.mpr (hcomponent z)
  exact ⟨hInfiniteGood, hholes, hchemical, hmaximal⟩

example (z : Site 2) :
    IsInfiniteConnectedGoodSet (fun _ : Site 2 => 3) 1 Set.univ ∧
      RnHoleProp 2 Set.univ ∧
      RnChemClause 2 1 Set.univ ∧
      componentIn (goodSites (fun _ : Site 2 => 3) 1) z = Set.univ := by
  have hvalue : 2 * (2 : ℤ) - 1 = 3 := by norm_num
  have hgood : goodSites (fun _ : Site 2 => 3) 1 = Set.univ := by
    simpa [hvalue] using arxivAllHigh_goodSitesOne 2 (by norm_num)
  exact arxiv_all_good_renorm_geometry 2 (by norm_num) _ 1 hgood z

end Exploding
