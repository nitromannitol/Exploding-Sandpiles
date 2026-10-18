import Exploding.Support.ArxivActualBondBoxCutoffAE
import Exploding.Support.ArxivCoreAttachment
import Exploding.Support.RNProofCore
import LatticeProb.Graph.Zd

/-!
# Logarithmic-square proximity to the actual infinite bond core

Almost surely, at every high bond density, there is one infinite actual open-bond cluster `I`
with `RnHoleProp` such that every vertex of a large centred box lies within the
logarithmic-square hole bound of a vertex of `I`.  The proximity walks are the finite-hole
attachment walks of `arxiv_core_attachment_of_finite_holes` with the ambient set `G = univ`.
-/

open LatticeProb MeasureTheory Filter

namespace Exploding

/-- The whole lattice is one component of `Set.univ`. -/
private theorem arxiv_proximity_univ_componentIn {d : ℕ} (hd : 0 < d) (i u : Site d) :
    u ∈ componentIn (Set.univ : Set (Site d)) i := by
  haveI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨w⟩ := (LatticeProb.Graph.Zd.latticeConnected d).preconnected i u
  let f : SimpleGraph.Hom (lattice d) ((lattice d).induce (Set.univ : Set (Site d))) :=
    { toFun := fun v => ⟨v, Set.mem_univ v⟩
      map_rel' := fun h => h }
  exact ⟨Set.mem_univ i, Set.mem_univ u, ⟨w.map f⟩⟩

/-- A set with `RnHoleProp` has finite complementary components at every point outside it. -/
private theorem arxiv_proximity_hole_finite {d : ℕ} {C : Set (Site d)}
    (hholes : RnHoleProp d C) (x : Site d) (hx : x ∉ C) :
    (componentIn Cᶜ x).Finite := by
  obtain ⟨n₀, hn₀⟩ := hholes
  let n : ℕ := max n₀ (mnorm x).toNat
  have hn₀n : n₀ ≤ n := Nat.le_max_left _ _
  have hxcent : x ∈ (cent d n : Set (Site d)) := by
    intro i
    have hcoord : |x i| ≤ mnorm x := by
      unfold mnorm
      exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
    have hnorm : 0 ≤ mnorm x := by
      unfold mnorm
      exact Finset.sum_nonneg fun j _ => abs_nonneg (x j)
    have hcast : ((mnorm x).toNat : ℤ) = mnorm x := Int.toNat_of_nonneg hnorm
    have hncoord : (mnorm x).toNat ≤ n := Nat.le_max_right _ _
    omega
  exact (hn₀ n hn₀n x hxcent hx).1

/-- A vertex outside a set `I` with `RnHoleProp` reaches `I` by a walk whose norm length is
at most the size of its complementary hole plus one. -/
private theorem arxiv_proximity_walk {d : ℕ} {I : Set (Site d)} {i x : Site d}
    (hd : 0 < d) (hi : i ∈ I) (hRn : RnHoleProp d I) :
    ∃ a : Site d, a ∈ I ∧
      ((mnorm (x - a) : ℤ) : ℝ) ≤ ((componentIn Iᶜ x).ncard : ℝ) + 1 := by
  have hu : x ∈ componentIn (Set.univ : Set (Site d)) i :=
    arxiv_proximity_univ_componentIn hd i x
  obtain ⟨a, ha, haComp, p, hplen⟩ :=
    arxiv_core_attachment_of_finite_holes (Set.subset_univ I)
      (fun y hy => arxiv_proximity_hole_finite hRn y hy) i hi x hu
  have hwalk : mnorm (x - a) ≤ (p.length : ℤ) :=
    rn_walk_length_ge (S := componentIn (Set.univ : Set (Site d)) i) ⟨x, hu⟩ ⟨a, haComp⟩ p
  have hlen : (p.length : ℤ) ≤ ((componentIn Iᶜ x).ncard : ℤ) + 1 := by
    exact_mod_cast hplen
  have hnorm : mnorm (x - a) ≤ ((componentIn Iᶜ x).ncard : ℤ) + 1 := hwalk.trans hlen
  refine ⟨a, ha, ?_⟩
  exact_mod_cast hnorm

/-- At high bond density, almost every configuration has an infinite actual open-bond cluster
`I` with `RnHoleProp` such that every vertex of a large centred box is within the
logarithmic-square hole bound of a vertex of `I`. -/
theorem arxiv_actual_bond_core_proximity_ae (d : ℕ) (hd : 2 ≤ d) :
    ∃ q0 B : ℝ, 0 ≤ q0 ∧ q0 < 1 ∧ 1 ≤ B ∧
      ∀ q : ℝ, q0 ≤ q → q ≤ 1 →
        ∀ᵐ ζ ∂(bondPercolation d q), ∃ i : Site d,
          let I : Set (Site d) := {y : Site d | (openBondGraph ζ).Reachable i y}
          I.Infinite ∧ RnHoleProp d I ∧
            ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, x ∈ cent d (4 * n) →
              ∃ a : Site d, a ∈ I ∧
                ((mnorm (x - a) : ℤ) : ℝ) ≤ B * (Real.log ((n : ℝ) + 2)) ^ (2 : ℕ) + 1 := by
  obtain ⟨q0, B, hq0, hq01, hB, hcut⟩ := arxiv_actual_bond_box_cutoff_ae d hd
  refine ⟨q0, B, hq0, hq01, hB, ?_⟩
  intro q hq hq1
  filter_upwards [hcut q hq hq1] with ζ hζ
  obtain ⟨i, hIinf, hRn, n0, hcutN⟩ := hζ
  have hi : i ∈ {y : Site d | (openBondGraph ζ).Reachable i y} :=
    SimpleGraph.Reachable.refl i
  refine ⟨i, hIinf, hRn, n0, ?_⟩
  intro n hn x hx
  by_cases hxI : x ∈ {y : Site d | (openBondGraph ζ).Reachable i y}
  · refine ⟨x, hxI, ?_⟩
    have h0 : mnorm (x - x) = 0 := by simp [mnorm]
    rw [h0, Int.cast_zero]
    have hL : 0 ≤ (Real.log ((n : ℝ) + 2)) ^ (2 : ℕ) := sq_nonneg _
    have hBL : 0 ≤ B * (Real.log ((n : ℝ) + 2)) ^ (2 : ℕ) := mul_nonneg (by linarith) hL
    linarith
  · obtain ⟨a, ha, hbound⟩ := arxiv_proximity_walk (by omega) hi hRn (x := x)
    refine ⟨a, ha, ?_⟩
    have hcard := (hcutN n hn x hx hxI).2
    linarith

end Exploding
