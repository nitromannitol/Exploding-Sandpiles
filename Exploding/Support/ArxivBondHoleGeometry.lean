import Exploding.Support.ArxivBondBoundaryStar
import Exploding.Support.ArxivBondHoleBoundary
import Exploding.Support.ExtMHGeom

/-!
# Size and boundary anchors for actual bond holes

For a finite component of the complement of an actual open-bond reachability cluster,
the inner-boundary cardinality controls the hole size and supplies a boundary site close
to the specified site. The deterministic geometry needs no infinitude assumption on the
open-bond cluster.
-/

namespace Exploding

open LatticeProb

/-- Finite actual-bond holes have size at most the square of their inner-boundary size,
and their boundary contains an anchor within that size in every coordinate. -/
theorem arxiv_bond_hole_size_and_anchor {d : ℕ} (hd : 2 ≤ d)
    (ζ : RnBond d → Bool) (i z : Site d)
    (hz : z ∉ {y : Site d | (openBondGraph ζ).Reachable i y})
    (hfin : (componentIn
      ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).Finite) :
    let H : Set (Site d) :=
      componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z
    H.ncard ≤ (innerBoundary H).ncard ^ 2 ∧
      ∃ p ∈ innerBoundary H,
        ∀ k : Fin d, |p k - z k| ≤ ((innerBoundary H).ncard : ℤ) := by
  classical
  let H : Set (Site d) :=
    componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z
  change H.ncard ≤ (innerBoundary H).ncard ^ 2 ∧
    ∃ p ∈ innerBoundary H,
      ∀ k : Fin d, |p k - z k| ≤ ((innerBoundary H).ncard : ℤ)
  let B : Finset (Site d) := hfin.toFinset
  have hBH : (B : Set (Site d)) = H := hfin.coe_toFinset
  have hzH : z ∈ H := by
    dsimp [H]
    exact ⟨hz, hz, SimpleGraph.Reachable.refl _⟩
  have hzB : z ∈ B := hfin.mem_toFinset.mpr hzH
  have hcard : H.ncard = B.card := by
    rw [← Set.ncard_eq_toFinset_card H hfin]
  have hsize : H.ncard ≤ (innerBoundary H).ncard ^ 2 := by
    calc
      H.ncard = B.card := hcard
      _ ≤ (innerBoundary (B : Set (Site d))).ncard ^ 2 := xmg_card_le_sq hd B
      _ = (innerBoundary H).ncard ^ 2 := by rw [hBH]
  obtain ⟨p, hpB, hnear⟩ := xmg_exists_near hd B hzB
  refine ⟨hsize, p, ?_, ?_⟩
  · simpa only [hBH] using hpB
  · intro k
    simpa only [hBH] using hnear k

end Exploding
