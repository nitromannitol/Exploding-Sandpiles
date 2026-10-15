import Exploding.Support.ArxivBondDefectiveFiniteness
import Exploding.Support.ArxivBondBoundaryStar
import Exploding.Support.ArxivBondHoleBoundary
import Exploding.Support.ArxivBoundaryInfiniteGeometry

/-!
# Finiteness of holes in an actual bond cluster

At sufficiently high bond density, every lattice component of the complement of an infinite
open-bond reachability component is finite almost surely. The argument uses the actual bond law,
the actual open-bond graph, and the no-infinite-defective-star event.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- Under the actual bond law, every complement component outside any infinite open-bond
reachability component is finite almost surely at sufficiently high density. -/
theorem arxiv_ae_actual_bond_holes_finite (d : ℕ) (hd : 2 ≤ d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ {q : ℝ}, 0 ≤ q → q ≤ 1 →
      (K : ENNReal) ^ (3 ^ d) *
        ENNReal.ofReal (2 * (d : ℝ) * (1 - q)) < 1 →
      ∀ᵐ ζ ∂(bondPercolation d q),
        ∀ i : Site d,
          ({y : Site d | (openBondGraph ζ).Reachable i y}).Infinite →
          ∀ x : Site d,
            x ∉ {y : Site d | (openBondGraph ζ).Reachable i y} →
            (componentIn
              ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) x).Finite := by
  classical
  obtain ⟨K, hK, hno⟩ := arxiv_ae_no_infinite_bond_defective_star_set d
  refine ⟨K, hK, ?_⟩
  intro q hq0 hq1 hnumeric
  filter_upwards [hno (q := q) hq0 hq1 hnumeric] with ζ hζ
  intro i hIinf x hx
  let I : Set (Site d) := {y : Site d | (openBondGraph ζ).Reachable i y}
  let H : Set (Site d) := componentIn Iᶜ x
  by_contra hHfin
  have hHinf : H.Infinite := Set.not_finite.mp hHfin
  have hIinf' : I.Infinite := by
    simpa only [I] using hIinf
  have hIcompl : I ⊆ Hᶜ := by
    intro y hyI hyH
    exact hyH.2.1 hyI
  have hHcInf : Hᶜ.Infinite := hIinf'.mono hIcompl
  have hboundaryInf : (innerBoundary H).Infinite :=
    arxiv_innerBoundary_infinite_of_infinite_compl hd hHinf hHcInf
  have hboundaryConn : xmh_SConn (innerBoundary H) := by
    simpa only [I, H] using arxiv_innerBoundary_bond_star_connected ζ i x
  have hboundaryDefective :
      ∀ b ∈ innerBoundary H, rn_siteField ζ b = false := by
    intro b hb
    have hb' : b ∈ innerBoundary
        (componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) x) := by
      simpa only [I, H] using hb
    exact arxiv_innerBoundary_bond_defective ζ i x b hb'
  exact hζ ⟨innerBoundary H, hboundaryInf, hboundaryConn, hboundaryDefective⟩

end Exploding
