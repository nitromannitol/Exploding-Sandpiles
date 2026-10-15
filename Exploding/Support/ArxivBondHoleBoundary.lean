import Exploding.Support.RNProofPercolation

/-!
# Defectiveness of bond-hole boundaries

Every vertex on the inner boundary of a component complementary to a selected open-bond cluster
has a closed incident bond. The argument uses only lattice adjacency and applies in every
dimension.
-/

namespace Exploding

open LatticeProb

/-- A boundary vertex of a complementary open-bond component has a closed incident bond: if all
its incident bonds were open, its edge to the selected cluster would put it in that cluster. -/
theorem arxiv_innerBoundary_bond_defective {d : ℕ}
    (ζ : RnBond d → Bool) (i x b : Site d)
    (hb : b ∈ innerBoundary
      (componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) x)) :
    rn_siteField ζ b = false := by
  let I : Set (Site d) := {y | (openBondGraph ζ).Reachable i y}
  have hb' : b ∈ innerBoundary (componentIn Iᶜ x) := by
    simpa only [I] using hb
  simp only [innerBoundary, Set.mem_setOf_eq] at hb'
  obtain ⟨hbHole, c, hcHole, hbc⟩ := hb'
  obtain ⟨hxHole, hbInHole, hreach⟩ := hbHole
  have hcInI : c ∈ I := by
    by_contra hcNotI
    have hcInHoleSet : c ∈ Iᶜ := by
      simpa only [Set.mem_compl_iff] using hcNotI
    have hstep : ((lattice d).induce Iᶜ).Adj ⟨b, hbInHole⟩ ⟨c, hcInHoleSet⟩ := by
      simpa [SimpleGraph.induce_adj] using hbc
    have hcInHole : c ∈ componentIn Iᶜ x :=
      ⟨hxHole, hcInHoleSet, hreach.trans (SimpleGraph.Adj.reachable hstep)⟩
    exact hcHole hcInHole
  cases hfield : rn_siteField ζ b with
  | false => rfl
  | true =>
    have hall : ∀ e ∈ rn_incident d b, ζ e = true := by
      simpa only [rn_siteField, decide_eq_true_eq] using hfield
    have hbcOpen : (openBondGraph ζ).Adj b c := by
      rw [openBondGraph, SimpleGraph.fromRel_adj]
      refine ⟨(lattice d).ne_of_adj hbc, ?_⟩
      obtain ⟨j, hj | hj⟩ := hbc
      · exact Or.inl ⟨j, hj, hall (b, j) (by simp [rn_incident])⟩
      · refine Or.inr ⟨j, hj, hall (c, j) ?_⟩
        have hbc' : b - unit j = c := by rw [hj]; abel
        simp only [rn_incident, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
          true_and]
        exact Or.inr ⟨j, congrArg (fun z => (z, j)) hbc'⟩
    have hib : (openBondGraph ζ).Reachable i b :=
      hcInI.trans (SimpleGraph.Adj.reachable hbcOpen.symm)
    have hbNotI : b ∉ I := by
      simpa only [Set.mem_compl_iff] using hbInHole
    exact False.elim (hbNotI hib)

end Exploding
