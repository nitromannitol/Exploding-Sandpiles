import Exploding.Support.Percolation
import LatticeProb.Graph.Zd

/-!
# The actual bond law at parameter one

At parameter `1` every bond of `ℤ^d` is open almost surely: the Bernoulli bond
product law is the Dirac mass at the all-open configuration.  Every nearest-neighbour
bond is then an edge of the actual open-bond graph, so the lattice connects every
pair of sites, and the actual open cluster of each site is all of `ℤ^d` almost surely.
-/

namespace Exploding

open LatticeProb MeasureTheory

/-- At parameter one a Bernoulli bit is `true` with probability one. -/
theorem bitLaw_one_eq_dirac_true : bitLaw (1 : ℝ) = Measure.dirac true := by
  unfold bitLaw
  simp

/-- The actual bond law at parameter one is concentrated on the all-open configuration. -/
theorem arxiv_actual_bond_law_one (d : ℕ) :
    bondPercolation d (1 : ℝ) = Measure.dirac (fun _ : Site d × Fin d => true) := by
  unfold bondPercolation
  simp only [bitLaw_one_eq_dirac_true]
  exact Measure.infinitePi_dirac (fun _ : Site d × Fin d => true)

/-- Every nearest-neighbour bond of `ℤ^d` is an edge of the open-bond graph of the
all-open configuration. -/
theorem lattice_le_openBondGraph_all_open (d : ℕ) :
    lattice d ≤ openBondGraph (fun _ : Site d × Fin d => true) := by
  rintro x y h
  have hne : x ≠ y := h.ne
  obtain ⟨i, hi | hi⟩ := h
  · exact (SimpleGraph.fromRel_adj _ x y).mpr ⟨hne, Or.inl ⟨i, hi, rfl⟩⟩
  · exact (SimpleGraph.fromRel_adj _ x y).mpr ⟨hne, Or.inr ⟨i, hi, rfl⟩⟩

/-- In the all-open configuration every site reaches every site. -/
theorem openBondGraph_all_open_reachable (d : ℕ) [NeZero d] (x y : Site d) :
    (openBondGraph (fun _ : Site d × Fin d => true)).Reachable x y :=
  SimpleGraph.Reachable.mono (lattice_le_openBondGraph_all_open d)
    ((LatticeProb.Graph.Zd.latticeConnected d).preconnected x y)

/-- At parameter one, almost surely every site reaches every site in the actual
open-bond graph, so each actual open cluster is the whole of `ℤ^d`. -/
theorem arxiv_actual_bond_reachable_univ_one_ae (d : ℕ) (hd : 2 ≤ d) :
    ∀ᵐ ζ ∂(bondPercolation d (1 : ℝ)), ∀ i : Site d,
      {y : Site d | (openBondGraph ζ).Reachable i y} = Set.univ := by
  haveI : NeZero d := ⟨by omega⟩
  rw [arxiv_actual_bond_law_one, ae_dirac_eq, Filter.eventually_pure]
  intro i
  exact Set.eq_univ_of_forall fun y => openBondGraph_all_open_reachable d i y

/-- At parameter one, almost surely the complement of each actual open-bond cluster has
empty component at every site: there are no holes. -/
theorem arxiv_actual_bond_complement_componentIn_one_ae (d : ℕ) (hd : 2 ≤ d) :
    ∀ᵐ ζ ∂(bondPercolation d (1 : ℝ)), ∀ i z : Site d,
      componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z = ∅ := by
  filter_upwards [arxiv_actual_bond_reachable_univ_one_ae d hd] with ζ hζ i z
  have hc : ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) = ∅ := by
    rw [hζ i, Set.compl_univ]
  rw [hc]
  ext y
  simp [componentIn]

end Exploding
