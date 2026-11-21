/-
Copied from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), commit
7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069, file `LatticeProb/Prob/Percolation/LatticeBondGraph.lean`,
licensed under the Apache License 2.0.
Changes: the namespace `LatticeProb.Percolation` is renamed `Exploding.LatticeBond`, which opens
`LatticeProb`; the import of `LatticeProb.Prob.Percolation.LatticeBondModel` is its copy
`Exploding.Support.LatticeBond.Model`; the Laplacian declarations `openLaplacian`,
`openLaplacian_eq_netLaplacian`, `open_harmonic_iff`, `componentLaplacian`,
`componentLaplacian_eq_netLaplacian` and `component_harmonic_iff`, with the sentence of the module
docstring about them, are omitted, and so is the import of `LatticeProb.Network.Basic` they use;
`allOpen_two_degree` is omitted.
-/
import Exploding.Support.LatticeBond.Model

/-!
# The open graph of a lattice bond configuration

A configuration retains precisely its open nearest-neighbor bonds. Its graph is locally finite,
with degree at most twice the dimension. Connected components are actual graph components; no
infinite component is selected and no existence or uniqueness property is assumed.
-/

namespace Exploding.LatticeBond

open LatticeProb

open scoped BigOperators

variable {d : ℕ}

/-- The graph retaining exactly the bonds assigned `true` by the configuration. -/
def openGraph (ω : Configuration d) : SimpleGraph (Vertex d) where
  Adj x y := ∃ h : (nearestNeighborGraph d).Adj x y, ω (bondOfAdjacent h) = true
  symm := ⟨fun _ _ ⟨h, ho⟩ => ⟨h.symm, by rw [bondOfAdjacent_symm]; exact ho⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h.ne rfl⟩

/-- An open edge is a nearest-neighbor edge with its genuine bond assigned `true`. -/
theorem openGraph_adj_iff (ω : Configuration d) (x y : Vertex d) :
    (openGraph ω).Adj x y ↔
      ∃ h : (nearestNeighborGraph d).Adj x y, ω (bondOfAdjacent h) = true := Iff.rfl

/-- The open graph is a subgraph of the full lattice. -/
theorem openGraph_le (ω : Configuration d) : openGraph ω ≤ nearestNeighborGraph d :=
  fun _ _ h => h.choose

/-- Every open neighbor set is a finite subset of the lattice neighbor set. -/
noncomputable instance openGraphLocallyFinite (ω : Configuration d) :
    (openGraph ω).LocallyFinite :=
  fun x => Set.Finite.fintype
    (((nbrFinset x).finite_toSet).subset (fun _ hy =>
      Graph.Zd.mem_nbrFinset.mpr (Graph.Zd.adj_iff.mp (openGraph_le ω hy))))

/-- Removing closed bonds can only decrease the lattice degree `2d`. -/
theorem openGraph_degree_le (ω : Configuration d) (x : Vertex d) :
    (openGraph ω).degree x ≤ 2 * d := by
  calc
    (openGraph ω).degree x ≤ (lattice d).degree x :=
      SimpleGraph.degree_le_of_le (openGraph_le ω)
    _ = 2 * d := Graph.Zd.degree_eq x

/-- Actual connected components of the configuration's open graph. -/
abbrev OpenComponent (ω : Configuration d) := (openGraph ω).ConnectedComponent

/-- Existence of an infinite open component, expressed without choosing one. -/
def HasInfiniteOpenComponent (ω : Configuration d) : Prop :=
  ∃ C : OpenComponent ω, C.supp.Infinite

/-- Existence and uniqueness of an infinite open component, without a chosen carrier. -/
def HasUniqueInfiniteOpenComponent (ω : Configuration d) : Prop :=
  ∃! C : OpenComponent ω, C.supp.Infinite

/-- The graph on the actual vertices of an open connected component. -/
abbrev componentGraph {ω : Configuration d} (C : OpenComponent ω) := C.toSimpleGraph

/-- Inclusion of component neighbors into the open graph's neighbors is injective. -/
private def componentNeighborEmbedding {ω : Configuration d} (C : OpenComponent ω) (x : C) :
    (componentGraph C).neighborSet x ↪ (openGraph ω).neighborSet x.val where
  toFun y := ⟨y.val.val, y.property⟩
  inj' := by
    intro y z h
    have hv : y.val.val = z.val.val :=
      congrArg (fun t : (openGraph ω).neighborSet x.val => t.val) h
    exact Subtype.ext (Subtype.ext hv)

/-- Component graphs inherit local finiteness through inclusion of their neighbors. -/
noncomputable instance componentGraphLocallyFinite {ω : Configuration d} (C : OpenComponent ω) :
    (componentGraph C).LocallyFinite := fun x =>
  Fintype.ofInjective (componentNeighborEmbedding C x) (componentNeighborEmbedding C x).injective

/-- Each component also has degree at most twice the ambient dimension. -/
theorem componentGraph_degree_le {ω : Configuration d} (C : OpenComponent ω) (x : C) :
    (componentGraph C).degree x ≤ 2 * d := by
  calc
    (componentGraph C).degree x ≤ (openGraph ω).degree x.val := by
      rw [← SimpleGraph.card_neighborSet_eq_degree,
        ← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_le_of_injective _ (componentNeighborEmbedding C x).injective
    _ ≤ 2 * d := openGraph_degree_le ω x.val

/-- The configuration in which every genuine lattice bond is open. -/
def allOpen (d : ℕ) : Configuration d := fun _ => true

/-- The configuration in which every genuine lattice bond is closed. -/
def allClosed (d : ℕ) : Configuration d := fun _ => false

/-- Opening every bond recovers the full nearest-neighbor graph. -/
theorem openGraph_allOpen (d : ℕ) : openGraph (allOpen d) = nearestNeighborGraph d := by
  ext x y
  exact ⟨fun h => h.choose, fun h => ⟨h, rfl⟩⟩

/-- Closing every bond gives the graph with no edges. -/
theorem openGraph_allClosed (d : ℕ) : openGraph (allClosed d) = ⊥ := by
  ext x y
  simp only [openGraph_adj_iff, allClosed, Bool.false_eq_true, exists_false,
    SimpleGraph.bot_adj]

/-- In dimension two a genuine nearest-neighbor bond is present when all bonds are open. -/
theorem allOpen_two_unit_adj :
    (openGraph (allOpen 2)).Adj 0 (unit (0 : Fin 2)) := by
  rw [openGraph_allOpen]
  exact ⟨0, Or.inl (zero_add _).symm⟩

/-- In dimension two the same nearest-neighbor bond is absent when all bonds are closed. -/
theorem allClosed_two_not_unit_adj :
    ¬ (openGraph (allClosed 2)).Adj 0 (unit (0 : Fin 2)) := by
  rw [openGraph_allClosed]
  exact fun h => h

end Exploding.LatticeBond
