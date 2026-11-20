/-
Copied from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), commit
7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069, file `LatticeProb/Prob/Percolation/LatticeBondGraph.lean`,
licensed under the Apache License 2.0.
Changes: the namespace `LatticeProb.Percolation` is renamed `Exploding.LatticeBond`, which opens `LatticeProb`; only `openGraph`, `openGraph_adj_iff`, `openGraph_le`, `allOpen`, `allClosed`, `openGraph_allOpen` and `openGraph_allClosed` are kept, so the import of `LatticeProb.Network.Basic` is dropped.
-/
import Exploding.Support.LatticeBond.Model

/-!
# The open graph of a lattice bond configuration

A configuration retains precisely its open nearest-neighbor bonds.
-/

namespace Exploding.LatticeBond

open LatticeProb

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

end Exploding.LatticeBond
