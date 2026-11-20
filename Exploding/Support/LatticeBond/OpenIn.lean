/-
Copied from Percolation-Rigidity (https://github.com/nitromannitol/Percolation-Rigidity), commit
9ac9c6c6b7c5e0c9eec4a65770deaa7b52b6b1e4, file `Rigidity/External/WellConnected.lean`.
Changes: only the definition `openIn` is kept, in the namespace `Exploding.LatticeBond` instead of
`Rigidity.External`, over the bond model of `Exploding.Support.LatticeBond.Graph`.
-/
import Exploding.Support.LatticeBond.Graph

/-!
# Open bonds inside a set

The graph of the open bonds of a configuration with both endpoints in a given set of vertices,
in which Percolation-Rigidity states its connection events.
-/

namespace Exploding.LatticeBond

variable {d : ℕ}

/-- The open edges with both endpoints in `B`. -/
def openIn (ω : Configuration d) (B : Set (Vertex d)) : SimpleGraph (Vertex d) where
  Adj y z := (openGraph ω).Adj y z ∧ y ∈ B ∧ z ∈ B
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => (openGraph ω).loopless.irrefl _ h.1⟩

end Exploding.LatticeBond
