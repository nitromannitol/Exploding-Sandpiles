/-
Copied from Percolation-Rigidity (https://github.com/nitromannitol/Percolation-Rigidity), commit
63c0ac991f33e61e9645694319070d9405333e5d, file `Rigidity/Percolation/TriadicWellConnectedGeometry.lean`,
licensed under the Apache License 2.0.
Changes: the module paths of the imports (`Rigidity.*` becomes `Exploding.Rigidity.*`, and the
Lattice-Probability bond model `LatticeProb.Prob.Percolation.LatticeBond*` becomes its copy
`Exploding.Support.LatticeBond.*`); the namespace `LatticeProb.Percolation` of that model becomes
`Exploding.LatticeBond`.
-/
import Exploding.Rigidity.Percolation.TriadicWellConnectedEvent
import Exploding.Rigidity.Percolation.TriadicLocalizationCentered

/-!
# Geometry of well-connectedness test cubes

Every test cube meeting a subset of a triadic cube is contained in the
concentric threefold enlargement of that triadic cube.
-/

namespace Rigidity.Percolation

open Exploding.LatticeBond

/-- A test cube meeting the ambient triadic cube is contained in its
concentric threefold enlargement. -/
theorem TriadicCube.testCube_vertices_subset_centeredTriple {d : ℕ}
    {Q : TriadicCube d} {interior : Set (Vertex d)} (hinterior : interior ⊆ Q.vertices)
    {R : IntegerCube d} (hR : R ∈ Q.testCubes interior) :
    (↑R.vertices : Set (Vertex d)) ⊆ Q.centeredTriple := by
  obtain ⟨_, hsize, x, hxR, hxI⟩ := hR
  have hxQ := hinterior hxI
  intro y hy i
  have hx := (IntegerCube.mem_vertices R x).mp hxR i
  have hy' := (IntegerCube.mem_vertices R y).mp hy i
  have hq := hxQ i
  change |2 * (y i - Q.center i)| < 3 * Q.side
  change |2 * (x i - Q.center i)| < Q.side at hq
  have hq' := abs_lt.mp hq
  apply abs_lt.mpr
  omega

end Rigidity.Percolation
