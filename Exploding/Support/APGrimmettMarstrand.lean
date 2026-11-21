/-
Uniform slab connectivity above the critical probability in dimensions `d ≥ 3`.

Percolation-Rigidity proves, in the bond model of Lattice-Probability, that above the critical
probability one slab width gives a uniform positive lower bound for two-point connections inside
every slab of every integer cube
(`Rigidity.Percolation.uniformCubeSlabConnectivity_of_criticalProbability_lt`, copied in
`Exploding/Rigidity/`); this is the slab form of the theorem of Grimmett and Marstrand (*The
supercritical phase of percolation is well behaved*, Proc. R. Soc. Lond. A 430 (1990)).  Its
statement is `LatticeBond.UniformCubeSlabConnectivity d p` with the integer cube written through
its corner and size (`latticeBond_uniformCubeSlabConnectivity`), which is the hypothesis of
`antalPisztoraChemicalDistance_of_slabConnectivity`.
-/
import Exploding.Rigidity.Percolation.Blocks.SlabConnectivity
import Exploding.Support.APPisztoraFromSlab

namespace Exploding

variable {d : ℕ}

/-- Uniform slab connectivity of Percolation-Rigidity, stated over integer cubes, is
`LatticeBond.UniformCubeSlabConnectivity`, stated over corners and sizes. -/
theorem latticeBond_uniformCubeSlabConnectivity {p : unitInterval}
    (h : Rigidity.Percolation.UniformCubeSlabConnectivity d p) :
    LatticeBond.UniformCubeSlabConnectivity d p := by
  obtain ⟨width, hwidth, ρ, hρ, hslab⟩ := h
  refine ⟨width, hwidth, ρ, hρ, fun c n a k hk x hx y hy => ?_⟩
  have e : cubeSlab c n a width k =
      (⟨c, n⟩ : Rigidity.Percolation.IntegerCube d).slab a width k :=
    (integerCube_slab_eq_cubeSlab ⟨c, n⟩ a width k).symm
  rw [e] at hx hy ⊢
  exact hslab ⟨c, n⟩ a k hk x hx y hy

/-- **Uniform slab connectivity above the critical probability** (the slab form of the theorem
of Grimmett and Marstrand), for `d ≥ 3`, in the form used by
`antalPisztoraChemicalDistance_of_slabConnectivity`. -/
theorem latticeBond_uniformCubeSlabConnectivity_of_criticalProbability_lt [NeZero d]
    (hd : 3 ≤ d) (p : unitInterval) (hp : LatticeBond.criticalProbability d < (p : ℝ)) :
    LatticeBond.UniformCubeSlabConnectivity d p :=
  latticeBond_uniformCubeSlabConnectivity
    (Rigidity.Percolation.uniformCubeSlabConnectivity_of_criticalProbability_lt hd p hp)

end Exploding
