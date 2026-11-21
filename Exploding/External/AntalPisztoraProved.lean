import Exploding.External.AntalPisztora
import Exploding.Support.APGrimmettMarstrand

/-!
# The theorem of Antal and Pisztora, proved

`Exploding.External.AntalPisztoraChemicalDistance` is proved here in every dimension `d ≥ 2` and at
every density above `bondCritical d`.  In dimension two it is `Exploding.antalPisztora_dim_two`.
In dimensions `d ≥ 3`, `Exploding.antalPisztoraChemicalDistance_of_slabConnectivity` derives it
from uniform two-point connectivity in the slabs of cubes above the critical probability, which
is `Exploding.latticeBond_uniformCubeSlabConnectivity_of_criticalProbability_lt`, the slab form of
the theorem of Grimmett and Marstrand proved in Percolation-Rigidity.  So the hypothesis can be
discharged instead of assumed.
-/

/-- Theorem 1.1 of Antal and Pisztora, proved for every `d ≥ 2` and every density above the
critical one. -/
theorem Exploding.External.antalPisztoraChemicalDistance_holds :
    Exploding.External.AntalPisztoraChemicalDistance :=
  Exploding.antalPisztoraChemicalDistance_of_slabConnectivity fun _ _ hd p hp =>
    Exploding.latticeBond_uniformCubeSlabConnectivity_of_criticalProbability_lt hd p hp
