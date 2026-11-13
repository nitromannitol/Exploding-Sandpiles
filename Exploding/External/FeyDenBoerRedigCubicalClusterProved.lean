import Exploding.External.FeyDenBoerRedigCubicalCluster
import LatticeProb.External.FeyDenBoerRedigCubicalClusterProved

/-!
# The result of Fey, den Boer and Redig, proved

`Exploding.External.FeyDenBoerRedigCubicalCluster` is the proposition
`LatticeProb.External.FeyDenBoerRedigCubicalCluster` under the name used here.  Lattice-Probability
proves it, `LatticeProb.External.feyDenBoerRedigCubicalCluster_holds`, so the hypothesis can be
discharged instead of assumed.
-/

/-- Theorem 4.1 of Fey, den Boer and Redig, proved in Lattice-Probability. -/
theorem Exploding.External.feyDenBoerRedigCubicalCluster_holds :
    Exploding.External.FeyDenBoerRedigCubicalCluster :=
  Exploding.External.FeyDenBoerRedigCubicalCluster_iff.mpr
    LatticeProb.External.feyDenBoerRedigCubicalCluster_holds
