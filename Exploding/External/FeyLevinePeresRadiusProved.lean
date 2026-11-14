import Exploding.External.FeyLevinePeresRadius
import LatticeProb.External.FeyLevinePeresRadiusProved

/-!
# The radius bound of Fey, Levine and Peres, proved

`Exploding.External.FeyLevinePeresRadius` is the proposition
`LatticeProb.External.FeyLevinePeresRadius` under the name used here.  Lattice-Probability proves
it, `LatticeProb.External.feyLevinePeresRadius_holds`, so the hypothesis can be discharged instead
of assumed.
-/

/-- Theorem 1.1 of Fey, Levine and Peres, proved in Lattice-Probability. -/
theorem Exploding.External.feyLevinePeresRadius_holds :
    Exploding.External.FeyLevinePeresRadius :=
  Exploding.External.FeyLevinePeresRadius_iff.mpr
    LatticeProb.External.feyLevinePeresRadius_holds
