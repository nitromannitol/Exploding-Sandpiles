/-
The explosion theorem of Fey, Levine and Peres, unconditionally: it follows from Schonmann's
bootstrap bound, which is proved in `Exploding/Support/ExtSchFinal.lean`.
-/
import Exploding.Support.ExtSchFinal
import Exploding.Support.LSProofAux

namespace Exploding

/-- **The explosion theorem of Fey, Levine and Peres (Theorem 1.1).** -/
theorem xsr_flp : Exploding.External.FeyLevinePeresExplosive :=
  LSProof.ls_flp_from_explosive xsr_schonmann

end Exploding
