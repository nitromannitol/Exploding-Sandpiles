module

public import Exploding.Support.ExtSchFinal
public import Exploding.Support.LSProofAux

@[expose] public section

open Exploding

/-- **The explosion theorem of Fey, Levine and Peres (Theorem 1.1).** -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.xsr_flp : Exploding.External.FeyLevinePeresExplosive
-- FROZEN-STATEMENT-END
  := LSProof.ls_flp_from_explosive Exploding.xsr_schonmann
