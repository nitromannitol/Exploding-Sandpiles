import Exploding.Support.ExtLSSCountable

open Exploding

-- FROZEN-STATEMENT-BEGIN
/-- In-repo discharge of `ext-lss-bounded-degree`; the proof is `Exploding.xlse_lss_bounded_degree`
in `Exploding/Support/ExtLSSCountable.lean`. -/
theorem Exploding.lssBoundedDegree : Exploding.External.LiggettSchonmannStaceyBoundedDegree
-- FROZEN-STATEMENT-END
  := Exploding.xlse_lss_bounded_degree
