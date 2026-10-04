/-
The hole-volume bound of Mathieu for the infinite cluster of site percolation.
-/
import Exploding.Support.ExtMHDet
import Exploding.Support.ExtMHFinal

open Exploding

/-- **Lemma 5.2 of Mathieu**, the hole-volume bound for the infinite cluster of site
percolation of density close to one, proved from the Peierls estimate on closed star-connected
sets, the uniqueness of the infinite cluster, and the bound of a finite set by the square of
its inner boundary. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.xmf_proved : Exploding.External.MathieuHoleVolume
-- FROZEN-STATEMENT-END
  := xmf_of_det fun _ hd _ _ _ hC _ hx hxC hfin hvol =>
    xmd_bad_of_failure hd hC hx hxC hfin hvol
