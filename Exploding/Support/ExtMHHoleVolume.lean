/-
Lemma 5.2 of Mathieu, the volume of the holes of the infinite cluster of highly supercritical
site percolation, with no remaining hypothesis.  The deterministic production of the enlarged
Peierls bad event from a finite hole of large volume through the box supplies the one
hypothesis of the reduction `xmf_of_det`.
-/
import Exploding.Support.ExtMHDet
import Exploding.Support.ExtMHFinal

namespace Exploding

/-- **Lemma 5.2 of Mathieu**, the hole-volume bound for the infinite cluster of site
percolation of density close to one, proved from the Peierls estimate on closed star-connected
sets, the uniqueness of the infinite cluster, and the bound of a finite set by the square of
its inner boundary. -/
theorem xmf_proved : Exploding.External.MathieuHoleVolume :=
  xmf_of_det fun _ hd _ _ _ hC _ hx hxC hfin hvol =>
    xmd_bad_of_failure hd hC hx hxC hfin hvol

end Exploding
