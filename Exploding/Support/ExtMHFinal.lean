/-
Mathieu's hole-volume bound from the deterministic step.  Above the density threshold the
infinite cluster is almost surely unique, so every hole is finite, and almost surely the
enlarged Peierls bad event fails for all large scales; a hole of volume at least `(log n)^{5/2}`
through the box would realise that event, so for large `n` every hole through the box is
smaller.  The deterministic step is the hypothesis of the reduction.
-/
import Exploding.External.MathieuHoles
import Exploding.Support.ExtMHPeierls
import Exploding.Support.ExtMHThreshold
import Exploding.Support.ExtMHProof13

namespace Exploding

open LatticeProb MeasureTheory Filter

/-- **Mathieu's hole-volume bound**, reduced to the deterministic production of the enlarged
bad event from a finite hole of large volume through the box. -/
theorem xmf_of_det
    (hdet : ∀ (d : ℕ), 2 ≤ d → ∀ (ω : Site d → Bool) (n : ℕ) (C : Set (Site d)),
      IsInfiniteOpenCluster ω C → ∀ x ∈ (cent d n : Set (Site d)), x ∉ C →
        (componentIn Cᶜ x).Finite → xmh3_V n ≤ ((componentIn Cᶜ x).ncard : ℝ) →
          xmp_bad d n ω) :
    Exploding.External.MathieuHoleVolume := by
  intro d hd
  refine ⟨xmt_q₀ d, xmt_q₀_lt_one d, fun q hq hq1 => ?_⟩
  have hS := xmt_summability hq hq1
  have huniq : ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
      ∀ x, x ∉ C → (componentIn Cᶜ x).Finite := xmh9_UniqueOpen hd (xmt_xmh6_of hS)
  have hno := xmp_ae_no_bad hS.1 hS.2.1 hS.2.2
  filter_upwards [huniq, hno] with ω hu hn C hC
  rw [Filter.eventually_atTop] at hn
  obtain ⟨n0, hn0⟩ := hn
  refine ⟨n0, fun n hle x hx hxC => ?_⟩
  have hfin := hu C hC x hxC
  refine ⟨hfin, ?_⟩
  by_contra hcon
  exact hn0 n hle (hdet d hd ω n C hC x hx hxC hfin (not_lt.mp hcon))

end Exploding
