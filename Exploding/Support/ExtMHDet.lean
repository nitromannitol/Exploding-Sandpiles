/-
A finite hole of an infinite open cluster, of volume at least `xmh3_V n`, through a point of
the box `[-n, n]^d`, produces the enlarged Peierls bad event.  The inner boundary of the hole
is a `*`-connected all-closed set, it has at least `xmh4_m n` sites because the hole has at
most `|∂B|^2` sites, and it lies within sup-distance `|∂B|` of the point of the box.
-/
import Exploding.Support.ExtMHPeierls
import Exploding.Support.ExtMHGeom
import Exploding.Support.ExtMHNumeric
import Exploding.Support.ExtMHProof12

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- A finite hole of an infinite open cluster through the box, of large volume, realises the
enlarged Peierls bad event. -/
theorem xmd_bad_of_failure (hd : 2 ≤ d) {ω : Site d → Bool} {n : ℕ} {C : Set (Site d)}
    (hC : IsInfiniteOpenCluster ω C) {x : Site d} (hx : x ∈ cent d n) (hxC : x ∉ C)
    (hfin : (componentIn Cᶜ x).Finite)
    (hvol : xmh3_V n ≤ ((componentIn Cᶜ x).ncard : ℝ)) : xmp_bad d n ω := by
  set B : Set (Site d) := componentIn Cᶜ x with hBdef
  set Bf : Finset (Site d) := hfin.toFinset with hBfdef
  have hBf : (Bf : Set (Site d)) = B := hfin.coe_toFinset
  have hxC' : x ∈ Cᶜ := hxC
  have hxB : x ∈ B := ⟨hxC', hxC', SimpleGraph.Reachable.refl _⟩
  have hxBf : x ∈ Bf := hfin.mem_toFinset.mpr hxB
  obtain ⟨hconn, hclosed⟩ := xmh8_boundary_sconn_closed hC hxC
  set D : Set (Site d) := innerBoundary B with hDdef
  have hDBf : innerBoundary (Bf : Set (Site d)) = D := by rw [hBf]
  have hDfin : D.Finite := hfin.subset (fun z hz => hz.1)
  have hDne : D.Nonempty := hDBf ▸ xmg_innerBoundary_nonempty (by omega) Bf ⟨x, hxBf⟩
  have hD1 : 1 ≤ D.ncard := (Set.ncard_pos hDfin).mpr hDne
  have hcard : B.ncard ≤ D.ncard ^ 2 := by
    have h := xmg_card_le_sq hd Bf
    rw [hDBf, hBfdef, ← Set.ncard_eq_toFinset_card B hfin] at h
    exact h
  have hV : xmh3_V n ≤ (D.ncard : ℝ) ^ 2 :=
    hvol.trans (by exact_mod_cast hcard)
  have hsize : xmh4_m n ≤ D.ncard := xmn_m_le_of_sq n D.ncard hD1 hV
  obtain ⟨p, hpD, hp⟩ := xmg_exists_near hd Bf hxBf
  rw [hDBf] at hpD hp
  have hnear : ∃ p ∈ D, ∀ i, |p i| ≤ (n : ℤ) + D.ncard := by
    refine ⟨p, hpD, fun i => ?_⟩
    have hxi : |x i| ≤ (n : ℤ) := hx i
    have h1 := abs_le.mp (hp i)
    have h2 := abs_le.mp hxi
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  exact xmp_bad_of_boundary hDfin hconn hclosed hsize hnear

end Exploding
