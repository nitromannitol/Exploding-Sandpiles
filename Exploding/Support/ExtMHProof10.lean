/-
Reduction of Mathieu's hole-volume bound to a single percolation input `hDet`, using the
summability `xmh5_ae_no_bad`, and the attack on `hDet` by the uniqueness of the infinite
cluster and the boundary witness.
-/
import Exploding.Support.ExtMHProof9

namespace Exploding

open LatticeProb MeasureTheory Filter Relation
open scoped BigOperators

variable {d : ℕ}
variable {q : ℝ}

/-- The constant of `xmh_starCount`, used in the summability threshold. -/
noncomputable def xmh6_K (d : ℕ) : ℕ := Classical.choose (xmh_starCount d)

theorem xmh6_K_spec (d : ℕ) :
    ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ xmh6_K d ^ m ∧
      ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T :=
  Classical.choose_spec (xmh_starCount d)

/-- The summability condition for the bad event at density `q`. -/
def xmh6_Summability (d : ℕ) (q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧
    ((2 : ENNReal) ^ d * ((xmh6_K d : ENNReal) * ENNReal.ofReal (1 - q))) * 2 < 1

/-- **Mathieu's hole-volume bound**, reduced to the single percolation input `hDet`.  The
summability is discharged by `xmh5_ae_no_bad`, and only the large-component equivalence
`hDet` remains. -/
theorem xmh6_proved (q₀ : ∀ d : ℕ, 2 ≤ d → ℝ) (hq₀ : ∀ d hd, q₀ d hd < 1)
    (hgood : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 → xmh6_Summability d q)
    (hDet : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 →
      ∀ᵐ ω ∂(sitePercolation d q), ∀ n : ℕ, ∀ C : Set (Site d),
        IsInfiniteOpenCluster ω C → xmh4_failure d n C → xmh4_bad d n ω) :
    External.MathieuHoleVolume := by
  intro d hd
  refine ⟨q₀ d hd, hq₀ d hd, fun q h1 h2 => ?_⟩
  obtain ⟨h0, h1', hr⟩ := hgood d hd q h1 h2
  exact xmh4_hole_small (hDet d hd q h1 h2)
    (xmh5_ae_no_bad (xmh6_K d) (xmh6_K_spec d) h0 h1' hr)

/-- **The percolation input for `hDet`.**  Almost surely, for every infinite open cluster
`C`: `C` is connected; for every hole `B = componentIn Cᶜ x` with `x` in the box, `B` is
finite (uniqueness of the infinite cluster), connected, closed under adjacency outside `C`;
and if the volume of `B` exceeds the threshold then its inner boundary has at least
`xmh4_m n` sites and meets the box (the isoperimetric bound plus the localisation of the
hole boundary). -/
def xmh6_HoleInput (d : ℕ) (q : ℝ) : Prop :=
  ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
    (∀ u ∈ C, ∀ v ∈ C,
      ReflTransGen (fun a b => a ∈ C ∧ b ∈ C ∧ (lattice d).Adj a b) u v)
    ∧ (∀ n : ℕ, ∀ x ∈ cent d n, x ∉ C →
        (componentIn Cᶜ x).Finite
        ∧ (∀ u ∈ componentIn Cᶜ x, ∀ v ∈ componentIn Cᶜ x,
            ReflTransGen (fun a b => a ∈ componentIn Cᶜ x ∧ b ∈ componentIn Cᶜ x ∧
              (lattice d).Adj a b) u v)
        ∧ (∀ b ∈ componentIn Cᶜ x, ∀ z, (lattice d).Adj b z → z ∉ C →
            z ∈ componentIn Cᶜ x)
        ∧ (xmh3_V n ≤ ((componentIn Cᶜ x).ncard : ℝ) →
            xmh4_m n ≤ (innerBoundary (componentIn Cᶜ x)).ncard
            ∧ ∃ p ∈ innerBoundary (componentIn Cᶜ x), p ∈ cent d n))

/-- **`hDet` from the percolation input**, using the boundary witness, the all-closed
boundary and the bad-event extraction. -/
theorem xmh6_hDet_of_input (h : xmh6_HoleInput d q) :
    ∀ᵐ ω ∂(sitePercolation d q), ∀ n : ℕ, ∀ C : Set (Site d),
      IsInfiniteOpenCluster ω C → xmh4_failure d n C → xmh4_bad d n ω := by
  filter_upwards [h] with ω hω n C hC hfail
  obtain ⟨x, hx, hxC, hfail'⟩ := hfail
  obtain ⟨hCconn, hrest⟩ := hω C hC
  obtain ⟨i, hiC, hCeq⟩ := hC.2
  obtain ⟨hBfin, hBconn, hclose, hsize_meet⟩ := hrest n x hx hxC
  set B := componentIn Cᶜ x with hBdef
  have hdisj : ∀ z, z ∈ C → z ∈ B → False := fun z hzC hzB => hzB.2.1 hzC
  have hvol : xmh3_V n ≤ (B.ncard : ℝ) := not_lt.mp fun hlt => hfail' ⟨hBfin, hlt⟩
  obtain ⟨hsz, hmeet⟩ := hsize_meet hvol
  have hconnD : xmh_SConn {z | z ∈ B ∧ ∃ c ∈ C, (lattice d).Adj c z} := by
    intro u hu v hv
    exact xmh3_boundaryStar d C B hCconn hBconn hdisj hclose u v hu hv
  have hDeq : {z | z ∈ B ∧ ∃ c ∈ C, (lattice d).Adj c z} = innerBoundary B := by
    ext z
    constructor
    · rintro ⟨hzB, c, hcC, hcz⟩
      exact ⟨hzB, c, fun hcB => hdisj c hcC hcB, hcz.symm⟩
    · rintro ⟨hzB, y, hyB, hzy⟩
      refine ⟨hzB, y, ?_, hzy.symm⟩
      by_contra hyC
      exact hyB (hclose z hzB y hzy hyC)
  have hconn : xmh_SConn (innerBoundary B) := hDeq ▸ hconnD
  have hclosed : ∀ z ∈ innerBoundary B, ω z = false := by
    intro z hz
    obtain ⟨hzB, y, hyB, hzy⟩ := hz
    have hyC : y ∈ C := by
      by_contra hyC
      exact hyB (hclose z hzB y hzy hyC)
    exact xmh5_boundary_closed (i := i) (B := B)
      (fun z hzB hzC => hzB.2.1 (hCeq.symm ▸ hzC)) hzB ⟨y, hCeq ▸ hyC, hzy.symm⟩
  have hBfin' : (innerBoundary B).Finite := hBfin.subset fun z hz => hz.1
  have hmeet' : ∃ p ∈ innerBoundary B, p ∈ xmh4_centFinset d n :=
    let ⟨p, hp, hpx⟩ := hmeet
    ⟨p, hp, xmh4_mem_centFinset.mpr hpx⟩
  exact xmh5_bad_of_boundary hBfin' hconn hclosed hsz hmeet'

end Exploding
