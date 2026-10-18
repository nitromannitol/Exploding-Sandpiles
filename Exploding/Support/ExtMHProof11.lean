/-
Isolation of the uniqueness input of Mathieu's hole-volume bound.  The connectedness and
closedness of the clusters and holes are proved from generic induced-graph facts about `componentIn`;
the only remaining percolation inputs are named explicitly: uniqueness of the infinite
cluster, localisation of the hole boundary, and the isoperimetric size of that boundary.
-/
import Exploding.Support.ExtMHProof10
import Exploding.Support.ExtMHBase

namespace Exploding

open LatticeProb MeasureTheory Filter Relation
open scoped BigOperators

variable {d : ℕ}
variable {q : ℝ}

/-- The component of `x` in `S` is connected by nearest-neighbour steps inside itself. -/
theorem xmh7_componentIn_conn {S : Set (Site d)} {x u v : Site d}
    (hu : u ∈ componentIn S x) (hv : v ∈ componentIn S x) :
    ReflTransGen (fun a b => a ∈ componentIn S x ∧ b ∈ componentIn S x ∧
      (lattice d).Adj a b) u v := by
  have key : ∀ (m : ℕ) (c : ℕ → Site d), c 0 = x →
      (∀ s ≤ m, c s ∈ S) → (∀ s < m, (lattice d).Adj (c s) (c (s + 1))) →
      (∀ s ≤ m, c s ∈ componentIn S x) ∧
        ReflTransGen (fun a b => a ∈ componentIn S x ∧ b ∈ componentIn S x ∧
          (lattice d).Adj a b) x (c m) := by
    intro m
    induction m with
    | zero =>
        intro c hc0 hS _
        refine ⟨?_, ?_⟩
        · intro s hs
          have hs0 : s = 0 := Nat.le_zero.mp hs
          subst hs0
          rw [hc0]
          exact ⟨hu.1, hu.1, SimpleGraph.Reachable.refl _⟩
        · rw [hc0]
    | succ m ih =>
        intro c hc0 hS hadj
        obtain ⟨ihmem, ihtg⟩ := ih c hc0
          (fun s hs => hS s (le_trans hs (Nat.le_succ m)))
          (fun s hs => hadj s (lt_of_lt_of_le hs (Nat.le_succ m)))
        have hcmem : c (m + 1) ∈ componentIn S x :=
          xmh_componentIn_step (ihmem m le_rfl) (hS (m + 1) le_rfl)
            (hadj m (Nat.lt_succ_self m))
        refine ⟨?_, ihtg.tail ⟨ihmem m le_rfl, hcmem, hadj m (Nat.lt_succ_self m)⟩⟩
        intro s hs
        rcases Nat.lt_or_eq_of_le hs with h | h
        · exact ihmem s (Nat.lt_succ_iff.mp h)
        · rw [h]; exact hcmem
  obtain ⟨mu, cu, hcu0, hcum, hcuS, hcuadj⟩ := xmh_walk_of_component hu
  obtain ⟨mv, cv, hcv0, hcvm, hcvS, hcvadj⟩ := xmh_walk_of_component hv
  have h1 := (key mu cu hcu0 hcuS hcuadj).2
  rw [hcum] at h1
  have h2 := (key mv cv hcv0 hcvS hcvadj).2
  rw [hcvm] at h2
  exact (xmh_rtg_symm (fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩) h1).trans h2

/-- The component of `x` in `S` is closed under adjacency inside `S`. -/
theorem xmh7_componentIn_close {S : Set (Site d)} {x b z : Site d}
    (hb : b ∈ componentIn S x) (hz : z ∈ S) (hbz : (lattice d).Adj b z) :
    z ∈ componentIn S x :=
  xmh_componentIn_step hb hz hbz

/-- **Uniqueness of the infinite cluster**: almost surely, every component of the complement
of an infinite open cluster is finite. -/
def xmh7_Unique (d : ℕ) (q : ℝ) : Prop :=
  ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
    ∀ x, x ∉ C → (componentIn Cᶜ x).Finite

/-- **Localisation of the hole boundary**: almost surely, a hole of volume above the threshold
has its inner boundary meeting the box. -/
def xmh7_Localized (d : ℕ) (q : ℝ) : Prop :=
  ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
    ∀ n : ℕ, ∀ x ∈ cent d n, x ∉ C →
      xmh3_V n ≤ ((componentIn Cᶜ x).ncard : ℝ) →
      ∃ p ∈ innerBoundary (componentIn Cᶜ x), p ∈ cent d n

/-- **Isoperimetric size of the hole boundary**: almost surely, a hole of volume above the
threshold has inner boundary of at least `xmh4_m n` sites. -/
def xmh7_Size (d : ℕ) (q : ℝ) : Prop :=
  ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
    ∀ n : ℕ, ∀ x ∈ cent d n, x ∉ C →
      xmh3_V n ≤ ((componentIn Cᶜ x).ncard : ℝ) →
      xmh4_m n ≤ (innerBoundary (componentIn Cᶜ x)).ncard

/-- The three named percolation claims imply the single input `xmh6_HoleInput` of the
assembly. -/
theorem xmh7_holeInput (huniq : xmh7_Unique d q) (hloc : xmh7_Localized d q)
    (hsize : xmh7_Size d q) : xmh6_HoleInput d q := by
  filter_upwards [huniq, hloc, hsize] with ω huniq hloc hsize C hC
  obtain ⟨i, hiC, hCeq⟩ := hC.2
  refine ⟨?_, fun n x hx hxC =>
    ⟨huniq C hC x hxC, fun u hu v hv => xmh7_componentIn_conn hu hv,
      fun b hb z hbz hzC => xmh7_componentIn_close hb (by simpa using hzC) hbz,
      fun hvol => ⟨hsize C hC n x hx hxC hvol, hloc C hC n x hx hxC hvol⟩⟩⟩
  intro u hu v hv
  have h := xmh7_componentIn_conn (S := openSites ω) (x := i) (hCeq ▸ hu) (hCeq ▸ hv)
  simpa [hCeq] using h

/-- **Mathieu's hole-volume bound**, with the uniqueness of the infinite cluster, the
localisation of the hole boundary and its isoperimetric size as the only percolation inputs
besides the summability threshold. -/
theorem xmh7_proved (q₀ : ∀ d : ℕ, 2 ≤ d → ℝ) (hq₀ : ∀ d hd, q₀ d hd < 1)
    (hgood : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 → xmh6_Summability d q)
    (huniq : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 → xmh7_Unique d q)
    (hloc : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 → xmh7_Localized d q)
    (hsize : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 → xmh7_Size d q) :
    External.MathieuHoleVolume :=
  xmh6_proved q₀ hq₀ hgood fun d hd q h1 h2 =>
    xmh6_hDet_of_input
      (xmh7_holeInput (huniq d hd q h1 h2) (hloc d hd q h1 h2) (hsize d hd q h1 h2))

end Exploding
