/-
Progress on the uniqueness input of Mathieu's hole-volume bound.  The bad-event machinery
already rules out infinite `*`-connected all-closed clusters; the remaining uniqueness
statement (Burton–Keane) is isolated as `xmh8_UniqueOpen`, and the unconditional reduction of
the bound to it and the two localisation/isoperimetry claims is recorded.
-/
import Exploding.Support.ExtMHProof11

namespace Exploding

open LatticeProb MeasureTheory Filter Relation
open scoped BigOperators

variable {d : ℕ}
variable {q : ℝ}

/-- **There is almost surely no infinite `*`-connected all-closed cluster.**  An infinite
all-closed `*`-connected set meets every large box, hence produces the bad event at every
large scale, contradicting the almost-sure eventual absence of the bad event. -/
theorem xmh8_no_infinite_closed (K : ℕ)
    (hK : ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
      ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T)
    {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hr : ((2 : ENNReal) ^ d * ((K : ENNReal) * ENNReal.ofReal (1 - q))) * 2 < 1) :
    ∀ᵐ ω ∂(sitePercolation d q),
      ¬ ∃ S : Set (Site d), S.Infinite ∧ xmh_SConn S ∧ ∀ z ∈ S, ω z = false := by
  filter_upwards [xmh5_ae_no_bad K hK h0 h1 hr] with ω hno
  rw [Filter.eventually_atTop] at hno
  obtain ⟨n0, hn0⟩ := hno
  rintro ⟨S, hSinf, hSconn, hSclosed⟩
  obtain ⟨p, hpS⟩ := hSinf.nonempty
  set N : ℕ := n0 + ∑ i : Fin d, (p i).natAbs with hN
  have hpcent : p ∈ cent d N := by
    intro i
    have h1' : (p i).natAbs ≤ N := by
      rw [hN]
      have hs := Finset.single_le_sum (f := fun i : Fin d => (p i).natAbs)
        (s := Finset.univ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have h2 : (|p i| : ℤ) = ((p i).natAbs : ℤ) := by simp
    show |p i| ≤ (N : ℤ)
    rw [h2]
    exact_mod_cast h1'
  have hN0 : n0 ≤ N := by rw [hN]; exact Nat.le_add_right n0 _
  refine hn0 N hN0 ?_
  have hen : ((xmh4_m N : ℕ) : ℕ∞) ≤ S.encard :=
    by rw [Set.encard_eq_top hSinf]; exact le_top
  obtain ⟨F, hpF, hFS, hFcard, hFconn⟩ :=
    xmh_grow hSconn hpS (xmh4_m N) (xmh4_m_pos N) hen
  exact ⟨p, xmh4_mem_centFinset.mpr hpcent, F, hpF, hFcard.ge, hFconn,
    fun z hz => hSclosed z (hFS hz)⟩

/-- **Uniqueness of the infinite open cluster** (Burton–Keane): almost surely there is at most
one infinite open cluster, equivalently every component of the complement of an infinite open
cluster is finite.  Stated here as the single remaining percolation claim. -/
def xmh8_UniqueOpen (d : ℕ) (q : ℝ) : Prop :=
  ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
    ∀ x, x ∉ C → (componentIn Cᶜ x).Finite

theorem xmh8_unique_of_uniqueOpen (h : xmh8_UniqueOpen d q) : xmh7_Unique d q := h

/-- **Mathieu's hole-volume bound**, with the uniqueness of the infinite cluster
(`xmh8_UniqueOpen`), the localisation of the hole boundary and its isoperimetric size as the
only percolation inputs. -/
theorem xmh8_proved (q₀ : ∀ d : ℕ, 2 ≤ d → ℝ) (hq₀ : ∀ d hd, q₀ d hd < 1)
    (hgood : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 → xmh6_Summability d q)
    (huniq : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 → xmh8_UniqueOpen d q)
    (hloc : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 → xmh7_Localized d q)
    (hsize : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 → xmh7_Size d q) :
    External.MathieuHoleVolume :=
  xmh7_proved q₀ hq₀ hgood
    (fun d hd q h1 h2 => xmh8_unique_of_uniqueOpen (huniq d hd q h1 h2)) hloc hsize

end Exploding

namespace Exploding

open LatticeProb MeasureTheory Filter Relation
open scoped BigOperators

variable {d : ℕ}
variable {q : ℝ}

/-- The inner boundary of a hole is `*`-connected and all-closed. -/
theorem xmh8_boundary_sconn_closed {ω : Site d → Bool} {C : Set (Site d)}
    (hC : IsInfiniteOpenCluster ω C) {x : Site d} (_hxC : x ∉ C) :
    xmh_SConn (innerBoundary (componentIn Cᶜ x)) ∧
      ∀ z ∈ innerBoundary (componentIn Cᶜ x), ω z = false := by
  obtain ⟨i, hiC, hCeq⟩ := hC.2
  set B := componentIn Cᶜ x with hBdef
  have hCconn : ∀ u ∈ C, ∀ v ∈ C,
      ReflTransGen (fun a b => a ∈ C ∧ b ∈ C ∧ (lattice d).Adj a b) u v := by
    intro u hu v hv
    have h := xmh7_componentIn_conn (S := openSites ω) (x := i) (hCeq ▸ hu) (hCeq ▸ hv)
    simpa [hCeq] using h
  have hBconn : ∀ u ∈ B, ∀ v ∈ B,
      ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ (lattice d).Adj a b) u v :=
    fun u hu v hv => xmh7_componentIn_conn hu hv
  have hdisj : ∀ z, z ∈ C → z ∈ B → False := fun z hzC hzB => hzB.2.1 hzC
  have hclose : ∀ b ∈ B, ∀ z, (lattice d).Adj b z → z ∉ C → z ∈ B :=
    fun b hb z hbz hzC => xmh7_componentIn_close hb (by simpa using hzC) hbz
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
  refine ⟨hDeq ▸ hconnD, fun z hz => ?_⟩
  obtain ⟨hzB, y, hyB, hzy⟩ := hz
  have hyC : y ∈ C := by
    by_contra hyC
    exact hyB (hclose z hzB y hzy hyC)
  exact xmh5_boundary_closed (i := i) (B := B)
    (fun z hzB hzC => hzB.2.1 (hCeq.symm ▸ hzC)) hzB ⟨y, hCeq ▸ hyC, hzy.symm⟩

/-- **The uniqueness of the infinite cluster reduces to a purely geometric claim:** an infinite
component of the complement of an infinite open cluster has infinite inner boundary. -/
theorem xmh8_unique_of_boundaryInfinite (K : ℕ)
    (hK : ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
      ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T)
    {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hr : ((2 : ENNReal) ^ d * ((K : ENNReal) * ENNReal.ofReal (1 - q))) * 2 < 1)
    (hbi : ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
      ∀ x, x ∉ C → (componentIn Cᶜ x).Infinite → (innerBoundary (componentIn Cᶜ x)).Infinite) :
    xmh7_Unique d q := by
  filter_upwards [hbi, xmh8_no_infinite_closed K hK h0 h1 hr] with ω hbi hno C hC x hxC
  by_contra hBfin
  have hBinf : (componentIn Cᶜ x).Infinite := Set.not_finite.mp hBfin
  obtain ⟨hconn, hclosed⟩ := xmh8_boundary_sconn_closed hC hxC
  exact hno ⟨innerBoundary (componentIn Cᶜ x), hbi C hC x hxC hBinf, hconn, hclosed⟩

end Exploding
