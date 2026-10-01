/-
The Borel–Cantelli assembly of Mathieu's hole-volume bound: the bad event of a
`*`-connected all-closed set of at least `Nat.log 2 n` sites meeting the box `[-n,n]^d`,
its Peierls probability bound, the almost-sure eventual absence, and the combination with
the boundary witness, the inner-boundary growth and the percolation inputs (uniqueness of
the infinite cluster and localisation of the hole boundary).
-/
import Exploding.Support.ExtMHProof7
import Exploding.External.MathieuHoles
import Exploding.Support.ExtMHProof6
import Exploding.Support.ExtMHProof3

namespace Exploding

open LatticeProb MeasureTheory Filter
open scoped BigOperators

variable {d : ℕ}

/-- The box `[-n, n]^d` as a finset. -/
noncomputable def xmh4_centFinset (d n : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) (n : ℤ)

theorem xmh4_mem_centFinset {n : ℕ} {x : Site d} :
    x ∈ xmh4_centFinset d n ↔ x ∈ cent d n := by
  simp only [xmh4_centFinset, Fintype.mem_piFinset, Finset.mem_Icc, cent, Set.mem_setOf_eq]
  constructor
  · intro h i
    rw [abs_le]
    exact h i
  · intro h i
    have := h i
    rw [abs_le] at this
    exact this

theorem xmh4_centFinset_card (d n : ℕ) :
    (xmh4_centFinset d n).card = (2 * n + 1) ^ d := by
  rw [xmh4_centFinset, Fintype.card_piFinset]
  simp only [Int.card_Icc]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- The size threshold of the bad event at scale `n`. -/
def xmh4_m (n : ℕ) : ℕ := max 1 (Nat.log 2 n)

theorem xmh4_m_pos (n : ℕ) : 1 ≤ xmh4_m n := le_max_left _ _

/-- The bad event at scale `n`: some `*`-connected all-closed set of at least `xmh4_m n`
sites meets the box `[-n, n]^d`. -/
def xmh4_bad (d n : ℕ) (ω : Site d → Bool) : Prop :=
  ∃ p ∈ xmh4_centFinset d n, ∃ F : Finset (Site d), p ∈ F ∧ xmh4_m n ≤ F.card ∧
    xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false

/-- The same event with an exact size. -/
def xmh4_badSize (d : ℕ) (S : Finset (Site d)) (m : ℕ) (ω : Site d → Bool) : Prop :=
  ∃ p ∈ S, ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
    xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false

theorem xmh4_bad_subset (n : ℕ) :
    {ω | xmh4_bad d n ω} ⊆ {ω | xmh4_badSize d (xmh4_centFinset d n) (xmh4_m n) ω} := by
  rintro ω ⟨p, hp, F, hpF, hm, hconn, hclosed⟩
  refine ⟨p, hp, ?_⟩
  have hencard : ((xmh4_m n : ℕ) : ℕ∞) ≤ (F : Set (Site d)).encard := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hm
  obtain ⟨F', hpF', hF'F, hF'card, hF'conn⟩ :=
    xmh_grow hconn hpF (xmh4_m n) (xmh4_m_pos n) hencard
  exact ⟨F', hpF', hF'card, hF'conn, fun x hx => hclosed x (hF'F hx)⟩

/-- **Peierls bound on the bad event.** -/
theorem xmh4_bad_prob (hSC : xmh_StarCount d) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (n : ℕ) :
    sitePercolation d q {ω | xmh4_bad d n ω}
      ≤ (xmh4_centFinset d n).card *
          ((Classical.choose hSC) ^ xmh4_m n * ENNReal.ofReal (1 - q) ^ xmh4_m n) :=
  (measure_mono (xmh4_bad_subset n)).trans
    (xmh2_finset_closed_prob hSC h0 h1 (xmh4_centFinset d n) (xmh4_m n))

/-- **Borel–Cantelli for the bad event**, given summability of the Peierls bounds. -/
theorem xmh4_ae_no_bad {q : ℝ} (hsum : (∑' n : ℕ, sitePercolation d q {ω | xmh4_bad d n ω}) ≠ ⊤) :
    ∀ᵐ ω ∂(sitePercolation d q), ∀ᶠ n : ℕ in atTop, ¬ xmh4_bad d n ω :=
  xmh2_ae_eventually_notMem (sitePercolation d q) (fun n => {ω : Site d → Bool | xmh4_bad d n ω}) hsum

end Exploding

namespace Exploding

open LatticeProb MeasureTheory Filter

variable {d : ℕ}

/-- The failure of the hole bound at scale `n` for a cluster `C`. -/
def xmh4_failure (d n : ℕ) (C : Set (Site d)) : Prop :=
  ∃ x ∈ cent d n, x ∉ C ∧
    ¬ ((componentIn Cᶜ x).Finite ∧ ((componentIn Cᶜ x).ncard : ℝ) < xmh3_V n)

/-- **Almost-sure hole bound from the two inputs.**  If almost surely every failure of the
hole bound at scale `n` produces a bad configuration, and almost surely no bad configuration
occurs for large `n`, then almost surely every infinite open cluster has all its complementary
components finite of volume below `xmh3_V`. -/
theorem xmh4_hole_small {q : ℝ}
    (hDet : ∀ᵐ ω ∂(sitePercolation d q), ∀ n : ℕ, ∀ C : Set (Site d),
      IsInfiniteOpenCluster ω C → xmh4_failure d n C → xmh4_bad d n ω)
    (hno : ∀ᵐ ω ∂(sitePercolation d q), ∀ᶠ n : ℕ in atTop, ¬ xmh4_bad d n ω) :
    ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ cent d n, x ∉ C →
        (componentIn Cᶜ x).Finite ∧ ((componentIn Cᶜ x).ncard : ℝ) < xmh3_V n := by
  filter_upwards [hDet, hno] with ω hd hn C hC
  rw [Filter.eventually_atTop] at hn
  obtain ⟨n0, hn0⟩ := hn
  refine ⟨n0, fun n hle x hx hxC => ?_⟩
  by_contra hcon
  exact hn0 n hle (hd n C hC ⟨x, hx, hxC, hcon⟩)

end Exploding

namespace Exploding

open LatticeProb MeasureTheory

/-- **Mathieu's hole-volume bound**, conditional on the two percolation inputs: the summability
of the Peierls bounds (`hsum`, proved by the dyadic grouping of `xmh4_bad_prob`) and the almost
sure equivalence of a large complementary component with a bad configuration (`hDet`, the
uniqueness and localisation of the infinite cluster together with `xmh3_boundary_witness` and
`xmh4_innerBoundary_iso`). -/
theorem xmh_proved
    (q₀ : ∀ d : ℕ, 2 ≤ d → ℝ) (hq₀ : ∀ d hd, q₀ d hd < 1)
    (hsum : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 →
      (∑' n : ℕ, sitePercolation d q {ω : Site d → Bool | xmh4_bad d n ω}) ≠ ⊤)
    (hDet : ∀ (d : ℕ) (hd : 2 ≤ d) (q : ℝ), q₀ d hd < q → q ≤ 1 →
      ∀ᵐ ω ∂(sitePercolation d q), ∀ n : ℕ, ∀ C : Set (Site d),
        IsInfiniteOpenCluster ω C → xmh4_failure d n C → xmh4_bad d n ω) :
    External.MathieuHoleVolume := by
  intro d hd
  exact ⟨q₀ d hd, hq₀ d hd, fun q h1 h2 =>
    xmh4_hole_small (hDet d hd q h1 h2) (xmh4_ae_no_bad (hsum d hd q h1 h2))⟩

end Exploding

namespace Exploding

open LatticeProb MeasureTheory Filter
open scoped BigOperators

variable {d : ℕ}

theorem xmh4_log_block (c : ENNReal) (i : ℕ) :
    ∑ n ∈ Finset.range (2 ^ i), c ^ (Nat.log 2 (2 ^ i + n)) = (c * 2) ^ i := by
  have h : ∀ n ∈ Finset.range (2 ^ i), c ^ (Nat.log 2 (2 ^ i + n)) = c ^ i := by
    intro n hn
    rw [Finset.mem_range] at hn
    congr 1
    rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by positivity⟩)]
    exact ⟨by omega, by have := pow_succ 2 i; omega⟩
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [mul_pow, Nat.cast_pow, Nat.cast_ofNat, mul_comm]

theorem xmh4_tsum_log_ne_top (c : ENNReal) (hc2 : c * 2 < 1) :
    (∑' n : ℕ, c ^ (Nat.log 2 n)) ≠ ⊤ := by
  have hstep : ∀ i, ∑ n ∈ Finset.range (2 ^ (i + 1)), c ^ (Nat.log 2 n)
      = (∑ n ∈ Finset.range (2 ^ i), c ^ (Nat.log 2 n)) + (c * 2) ^ i := by
    intro i
    rw [show 2 ^ (i + 1) = 2 ^ i + 2 ^ i by rw [pow_succ]; ring]
    rw [Finset.sum_range_add, xmh4_log_block]
  have hS : ∀ i, ∑ n ∈ Finset.range (2 ^ i), c ^ (Nat.log 2 n)
      = 1 + ∑ j ∈ Finset.range i, (c * 2) ^ j := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [hstep i, ih, Finset.sum_range_succ]; ring
  have hle : ∀ i, ∑ n ∈ Finset.range (2 ^ i), c ^ (Nat.log 2 n)
      ≤ 1 + (1 - c * 2)⁻¹ := by
    intro i
    rw [hS i]
    gcongr
    rw [← ENNReal.tsum_geometric (c * 2)]
    exact ENNReal.sum_le_tsum _
  have hne : (1 - c * 2) ≠ 0 := by
    intro h
    exact absurd (tsub_eq_zero_iff_le.mp h) (not_le_of_gt hc2)
  have hfin : (1 + (1 - c * 2)⁻¹ : ENNReal) ≠ ⊤ := by
    rw [ENNReal.add_ne_top]
    exact ⟨by simp, ENNReal.inv_ne_top.mpr hne⟩
  rw [ENNReal.tsum_eq_iSup_nat' (N := fun i => 2 ^ i)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℕ) < 2))]
  intro htop
  exact hfin (top_le_iff.mp (htop ▸ iSup_le hle))

end Exploding
