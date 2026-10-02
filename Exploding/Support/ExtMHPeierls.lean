/-
The enlarged Peierls event for the holes of the infinite cluster: a `*`-connected all-closed
set of at least `xmh4_m n` sites with a point within sup-distance `n` plus its size of the
origin.  Its probability is bounded by a geometric tail of the Peierls estimates, the bounds
are summable in `n` when `2 · 6^d · K · (1 - q) < 1`, so almost surely the event fails for all
large `n`; and a finite `*`-connected all-closed set of the right size near the box realises
the event.
-/
import Exploding.Support.ExtMHProof10

namespace Exploding

open LatticeProb MeasureTheory Filter
open scoped BigOperators ENNReal

variable {d : ℕ}

/-- The enlarged bad event at scale `n`: for some `j`, a `*`-connected all-closed set of
`xmh4_m n + j` sites meets the box `[-(n + xmh4_m n + j), n + xmh4_m n + j]^d`. -/
def xmp_bad (d n : ℕ) (ω : Site d → Bool) : Prop :=
  ∃ j : ℕ, ∃ p ∈ xmh4_centFinset d (n + (xmh4_m n + j)), ∃ F : Finset (Site d),
    p ∈ F ∧ F.card = xmh4_m n + j ∧ xmh_SConn (F : Set (Site d)) ∧ ∀ z ∈ F, ω z = false

/-- Peierls bound on the enlarged bad event, as a series over the excess size `j`. -/
theorem xmp_bad_prob {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (n : ℕ) :
    sitePercolation d q {ω | xmp_bad d n ω} ≤
      ∑' j : ℕ, ((xmh4_centFinset d (n + (xmh4_m n + j))).card : ENNReal) *
        ((xmh6_K d : ENNReal) ^ (xmh4_m n + j) * ENNReal.ofReal (1 - q) ^ (xmh4_m n + j)) := by
  have hset : {ω : Site d → Bool | xmp_bad d n ω} = ⋃ j : ℕ, {ω : Site d → Bool |
      ∃ p ∈ xmh4_centFinset d (n + (xmh4_m n + j)), ∃ F : Finset (Site d),
        p ∈ F ∧ F.card = xmh4_m n + j ∧ xmh_SConn (F : Set (Site d)) ∧
          ∀ z ∈ F, ω z = false} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, xmp_bad]
  rw [hset]
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => ?_)
  exact xmh5_finset_closed_prob (xmh6_K d) (xmh6_K_spec d) h0 h1 _ _

/-- `2m + 1 ≤ 3^m`. -/
theorem xmp_two_mul_add_one_le (m : ℕ) : 2 * m + 1 ≤ 3 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ]
    omega

/-- The side of the enlarged box is dominated by a product. -/
theorem xmp_box_mul (n m : ℕ) : 2 * (n + m) + 1 ≤ (2 * n + 1) * (2 * m + 1) := by
  nlinarith

/-- Summability of the enlarged Peierls bounds when `2 · 6^d · K · (1 - q) < 1`. -/
theorem xmp_tsum_ne_top {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hr : ((6 : ENNReal) ^ d * ((xmh6_K d : ENNReal) * ENNReal.ofReal (1 - q))) * 2 < 1) :
    (∑' n : ℕ, sitePercolation d q {ω | xmp_bad d n ω}) ≠ ⊤ := by
  set r : ENNReal := (xmh6_K d : ENNReal) * ENNReal.ofReal (1 - q) with hrdef
  set c₁ : ENNReal := (3 : ENNReal) ^ d * r with hc₁def
  set c : ENNReal := (2 : ENNReal) ^ d * c₁ with hcdef
  have hc6 : c = (6 : ENNReal) ^ d * r := by
    rw [hcdef, hc₁def, ← mul_assoc, ← mul_pow]
    norm_num
  have hc2 : c * 2 < 1 := by
    rw [hc6]
    exact hr
  have hc_lt : c < 1 := by
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * 2 := by gcongr; norm_num
      _ < 1 := hc2
  have hc₁_le_c : c₁ ≤ c := by
    rw [hcdef]
    exact le_mul_of_one_le_left' (one_le_pow₀ (by norm_num : (1 : ENNReal) ≤ 2))
  have hc₁_lt : c₁ < 1 := lt_of_le_of_lt hc₁_le_c hc_lt
  have hterm : ∀ n j : ℕ,
      ((xmh4_centFinset d (n + (xmh4_m n + j))).card : ENNReal) *
        ((xmh6_K d : ENNReal) ^ (xmh4_m n + j) * ENNReal.ofReal (1 - q) ^ (xmh4_m n + j))
      ≤ ((2 * n + 1 : ℕ) : ENNReal) ^ d * (c₁ ^ (xmh4_m n) * c₁ ^ j) := by
    intro n j
    rw [← mul_pow, ← hrdef, xmh4_centFinset_card, Nat.cast_pow]
    have hb1 : ((2 * (n + (xmh4_m n + j)) + 1 : ℕ) : ENNReal)
        ≤ ((2 * n + 1 : ℕ) : ENNReal) * ((2 * (xmh4_m n + j) + 1 : ℕ) : ENNReal) := by
      rw [← Nat.cast_mul]
      exact_mod_cast xmp_box_mul n (xmh4_m n + j)
    have hb2 : ((2 * (xmh4_m n + j) + 1 : ℕ) : ENNReal) ≤ (3 : ENNReal) ^ (xmh4_m n + j) := by
      exact_mod_cast xmp_two_mul_add_one_le (xmh4_m n + j)
    calc ((2 * (n + (xmh4_m n + j)) + 1 : ℕ) : ENNReal) ^ d * r ^ (xmh4_m n + j)
        ≤ (((2 * n + 1 : ℕ) : ENNReal) * ((2 * (xmh4_m n + j) + 1 : ℕ) : ENNReal)) ^ d *
            r ^ (xmh4_m n + j) := by gcongr
      _ ≤ (((2 * n + 1 : ℕ) : ENNReal) * (3 : ENNReal) ^ (xmh4_m n + j)) ^ d *
            r ^ (xmh4_m n + j) := by gcongr
      _ = ((2 * n + 1 : ℕ) : ENNReal) ^ d * (c₁ ^ (xmh4_m n) * c₁ ^ j) := by
          rw [hc₁def]
          ring
  have hgeom : ∀ n : ℕ, sitePercolation d q {ω | xmp_bad d n ω}
      ≤ ((2 * n + 1 : ℕ) : ENNReal) ^ d * c₁ ^ (xmh4_m n) * (1 - c₁)⁻¹ := by
    intro n
    refine (xmp_bad_prob h0 h1 n).trans ?_
    calc ∑' j : ℕ, ((xmh4_centFinset d (n + (xmh4_m n + j))).card : ENNReal) *
          ((xmh6_K d : ENNReal) ^ (xmh4_m n + j) * ENNReal.ofReal (1 - q) ^ (xmh4_m n + j))
        ≤ ∑' j : ℕ, ((2 * n + 1 : ℕ) : ENNReal) ^ d * (c₁ ^ (xmh4_m n) * c₁ ^ j) :=
          ENNReal.tsum_le_tsum (hterm n)
      _ = ((2 * n + 1 : ℕ) : ENNReal) ^ d * c₁ ^ (xmh4_m n) * ∑' j : ℕ, c₁ ^ j := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, mul_assoc]
      _ = ((2 * n + 1 : ℕ) : ENNReal) ^ d * c₁ ^ (xmh4_m n) * (1 - c₁)⁻¹ := by
          rw [ENNReal.tsum_geometric]
  have hbound : ∀ n, sitePercolation d q {ω | xmp_bad d n ω}
      ≤ ((6 : ENNReal) ^ d * (1 - c₁)⁻¹) * c ^ (Nat.log 2 n) := by
    intro n
    refine (hgeom n).trans ?_
    have hbox : ((2 * n + 1 : ℕ) : ENNReal) ^ d
        ≤ (6 : ENNReal) ^ d * ((2 : ENNReal) ^ d) ^ (Nat.log 2 n) := by
      have h := xmh5_centFinset_card_bound d n
      rwa [xmh4_centFinset_card, Nat.cast_pow] at h
    have hpow : c₁ ^ (xmh4_m n) ≤ c₁ ^ (Nat.log 2 n) :=
      pow_le_pow_of_le_one zero_le hc₁_lt.le (le_max_right _ _)
    calc ((2 * n + 1 : ℕ) : ENNReal) ^ d * c₁ ^ (xmh4_m n) * (1 - c₁)⁻¹
        ≤ ((6 : ENNReal) ^ d * ((2 : ENNReal) ^ d) ^ (Nat.log 2 n)) * c₁ ^ (Nat.log 2 n) *
            (1 - c₁)⁻¹ := by gcongr
      _ = ((6 : ENNReal) ^ d * (1 - c₁)⁻¹) * c ^ (Nat.log 2 n) := by
          rw [hcdef]
          ring
  have hle : (∑' n, sitePercolation d q {ω | xmp_bad d n ω})
      ≤ ((6 : ENNReal) ^ d * (1 - c₁)⁻¹) * ∑' n, c ^ (Nat.log 2 n) :=
    (ENNReal.tsum_le_tsum hbound).trans_eq ENNReal.tsum_mul_left
  have hne : (1 - c₁) ≠ 0 := by
    intro h
    exact absurd (tsub_eq_zero_iff_le.mp h) (not_le_of_gt hc₁_lt)
  refine ne_top_of_le_ne_top ?_ hle
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (ENNReal.inv_ne_top.mpr hne))
    (xmh4_tsum_log_ne_top c hc2)

/-- Almost surely the enlarged bad event fails for all large `n`. -/
theorem xmp_ae_no_bad {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hr : ((6 : ENNReal) ^ d * ((xmh6_K d : ENNReal) * ENNReal.ofReal (1 - q))) * 2 < 1) :
    ∀ᵐ ω ∂(sitePercolation d q), ∀ᶠ n : ℕ in atTop, ¬ xmp_bad d n ω :=
  xmh2_ae_eventually_notMem (sitePercolation d q) (fun n => {ω : Site d → Bool | xmp_bad d n ω})
    (xmp_tsum_ne_top h0 h1 hr)

/-- A finite `*`-connected all-closed set of at least `xmh4_m n` sites with a point within
sup-distance `n + |D|` of the origin realises the enlarged bad event. -/
theorem xmp_bad_of_boundary {ω : Site d → Bool} {n : ℕ} {D : Set (Site d)} (hfin : D.Finite)
    (hconn : xmh_SConn D) (hclosed : ∀ z ∈ D, ω z = false) (hsize : xmh4_m n ≤ D.ncard)
    (hnear : ∃ p ∈ D, ∀ i, |p i| ≤ (n : ℤ) + D.ncard) : xmp_bad d n ω := by
  obtain ⟨p, hpD, hp⟩ := hnear
  refine ⟨D.ncard - xmh4_m n, p, ?_, hfin.toFinset, ?_, ?_, ?_, ?_⟩
  · rw [xmh4_mem_centFinset]
    intro i
    have h := hp i
    rw [Nat.add_sub_cancel' hsize]
    push_cast
    exact h
  · exact hfin.mem_toFinset.mpr hpD
  · rw [← Set.ncard_eq_toFinset_card D hfin, Nat.add_sub_cancel' hsize]
  · rw [hfin.coe_toFinset]
    exact hconn
  · intro z hz
    exact hclosed z (hfin.mem_toFinset.mp hz)

end Exploding
