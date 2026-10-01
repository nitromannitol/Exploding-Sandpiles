/-
The summability of the Peierls bounds for the bad event, completing the Borel–Cantelli
step.  The Peierls estimate is re-derived with an explicit constant `K` (rather than the
opaque `Classical.choose` of `xmh_StarCount`), and the box `[-n,n]^d` is bounded by
`6^d (2^d)^{Nat.log 2 n}`, so the bad-event probability is dominated by
`6^d · c^{Nat.log 2 n}` with `c = 2^d K (1-q)`, whose dyadic blocks sum to a finite quantity.
-/
import Exploding.Support.ExtMHProof8

namespace Exploding

open LatticeProb MeasureTheory Filter
open scoped BigOperators

variable {d : ℕ}

/-- Peierls estimate with an explicit constant. -/
theorem xmh5_starconn_closed_prob (K : ℕ)
    (hK : ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
      ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T)
    {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (p : Site d) (m : ℕ) :
    sitePercolation d q {ω : Site d → Bool |
        ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧ xmh_SConn (F : Set (Site d)) ∧
          ∀ x ∈ F, ω x = false}
      ≤ (K : ENNReal) ^ m * ENNReal.ofReal (1 - q) ^ m := by
  classical
  obtain ⟨T, hTcard, hTmem⟩ := hK p m
  set T' : Finset (Finset (Site d)) := T.filter (fun F => F.card = m) with hT'
  have hsub : {ω : Site d → Bool |
        ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧ xmh_SConn (F : Set (Site d)) ∧
          ∀ x ∈ F, ω x = false}
      ⊆ {ω : Site d → Bool | ∃ F ∈ T', ∀ x ∈ F, ω x = false} := by
    rintro ω ⟨F, hp, hcard, hconn, hcl⟩
    exact ⟨F, Finset.mem_filter.mpr ⟨hTmem F hp hcard hconn, hcard⟩, hcl⟩
  have hbound : sitePercolation d q
        {ω : Site d → Bool | ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false}
      ≤ (T'.card : ENNReal) * ENNReal.ofReal (1 - q) ^ m :=
    le_trans (measure_mono hsub)
      (xmh_peierls_union h0 h1 T' m fun F hF => (Finset.mem_filter.mp hF).2)
  refine le_trans hbound ?_
  gcongr
  exact_mod_cast le_trans (Finset.card_filter_le _ _) hTcard

/-- Peierls union bound with an explicit constant. -/
theorem xmh5_finset_closed_prob (K : ℕ)
    (hK : ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
      ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T)
    {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (S : Finset (Site d)) (m : ℕ) :
    sitePercolation d q {ω : Site d → Bool |
        ∃ p ∈ S, ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false}
      ≤ (S.card : ENNReal) * ((K : ENNReal) ^ m * ENNReal.ofReal (1 - q) ^ m) := by
  classical
  have hsub : {ω : Site d → Bool |
        ∃ p ∈ S, ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false}
      = ⋃ p ∈ S, {ω : Site d → Bool |
          ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
            xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]
  rw [hsub]
  refine le_trans (measure_biUnion_finset_le S _) ?_
  calc ∑ p ∈ S, sitePercolation d q {ω : Site d → Bool |
          ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
            xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false}
      ≤ ∑ _p ∈ S, (K : ENNReal) ^ m * ENNReal.ofReal (1 - q) ^ m :=
        Finset.sum_le_sum fun p _ => xmh5_starconn_closed_prob K hK h0 h1 p m
    _ = (S.card : ENNReal) * ((K : ENNReal) ^ m * ENNReal.ofReal (1 - q) ^ m) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Peierls bound on the bad event with an explicit constant. -/
theorem xmh5_bad_prob (K : ℕ)
    (hK : ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
      ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T)
    {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (n : ℕ) :
    sitePercolation d q {ω : Site d → Bool | xmh4_bad d n ω}
      ≤ (xmh4_centFinset d n).card *
          ((K : ENNReal) ^ xmh4_m n * ENNReal.ofReal (1 - q) ^ xmh4_m n) :=
  (measure_mono (xmh4_bad_subset n)).trans
    (xmh5_finset_closed_prob K hK h0 h1 (xmh4_centFinset d n) (xmh4_m n))

/-- The box `[-n,n]^d` has at most `6^d · (2^d)^{Nat.log 2 n}` sites. -/
theorem xmh5_centFinset_card_bound (d n : ℕ) :
    ((xmh4_centFinset d n).card : ENNReal)
      ≤ (6 : ENNReal) ^ d * ((2 : ENNReal) ^ d) ^ (Nat.log 2 n) := by
  rw [xmh4_centFinset_card]
  have hle : (2 * n + 1 : ℕ) ≤ 6 * 2 ^ Nat.log 2 n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; norm_num
    · have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
      have h2 : 1 ≤ 2 ^ Nat.log 2 n := one_le_pow₀ (by norm_num)
      rw [pow_succ] at hlt
      nlinarith
  have hle' : ((2 * n + 1 : ℕ) : ENNReal) ≤ ((6 * 2 ^ Nat.log 2 n : ℕ) : ENNReal) := by
    exact_mod_cast hle
  calc (((2 * n + 1) ^ d : ℕ) : ENNReal)
      = ((2 * n + 1 : ℕ) : ENNReal) ^ d := by push_cast; ring
    _ ≤ ((6 * 2 ^ Nat.log 2 n : ℕ) : ENNReal) ^ d :=
        pow_le_pow_left₀ (zero_le) hle' d
    _ = (6 : ENNReal) ^ d * ((2 : ENNReal) ^ d) ^ (Nat.log 2 n) := by
        push_cast
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (Nat.log 2 n) d, mul_comm]

/-- **Summability of the Peierls bounds.**  For `2^d · K · (1-q) · 2 < 1` the bad-event
probabilities are summable, so `hsum` holds. -/
theorem xmh5_tsum_ne_top (K : ℕ)
    (hK : ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
      ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T)
    {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hr : ((2 : ENNReal) ^ d * ((K : ENNReal) * ENNReal.ofReal (1 - q))) * 2 < 1) :
    (∑' n : ℕ, sitePercolation d q {ω : Site d → Bool | xmh4_bad d n ω}) ≠ ⊤ := by
  set r : ENNReal := (K : ENNReal) * ENNReal.ofReal (1 - q) with hrdef
  set c : ENNReal := (2 : ENNReal) ^ d * r with hcdef
  have hc2 : c * 2 < 1 := by rw [hcdef, hrdef]; exact hr
  have hc_lt : c < 1 := by
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * 2 := by gcongr; norm_num
      _ < 1 := hc2
  have hr_le_c : r ≤ c := by
    rw [hcdef]
    exact le_mul_of_one_le_left' (one_le_pow₀ (by norm_num : (1 : ENNReal) ≤ 2))
  have hr1 : r ≤ 1 := hr_le_c.trans hc_lt.le
  have hbound : ∀ n, sitePercolation d q {ω : Site d → Bool | xmh4_bad d n ω}
      ≤ (6 : ENNReal) ^ d * c ^ (Nat.log 2 n) := by
    intro n
    refine (xmh5_bad_prob K hK h0 h1 n).trans ?_
    rw [← mul_pow, ← hrdef]
    have h2 : r ^ xmh4_m n ≤ r ^ Nat.log 2 n :=
      pow_le_pow_of_le_one (zero_le) hr1 (le_max_right _ _)
    calc (xmh4_centFinset d n).card * r ^ xmh4_m n
        ≤ ((6 : ENNReal) ^ d * ((2 : ENNReal) ^ d) ^ (Nat.log 2 n)) * r ^ xmh4_m n := by
          gcongr
          exact xmh5_centFinset_card_bound d n
      _ ≤ ((6 : ENNReal) ^ d * ((2 : ENNReal) ^ d) ^ (Nat.log 2 n)) * r ^ Nat.log 2 n := by
          gcongr
      _ = (6 : ENNReal) ^ d * c ^ (Nat.log 2 n) := by
          rw [hcdef, mul_assoc, ← mul_pow]
  have hle : (∑' n, sitePercolation d q {ω : Site d → Bool | xmh4_bad d n ω})
      ≤ (6 : ENNReal) ^ d * ∑' n, c ^ (Nat.log 2 n) :=
    (ENNReal.tsum_le_tsum hbound).trans_eq ENNReal.tsum_mul_left
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_lt_top (n := d) (by norm_num : (6:ENNReal) < ⊤)).ne
    (xmh4_tsum_log_ne_top c hc2)) hle

/-- **Almost-sure eventual absence of the bad event**, with the summability discharged. -/
theorem xmh5_ae_no_bad (K : ℕ)
    (hK : ∀ (p : Site d) (m : ℕ), ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
      ∀ F : Finset (Site d), p ∈ F → F.card = m → xmh_SConn (F : Set (Site d)) → F ∈ T)
    {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hr : ((2 : ENNReal) ^ d * ((K : ENNReal) * ENNReal.ofReal (1 - q))) * 2 < 1) :
    ∀ᵐ ω ∂(sitePercolation d q), ∀ᶠ n : ℕ in atTop, ¬ xmh4_bad d n ω :=
  xmh4_ae_no_bad (xmh5_tsum_ne_top K hK h0 h1 hr)

end Exploding
