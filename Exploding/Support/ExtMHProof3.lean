/-
The hole-volume assembly: the union bound over a finite set of starting points for the Peierls
estimate on `*`-connected closed sets, and its Borel-Cantelli consequence.  The deterministic
input that a large hole produces such a closed set (the boundary `xmh_BoundaryStar` plus an
isoperimetric lower bound on its size) is isolated as a hypothesis of the final step.
-/
import Exploding.Support.ExtMHProof2

namespace Exploding

open LatticeProb MeasureTheory Filter
open scoped BigOperators

variable {d : ℕ}

/-- **Peierls union bound over a finite set of starting points.**  For a finite set `S` of
sites and a size `m`, the probability that some `*`-connected set of `m` closed sites contains
a point of `S` is at most `|S| K ^ m (1 - q) ^ m`. -/
theorem xmh2_finset_closed_prob (hSC : xmh_StarCount d) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (S : Finset (Site d)) (m : ℕ) :
    sitePercolation d q {ω : Site d → Bool |
        ∃ p ∈ S, ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false}
      ≤ (S.card : ENNReal) * ((Classical.choose hSC) ^ m * ENNReal.ofReal (1 - q) ^ m) := by
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
      ≤ ∑ _p ∈ S, (Classical.choose hSC) ^ m * ENNReal.ofReal (1 - q) ^ m :=
        Finset.sum_le_sum fun p _ => xmh2_starconn_closed_prob hSC h0 h1 p m
    _ = (S.card : ENNReal) * ((Classical.choose hSC) ^ m * ENNReal.ofReal (1 - q) ^ m) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Borel-Cantelli consequence.**  If the Peierls bounds over a sequence of boxes are
summable, then almost surely only finitely many boxes carry a `*`-connected closed set of the
prescribed size. -/
theorem xmh2_ae_eventually_notMem {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : ℕ → Set Ω) (hs : (∑' n : ℕ, μ (s n)) ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ω ∉ s n :=
  MeasureTheory.ae_eventually_notMem hs

end Exploding

namespace Exploding

open LatticeProb MeasureTheory Filter

variable {d : ℕ}

/-- **Deterministic hole reduction.**  Fix a threshold function `V` and a "bad" predicate on
configurations and scales.  If every failure of the hole bound at scale `n` produces a bad
configuration, and almost surely no bad configuration occurs for large `n`, then almost surely
every infinite open cluster has all its complementary components finite of `ncard` below `V`. -/
theorem xmh2_hole_small_of_no_bad {q : ℝ} (V : ℕ → ℝ) (Bad : (Site d → Bool) → ℕ → Prop)
    (hDet : ∀ (ω : Site d → Bool) (n : ℕ) (C : Set (Site d)), IsInfiniteOpenCluster ω C →
      (∃ x ∈ cent d n, x ∉ C ∧
        ¬ ((componentIn Cᶜ x).Finite ∧ ((componentIn Cᶜ x).ncard : ℝ) < V n)) → Bad ω n)
    (hno : ∀ᵐ ω ∂(sitePercolation d q), ∀ᶠ n : ℕ in atTop, ¬ Bad ω n) :
    ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ cent d n, x ∉ C →
        (componentIn Cᶜ x).Finite ∧ ((componentIn Cᶜ x).ncard : ℝ) < V n := by
  filter_upwards [hno] with ω hω C hC
  rw [Filter.eventually_atTop] at hω
  obtain ⟨n0, hn0⟩ := hω
  refine ⟨n0, fun n hn x hx hxC => ?_⟩
  by_contra hcon
  exact hn0 n hn (hDet ω n C hC ⟨x, hx, hxC, hcon⟩)

end Exploding
