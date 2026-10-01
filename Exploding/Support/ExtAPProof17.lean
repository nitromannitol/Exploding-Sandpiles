/-
Structural steps for the infinite-cluster case: an infinite good cluster contains
good star-walks of every length.

A star-step changes the Manhattan norm by at most `d`
(`xap17_mnorm_star_le`), so a good star-walk of length `ℓ` starting at the origin
ends at a site of norm at most `d ℓ` (`xap17_walk_mnorm_le`).  Hence an infinite
good cluster — which has good sites at every distance
(`xap15_not_smallCluster_unbounded`) — contains good star-walks of arbitrarily
large length (`xap17_infiniteCluster_longWalk`).  This is the structural reason
the infinite-cluster case cannot be reached by a fixed-length Peierls count.

The good-crossing event is monotone in the configuration, matching
`xap15_openCrosses_mono`.
-/
import Exploding.Support.ExtAPProof16

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology

namespace Exploding

variable {d : ℕ}

/-! ### A star-step changes `mnorm` by at most `d` -/

theorem xap17_star_symm {a b : Site d} (h : xap_Star a b) : xap_Star b a :=
  ⟨h.1.symm, fun i => by rw [abs_sub_comm]; exact h.2 i⟩

/-- A star-step changes the Manhattan norm by at most `d`. -/
theorem xap17_mnorm_star_le {a b : Site d} (hab : xap_Star a b) :
    mnorm a ≤ mnorm b + (d : ℤ) := by
  rw [mnorm, mnorm]
  calc ∑ i, |a i| ≤ ∑ i, (|b i| + 1) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : |a i - b i| ≤ 1 := hab.2 i
        have h2 : b i + (a i - b i) = a i := by ring
        rw [← h2]
        exact (abs_add_le _ _).trans (add_le_add (le_refl _) h1)
    _ = ∑ i, |b i| + (d : ℤ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp

theorem xap17_mnorm_star_le' {a b : Site d} (hab : xap_Star a b) :
    mnorm b ≤ mnorm a + (d : ℤ) :=
  xap17_mnorm_star_le (xap17_star_symm hab)

/-- A star-walk of length `ℓ` from `a` to `b` satisfies `mnorm b ≤ mnorm a + d ℓ`. -/
theorem xap17_walk_mnorm_le {a b : Site d} (p : (xap2_kingGraph d).Walk a b) :
    mnorm b ≤ mnorm a + (d : ℤ) * (p.length : ℤ) := by
  induction p with
  | nil => simp
  | cons h p' ih =>
      have h1 : mnorm _ ≤ mnorm _ + (d : ℤ) := xap17_mnorm_star_le' h
      rw [SimpleGraph.Walk.length_cons]
      push_cast
      linarith [ih, h1]

/-! ### An infinite good cluster has arbitrarily long good walks -/

/-- An infinite good cluster contains a good star-walk from the origin of length
greater than `L`, for every `L`. -/
theorem xap17_infiniteCluster_longWalk (hd : 1 ≤ d) {ω : Site d × Fin d → Bool}
    (h : ¬ xap5_SmallCluster ω) (L : ℕ) :
    ∃ z : Site d, xap3_GoodConnected ω z ∧
      ∃ p : (xap2_kingGraph d).Walk (0 : Site d) z,
        (∀ w ∈ p.support, xap_Good ω w) ∧ L < p.length := by
  obtain ⟨z, hz, hzn⟩ := xap15_not_smallCluster_unbounded h (d * L + 1)
  obtain ⟨p, hp⟩ := hz
  refine ⟨z, ⟨p, hp⟩, p, hp, ?_⟩
  have h0 : mnorm (0 : Site d) = 0 := by simp [mnorm]
  have hb := xap17_walk_mnorm_le p
  rw [h0, zero_add] at hb
  have hlt : ((d * L + 1 : ℕ) : ℤ) < (d : ℤ) * (p.length : ℤ) := lt_of_lt_of_le hzn hb
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hlt' : (d : ℤ) * (L : ℤ) + 1 < (d : ℤ) * (p.length : ℤ) := by
    have hc : ((d * L + 1 : ℕ) : ℤ) = (d : ℤ) * (L : ℤ) + 1 := by push_cast; ring
    rw [hc] at hlt; exact hlt
  have : (L : ℤ) < (p.length : ℤ) := by nlinarith [hlt', hd']
  exact_mod_cast this

/-! ### Good crossings are monotone -/

theorem xap17_goodCrosses_mono {n : ℕ} {i : Fin d} {ω ω' : Site d × Fin d → Bool}
    (h : ∀ z, xap_Good ω z → xap_Good ω' z) (hc : xap16_GoodCrosses d n i ω) :
    xap16_GoodCrosses d n i ω' := by
  obtain ⟨x, y, hx, hy, hxb, hyb, p, hp, hpb⟩ := hc
  exact ⟨x, y, hx, hy, hxb, hyb, p, fun z hz => h z (hp z hz), hpb⟩

end Exploding
