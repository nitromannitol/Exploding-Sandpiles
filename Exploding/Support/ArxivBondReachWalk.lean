import Exploding.Support.ArxivBondConfinedSurgery

/-!
# Confined open walks from restricted reachability

A finite chain of open bonds in a set gives an open walk with support in that set.
-/

open LatticeProb Relation

namespace Exploding

/-- Restricted open reachability gives an open walk contained in the restricting set. -/
theorem open_walk_of_reach_in_set {d : ℕ} {ω : Site d × Fin d → Bool}
    {S : Set (Site d)} {x y : Site d} (h : xap_Reach ω S x y) :
    ∃ p : (openBondGraph ω).Walk x y, ∀ z ∈ p.support, z ∈ S := by
  have hwalk : ∀ z, ReflTransGen (xap_RS ω S) x z →
      ∃ p : (openBondGraph ω).Walk x z, ∀ w ∈ p.support, w ∈ S := by
    intro z hz
    induction hz with
    | refl =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro w hw
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
      simpa only [hw] using h.1
    | @tail u v _ huv ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p.concat huv.2.2, ?_⟩
      intro w hw
      rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact hp w hw
      · exact huv.2.1
  exact hwalk y h.2

end Exploding
