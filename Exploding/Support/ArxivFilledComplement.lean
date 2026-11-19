import Exploding.Support.ExtMHBase

/-!
# Connected filled complements

In a connected graph, removing one component of the complement of a
connected set leaves a connected set.
-/

open Relation

namespace Exploding

/-- Removing one component of the complement of a connected set preserves
connectedness. -/
theorem connected_complement_of_complement_component {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) {A H : Set V} {a : V} (ha : a ∈ A)
    (hA : ∀ u ∈ A, ∀ v ∈ A,
      ReflTransGen (fun x y => x ∈ A ∧ y ∈ A ∧ G.Adj x y) u v)
    (hdisj : ∀ x, x ∈ A → x ∉ H)
    (hclose : ∀ x ∈ H, ∀ y, G.Adj x y → y ∉ A → y ∈ H) :
    ∀ u ∉ H, ∀ v ∉ H,
      ReflTransGen (fun x y => x ∉ H ∧ y ∉ H ∧ G.Adj x y) u v := by
  let R : V → V → Prop := fun x y => x ∉ H ∧ y ∉ H ∧ G.Adj x y
  have hmain : ∀ z, ReflTransGen G.Adj a z → z ∈ H ∨ (z ∉ H ∧ ReflTransGen R a z) := by
    intro z hz
    induction hz with
    | refl => exact Or.inr ⟨hdisj a ha, ReflTransGen.refl⟩
    | @tail b c hab hbc ih =>
      by_cases hc : c ∈ H
      · exact Or.inl hc
      · right
        refine ⟨hc, ?_⟩
        rcases ih with hb | ⟨hb, habR⟩
        · have hcA : c ∈ A := by
            by_contra hcA
            exact hc (hclose b hb c hbc hcA)
          exact ReflTransGen.mono (fun x y hxy =>
            ⟨hdisj x hxy.1, hdisj y hxy.2.1, hxy.2.2⟩) a c (hA a ha c hcA)
        · exact habR.tail ⟨hb, hc, hbc⟩
  have hpath : ∀ z, z ∉ H → ReflTransGen R a z := by
    intro z hz
    have hreach : ReflTransGen G.Adj a z := by
      rw [← SimpleGraph.reachable_iff_reflTransGen]
      exact hG a z
    exact (hmain z hreach).resolve_left hz |>.2
  intro u hu v hv
  exact (xmh_rtg_symm (fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩)
    (hpath u hu)).trans (hpath v hv)

end Exploding
