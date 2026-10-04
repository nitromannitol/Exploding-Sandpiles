import Exploding.Support.ExtAPMinCutTwo
open Exploding LatticeProb
open scoped Classical
namespace Exploding
variable {d : ℕ}

theorem xmk_induce_connected_iff (S : Set (Site d)) :
    ((xap2_kingGraph d).induce S).Connected ↔ S.Nonempty ∧ xmh_SConn S := by
  constructor
  · intro h
    have hne : S.Nonempty := h.nonempty.elim fun u => ⟨u, u.2⟩
    refine ⟨hne, fun x hx y hy => ?_⟩
    have hreach : Relation.ReflTransGen ((xap2_kingGraph d).induce S).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
      rw [← SimpleGraph.reachable_iff_reflTransGen]
      exact h.preconnected _ _
    exact Relation.ReflTransGen.lift
      (p := fun a b : Site d => a ∈ S ∧ b ∈ S ∧ xmh_star a b)
      (fun u : ↥S => (u : Site d)) (fun u v huv => ⟨u.2, v.2, huv⟩) _ _ hreach
  · rintro ⟨hne, hconn⟩
    refine { preconnected := fun u v => ?_, nonempty := ?_ }
    · rw [SimpleGraph.reachable_iff_reflTransGen]
      have hlift : ∀ {x y : Site d},
          Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ xmh_star a b) x y →
          ∀ (hx : x ∈ S) (hy : y ∈ S),
            Relation.ReflTransGen ((xap2_kingGraph d).induce S).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
        intro x y hw
        induction hw with
        | refl => intro hx hy; exact Relation.ReflTransGen.refl
        | tail hpre hstep ih =>
          intro hx hy
          exact (ih hx hstep.1).tail hstep.2.2
      exact hlift (hconn u u.2 v v.2) u.2 v.2
    · exact hne.elim fun x hx => ⟨⟨x, hx⟩⟩

end Exploding
