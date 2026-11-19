import Exploding.Support.ArxivBondGoodInterfaceWalk

/-!
# Confined paths by interface surgery

An open path between sites of a finite star-connected set closed under bad
star-steps can be confined to its double cube enlargement.
-/

open LatticeProb Relation

namespace Exploding

/-- Open connectivity from a site in a bad-star-closed finite set to its cube
enlargement can be confined to the double cube enlargement. -/
theorem open_reach_in_double_cube_enlargement_of_bad_star_closed
    {d : ℕ} (hd : 1 ≤ d) {ω : Site d × Fin d → Bool}
    {F : Finset (Site d)} {x y : Site d} (hx : x ∈ F)
    (hF : xmh_SConn (F : Set (Site d)))
    (hclosed : ∀ c ∈ F, ∀ z, ¬ xap_Good ω z → xmh_star c z → z ∈ F)
    (hy : y ∈ unitCubeEnlargement F) (hxy : (openBondGraph ω).Reachable x y) :
    xap_Reach ω (unitCubeEnlargement (unitCubeEnlargement F) : Set (Site d)) x y := by
  classical
  let U : Set (Site d) := unitCubeEnlargement F
  let E : Set (Site d) := unitCubeEnlargement (unitCubeEnlargement F)
  have hUE : U ⊆ E := subset_unit_cube_enlargement _
  have hxU : x ∈ U := subset_unit_cube_enlargement F hx
  have hcomp_eq : ∀ {u v}, v ∈ componentIn Uᶜ u → componentIn Uᶜ u = componentIn Uᶜ v := by
    intro u v hv
    rcases hv with ⟨huU, hvU, huv⟩
    ext z
    constructor
    · rintro ⟨_, hzU, huz⟩
      exact ⟨hvU, hzU, huv.symm.trans huz⟩
    · rintro ⟨_, hzU, hvz⟩
      exact ⟨huU, hzU, huv.trans hvz⟩
  have hconnect : ∀ z ∉ U, ∀ u ∈ U, ∀ v ∈ U,
      (∃ t ∈ componentIn Uᶜ z, (lattice d).Adj t u) →
      (∃ t ∈ componentIn Uᶜ z, (lattice d).Adj t v) → xap_Reach ω E u v := by
    intro z hz u hu v hv hzu hzv
    let H := componentIn Uᶜ z
    let I : Set (Site d) := {w | w ∉ H ∧ ∃ t ∈ H, (lattice d).Adj t w}
    have hI : xmh_SConn I ∧ ∀ w ∈ I, w ∈ innerBoundary U ∧ xap_Good ω w :=
      enlarged_bad_star_closed_set_interface (x := z) hd hx hF hclosed
    have hIu : u ∈ I := ⟨fun h => h.2.1 hu, hzu⟩
    have hIv : v ∈ I := ⟨fun h => h.2.1 hv, hzv⟩
    exact open_reach_in_unit_cube_enlargement_of_good_star_connected hI.1
      (fun w hw => (hI.2 w hw).1.1) (fun w hw => (hI.2 w hw).2) hIu hIv
  let T : Site d → Prop := fun z =>
    (z ∈ U ∧ xap_Reach ω E x z) ∨
      (z ∉ U ∧ ∃ t ∈ componentIn Uᶜ z, ∃ u ∈ U,
        (lattice d).Adj t u ∧ xap_Reach ω E x u)
  have hstate : ∀ z, ReflTransGen (openBondGraph ω).Adj x z → T z := by
    intro z hz
    induction hz with
    | refl => exact Or.inl ⟨hxU, xap_reach_refl (hUE hxU)⟩
    | @tail u v _ huv ih =>
      have hlat : (lattice d).Adj u v := xap_lattice_of_open huv
      by_cases hvU : v ∈ U
      · left
        refine ⟨hvU, ?_⟩
        rcases ih with ⟨huU, hxu⟩ | ⟨huU, t, ht, w, hwU, htw, hxw⟩
        · exact xap_reach_trans hxu (xap_reach_step (hUE huU) (hUE hvU) huv)
        · have hucomp : u ∈ componentIn Uᶜ u :=
            ⟨huU, huU, SimpleGraph.Reachable.refl _⟩
          exact xap_reach_trans hxw
            (hconnect u huU w hwU v hvU ⟨t, ht, htw⟩ ⟨u, hucomp, hlat⟩)
      · right
        refine ⟨hvU, ?_⟩
        rcases ih with ⟨huU, hxu⟩ | ⟨huU, t, ht, w, hwU, htw, hxw⟩
        · have hvcomp : v ∈ componentIn Uᶜ v :=
            ⟨hvU, hvU, SimpleGraph.Reachable.refl _⟩
          exact ⟨v, hvcomp, u, huU, hlat.symm, hxu⟩
        · have hucomp : u ∈ componentIn Uᶜ u :=
            ⟨huU, huU, SimpleGraph.Reachable.refl _⟩
          have hvcomp : v ∈ componentIn Uᶜ u := xmh_componentIn_step hucomp hvU hlat
          have heq := hcomp_eq hvcomp
          exact ⟨t, heq ▸ ht, w, hwU, htw, hxw⟩
  have hxy' : ReflTransGen (openBondGraph ω).Adj x y := by
    rw [← SimpleGraph.reachable_iff_reflTransGen]
    exact hxy
  exact ((hstate y hxy').resolve_right (fun h => h.1 hy)).2

end Exploding
