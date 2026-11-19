import Exploding.Support.ExtMHBase

/-!
# Connected unions of star-connected sets

A star-connected set stays star-connected after adjoining any family of
star-connected sets that meet it.
-/

open LatticeProb Relation

namespace Exploding

variable {d : ℕ}

/-- A union of star-connected sets is star-connected if every member of the
family meets the star-connected base set. -/
theorem star_connected_union_iUnion {ι : Type*} (P : Set (Site d))
    (C : ι → Set (Site d)) (hP : xmh_SConn P)
    (hC : ∀ i, xmh_SConn (C i)) (htouch : ∀ i, ∃ z ∈ P, z ∈ C i) :
    xmh_SConn (P ∪ ⋃ i, C i) := by
  let U : Set (Site d) := P ∪ ⋃ i, C i
  let R : Site d → Site d → Prop := fun x y => x ∈ U ∧ y ∈ U ∧ xmh_star x y
  have hliftP : ∀ {x y}, x ∈ P → y ∈ P → ReflTransGen R x y := by
    intro x y hx hy
    apply ReflTransGen.mono (fun a b hab => ?_) x y (hP x hx y hy)
    exact ⟨Set.mem_union_left _ hab.1, Set.mem_union_left _ hab.2.1, hab.2.2⟩
  have hliftC : ∀ (i : ι) {x y}, x ∈ C i → y ∈ C i → ReflTransGen R x y := by
    intro i x y hx hy
    apply ReflTransGen.mono (fun a b hab => ?_) x y (hC i x hx y hy)
    exact ⟨Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, hab.1⟩),
      Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, hab.2.1⟩), hab.2.2⟩
  have hanchor : ∀ x ∈ U, ∃ z ∈ P, ReflTransGen R x z ∧ ReflTransGen R z x := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨x, hx, ReflTransGen.refl, ReflTransGen.refl⟩
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨z, hzP, hzC⟩ := htouch i
      exact ⟨z, hzP, hliftC i hxi hzC, hliftC i hzC hxi⟩
  intro x hx y hy
  obtain ⟨a, ha, hxa, _⟩ := hanchor x hx
  obtain ⟨b, hb, _, hby⟩ := hanchor y hy
  exact hxa.trans ((hliftP ha hb).trans hby)

end Exploding
