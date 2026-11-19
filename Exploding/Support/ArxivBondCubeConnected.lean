import Exploding.Support.ArxivBondCubeEnlargement
import Exploding.Support.ExtMHBase

/-!
# Connectivity of cube enlargements

The unit-cube enlargement of a star-connected set is connected by
nearest-neighbor lattice steps.
-/

open LatticeProb Relation

namespace Exploding

variable {d : ℕ}

/-- The unit-cube enlargement of a star-connected set is lattice-connected. -/
theorem unit_cube_enlargement_connected {F : Finset (Site d)}
    (hF : xmh_SConn (F : Set (Site d))) :
    ∀ x ∈ unitCubeEnlargement F, ∀ y ∈ unitCubeEnlargement F,
      ReflTransGen (fun a b => a ∈ unitCubeEnlargement F ∧
        b ∈ unitCubeEnlargement F ∧ (lattice d).Adj a b) x y := by
  classical
  let R : Site d → Site d → Prop := fun a b => a ∈ unitCubeEnlargement F ∧
    b ∈ unitCubeEnlargement F ∧ (lattice d).Adj a b
  have hlocal : ∀ c ∈ F, ∀ a ∈ xap_cube c, ∀ b ∈ xap_cube c,
      ReflTransGen R a b := by
    intro c hc a ha b hb
    let ω : Site d × Fin d → Bool := fun _ => true
    have hgood : xap_Good ω c := by
      intro z i hz hzi
      rfl
    have hreach := xap_cube_reach' hgood ha hb
    apply xap_rtg_mono (p := R) _ hreach.2
    intro u v huv
    have hmem : ∀ z ∈ xap_cube c, z ∈ unitCubeEnlargement F := by
      intro z hz
      exact Finset.mem_biUnion.mpr ⟨c, hc, (xap_mem_cubeFinset c z).2 hz⟩
    exact ⟨hmem u huv.1, hmem v huv.2.1, xap_lattice_of_open huv.2.2⟩
  have hcenter : ∀ a ∈ F, ∀ b ∈ F, ReflTransGen R a b := by
    intro a ha b hb
    have hchain := hF a ha b hb
    induction hchain with
    | refl => exact ReflTransGen.refl
    | tail _ hstep ih =>
      exact (ih hstep.1).trans (hlocal _ hstep.1 _ (xap_mem_cube_self _) _
        (xap_star_mem_cube hstep.2.2))
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨b, hb, hyb⟩ := Finset.mem_biUnion.mp hy
  have hxa' : x ∈ xap_cube a := (xap_mem_cubeFinset a x).1 hxa
  have hyb' : y ∈ xap_cube b := (xap_mem_cubeFinset b y).1 hyb
  exact (hlocal a ha x hxa' a (xap_mem_cube_self a)).trans
    ((hcenter a ha b hb).trans (hlocal b hb b (xap_mem_cube_self b) y hyb'))

end Exploding
