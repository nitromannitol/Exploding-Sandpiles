/-
Confinement of open paths by renormalized interface surgery.

Blocks of side `N` play the role of sites.  A predicate `good` on blocks and, for each block, a
set `core b` of sites (the crossing cluster of a good block) are linked to the bond
configuration by four deterministic properties (`BlockLinks`): a good block has a nonempty core;
a site of a good block with an open connection leaving the window of its block is joined to the
core inside the window; the core of a good block is connected inside its window; and the cores
of two star-adjacent good blocks are joined inside the union of their windows.  Under these
properties an open path between two sites can be replaced by an open path inside the sites of a
bounded enlargement of any finite star-connected set of blocks that is closed under bad
star-steps and contains the blocks of its endpoints.  This is the block form of
`open_reach_in_double_cube_enlargement_of_bad_star_closed` (compare Antal and Pisztora, *On the
chemical distance for supercritical Bernoulli percolation*, Ann. Probab. 24 (1996),
Proposition 3.1).
-/
import Exploding.Support.APCoarseGeometry
import Exploding.Support.APPredicateHalo

open LatticeProb Relation

namespace Exploding

variable {d : ℕ}

/-- The site `u` has an open connection to a site outside the window of its block. -/
def LeavesWindow (N r : ℕ) (ω : Site d × Fin d → Bool) (u : Site d) : Prop :=
  ∃ e, e ∉ coarseWindow N r (coarseSite N u) ∧ (openBondGraph ω).Reachable u e

/-- The deterministic links between good blocks, their cores and the open bonds of `ω`. -/
structure BlockLinks (N r : ℕ) (ω : Site d × Fin d → Bool) (good : Site d → Prop)
    (core : Site d → Set (Site d)) : Prop where
  nonempty : ∀ b, good b → (core b).Nonempty
  attach : ∀ u, good (coarseSite N u) → LeavesWindow N r ω u →
    ∃ c ∈ core (coarseSite N u), xap_Reach ω (coarseWindow N r (coarseSite N u)) u c
  inner : ∀ b, good b → ∀ c ∈ core b, ∀ c' ∈ core b, xap_Reach ω (coarseWindow N r b) c c'
  link : ∀ b b', good b → good b' → xmh_star b b' → ∀ c ∈ core b, ∀ c' ∈ core b',
    xap_Reach ω (coarseWindow N r b ∪ coarseWindow N r b') c c'

theorem mem_coarseEnlargement_of_unitCube {r : ℕ} {F : Finset (Site d)} {b c : Site d}
    (hb : b ∈ unitCubeEnlargement F) (hc : c ∈ coarseCube r b) :
    c ∈ coarseEnlargement (r + 1) F := by
  obtain ⟨a, ha, hba⟩ := Finset.mem_biUnion.mp hb
  have hba' : b ∈ xap_cube a := (xap_mem_cubeFinset a b).1 hba
  refine mem_coarseEnlargement.mpr ⟨a, ha, fun i => ?_⟩
  have h1 := hc i
  have h2 := hba' i
  rw [abs_le] at h1 h2 ⊢
  push_cast
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Block surgery.**  Under `BlockLinks`, an open path from `x` to `y`, whose blocks lie in a
finite star-connected set `F` of blocks closed under bad star-steps (respectively in its
unit-cube enlargement), can be confined to the sites of the blocks of the enlargement of `F` by
cubes of radius `r + 1`, provided no window contains both `x` and `y`. -/
theorem open_reach_in_coarseEnlargement_of_closed (hd : 1 ≤ d) {N r : ℕ} (hN : 0 < N)
    {ω : Site d × Fin d → Bool} {good : Site d → Prop} {core : Site d → Set (Site d)}
    (hL : BlockLinks N r ω good core) {F : Finset (Site d)} {x y : Site d}
    (hx : coarseSite N x ∈ F) (hF : xmh_SConn (F : Set (Site d)))
    (hclosed : ∀ c ∈ F, ∀ z, ¬ good z → xmh_star c z → z ∈ F)
    (hy : coarseSite N y ∈ unitCubeEnlargement F)
    (hfar : ∀ b, x ∉ coarseWindow N r b ∨ y ∉ coarseWindow N r b)
    (hxy : (openBondGraph ω).Reachable x y) :
    xap_Reach ω (coarseRegion N (coarseEnlargement (r + 1) F : Set (Site d))) x y := by
  classical
  let U : Set (Site d) := unitCubeEnlargement F
  let E : Set (Site d) := coarseRegion N (coarseEnlargement (r + 1) F : Set (Site d))
  have hWE : ∀ b ∈ U, coarseWindow N r b ⊆ E := fun b hb u hu =>
    mem_coarseEnlargement_of_unitCube hb hu
  have hUE : ∀ u, coarseSite N u ∈ U → u ∈ E := fun u hu =>
    hWE _ hu (mem_coarseWindow_self N r u)
  have hxU : coarseSite N x ∈ U := subset_unit_cube_enlargement F hx
  have hleave : ∀ z, ReflTransGen (openBondGraph ω).Adj x z → LeavesWindow N r ω z := by
    intro z hz
    have hxz : (openBondGraph ω).Reachable x z := by
      rw [SimpleGraph.reachable_iff_reflTransGen]
      exact hz
    rcases hfar (coarseSite N z) with h | h
    · exact ⟨x, h, hxz.symm⟩
    · exact ⟨y, h, hxz.symm.trans hxy⟩
  have hcomp_eq : ∀ {u v}, v ∈ componentIn Uᶜ u → componentIn Uᶜ u = componentIn Uᶜ v := by
    intro u v hv
    rcases hv with ⟨huU, hvU, huv⟩
    ext z
    constructor
    · rintro ⟨_, hzU, huz⟩
      exact ⟨hvU, hzU, huv.symm.trans huz⟩
    · rintro ⟨_, hzU, hvz⟩
      exact ⟨huU, hzU, huv.trans hvz⟩
  have hconnect : ∀ z ∉ U, ∀ u w, coarseSite N u ∈ U → coarseSite N w ∈ U →
      (∃ t ∈ componentIn Uᶜ z, (lattice d).Adj t (coarseSite N u)) →
      (∃ t ∈ componentIn Uᶜ z, (lattice d).Adj t (coarseSite N w)) →
      LeavesWindow N r ω u → LeavesWindow N r ω w → xap_Reach ω E u w := by
    intro z hz u w hu hw hzu hzw hlu hlw
    let H := componentIn Uᶜ z
    let I : Set (Site d) := {v | v ∉ H ∧ ∃ t ∈ H, (lattice d).Adj t v}
    have hI : xmh_SConn I ∧ ∀ v ∈ I, v ∈ innerBoundary U ∧ good v :=
      pred_enlarged_closed_set_interface (x := z) hd hx hF hclosed
    have hIU : ∀ v ∈ I, v ∈ U := fun v hv => (hI.2 v hv).1.1
    have hIu : coarseSite N u ∈ I := ⟨fun h => h.2.1 hu, hzu⟩
    have hIw : coarseSite N w ∈ I := ⟨fun h => h.2.1 hw, hzw⟩
    obtain ⟨cu, hcu, hucu⟩ := hL.attach u (hI.2 _ hIu).2 hlu
    obtain ⟨cw, hcw, hwcw⟩ := hL.attach w (hI.2 _ hIw).2 hlw
    have hchain : ∀ b, ReflTransGen (fun a b => a ∈ I ∧ b ∈ I ∧ xmh_star a b)
        (coarseSite N u) b → ∀ c ∈ core b, xap_Reach ω E cu c := by
      intro b hb
      induction hb with
      | refl =>
        intro c hc
        exact xap_reach_mono (hWE _ hu) (hL.inner _ (hI.2 _ hIu).2 cu hcu c hc)
      | @tail a b _ hstep ih =>
        intro c hc
        obtain ⟨ca, hca⟩ := hL.nonempty a (hI.2 a hstep.1).2
        refine xap_reach_trans (ih ca hca) (xap_reach_mono ?_
          (hL.link a b (hI.2 a hstep.1).2 (hI.2 b hstep.2.1).2 hstep.2.2 ca hca c hc))
        exact Set.union_subset (hWE a (hIU a hstep.1)) (hWE b (hIU b hstep.2.1))
    have hcucw := hchain _ (hI.1 _ hIu _ hIw) cw hcw
    exact xap_reach_trans (xap_reach_mono (hWE _ hu) hucu)
      (xap_reach_trans hcucw (xap_reach_symm (xap_reach_mono (hWE _ hw) hwcw)))
  let T : Site d → Prop := fun z =>
    (coarseSite N z ∈ U ∧ xap_Reach ω E x z) ∨
      (coarseSite N z ∉ U ∧ ∃ t ∈ componentIn Uᶜ (coarseSite N z), ∃ u,
        coarseSite N u ∈ U ∧ (lattice d).Adj t (coarseSite N u) ∧ xap_Reach ω E x u ∧
          LeavesWindow N r ω u)
  have hstate : ∀ z, ReflTransGen (openBondGraph ω).Adj x z → T z := by
    intro z hz
    induction hz with
    | refl => exact Or.inl ⟨hxU, xap_reach_refl (hUE x hxU)⟩
    | @tail u v hxu huv ih =>
      have hlat : (lattice d).Adj u v := xap_lattice_of_open huv
      have hcoarse := coarseSite_eq_or_adj hN hlat
      by_cases hvU : coarseSite N v ∈ U
      · left
        refine ⟨hvU, ?_⟩
        rcases ih with ⟨huU, hxu'⟩ | ⟨huU, t, ht, w, hwU, htw, hxw, hlw⟩
        · exact xap_reach_trans hxu' (xap_reach_step (hUE u huU) (hUE v hvU) huv)
        · have hadj : (lattice d).Adj (coarseSite N u) (coarseSite N v) := by
            rcases hcoarse with h | h
            · exact (huU (h ▸ hvU)).elim
            · exact h
          have hucomp : coarseSite N u ∈ componentIn Uᶜ (coarseSite N u) :=
            ⟨huU, huU, SimpleGraph.Reachable.refl _⟩
          exact xap_reach_trans hxw
            (hconnect _ huU w v hwU hvU ⟨t, ht, htw⟩ ⟨_, hucomp, hadj⟩ hlw
              (hleave v (hxu.tail huv)))
      · right
        refine ⟨hvU, ?_⟩
        rcases ih with ⟨huU, hxu'⟩ | ⟨huU, t, ht, w, hwU, htw, hxw, hlw⟩
        · have hadj : (lattice d).Adj (coarseSite N v) (coarseSite N u) := by
            rcases hcoarse with h | h
            · exact (hvU (h ▸ huU)).elim
            · exact h.symm
          have hvcomp : coarseSite N v ∈ componentIn Uᶜ (coarseSite N v) :=
            ⟨hvU, hvU, SimpleGraph.Reachable.refl _⟩
          exact ⟨_, hvcomp, u, huU, hadj, hxu', hleave u hxu⟩
        · have hucomp : coarseSite N u ∈ componentIn Uᶜ (coarseSite N u) :=
            ⟨huU, huU, SimpleGraph.Reachable.refl _⟩
          have hvcomp : coarseSite N v ∈ componentIn Uᶜ (coarseSite N u) := by
            rcases hcoarse with h | h
            · rw [← h]
              exact hucomp
            · exact xmh_componentIn_step hucomp hvU h
          have heq := hcomp_eq hvcomp
          exact ⟨t, heq ▸ ht, w, hwU, htw, hxw, hlw⟩
  have hxy' : ReflTransGen (openBondGraph ω).Adj x y := by
    rw [← SimpleGraph.reachable_iff_reflTransGen]
    exact hxy
  exact ((hstate y hxy').resolve_right (fun h => h.1 hy)).2

end Exploding
