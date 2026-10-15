import Exploding.Support.ArxivMaximalGoodCluster

/-!
# Attaching good-cluster endpoints to a core

Finite complementary components let a path from a maximal good component reach the
selected connected core after at most the size of the starting hole plus one steps.
The paper-local result uses the actual good-site and hole-property carriers.
-/

open Exploding LatticeProb

namespace Exploding

/-- A walk ending in `S` has a prefix ending at its first vertex in `S`. -/
private theorem arxiv_first_hit_walk {d : ℕ} {S G : Set (Site d)} {u v : G}
    (p : ((lattice d).induce G).Walk u v) (hp : p.IsPath)
    (hv : (v : Site d) ∈ S) :
    ∃ a : Site d, ∃ _ha : a ∈ S, ∃ haG : a ∈ G,
      ∃ q : ((lattice d).induce G).Walk u ⟨a, haG⟩, q.IsPath ∧
        ∀ x ∈ q.support, (x : Site d) ≠ a → (x : Site d) ∉ S := by
  classical
  let hits : G → Bool := fun x => decide ((x : Site d) ∈ S)
  have hsome : (p.support.find? hits).isSome := by
    rw [List.find?_isSome]
    exact ⟨v, p.end_mem_support, by simp [hits, hv]⟩
  let aG : G := (p.support.find? hits).get hsome
  have hfind : p.support.find? hits = some aG := by simp [aG]
  have hfind' := List.find?_eq_some_iff_append.mp hfind
  rcases hfind' with ⟨haHit, before, after, hsplit, hbefore⟩
  have ha : (aG : Site d) ∈ S := by simpa [hits] using haHit
  have haG : (aG : Site d) ∈ G := aG.property
  have hmem : aG ∈ p.support := List.mem_of_find?_eq_some hfind
  let q := p.takeUntil aG hmem
  have hqPath : q.IsPath := by
    exact hp.takeUntil hmem
  have hprefix : q.support <+: p.support := by
    exact p.support_takeUntil_prefix_support hmem
  have haBefore : aG ∉ before := by
    intro h
    have hfalse : False := by simpa [hits, ha] using hbefore aG h
    exact hfalse.elim
  have hidxA : p.support.idxOf aG = before.length := by
    rw [hsplit, List.idxOf_append_of_notMem haBefore]
    simp
  refine ⟨aG, ha, haG, q, hqPath, ?_⟩
  intro x hx hxa
  have hxP : x ∈ p.support := hprefix.subset hx
  have haIdxQ : q.support.idxOf aG = q.length := by
    simpa only [SimpleGraph.Walk.support_getElem_length] using
      hqPath.support_nodup.idxOf_getElem q.length
        (by simp [SimpleGraph.Walk.length_support])
  have haIdxP : p.support.idxOf aG = q.length := by
    exact (hprefix.idxOf_eq_of_mem q.end_mem_support).symm.trans haIdxQ
  have hxIdxNe : q.support.idxOf x ≠ q.support.idxOf aG := by
    intro heq
    have hEq := (List.idxOf_inj hx).mp heq
    exact hxa (congrArg Subtype.val hEq)
  have hxIdxLtQ : q.support.idxOf x < q.length := by
    have hlt : q.support.idxOf x < q.support.length :=
    List.idxOf_lt_length_of_mem hx
    rw [SimpleGraph.Walk.length_support] at hlt
    rw [haIdxQ] at hxIdxNe
    omega
  have hxIdxLtA : p.support.idxOf x < p.support.idxOf aG := by
    rw [← hprefix.idxOf_eq_of_mem hx, haIdxP]
    exact hxIdxLtQ
  have hxBefore : x ∈ before := by
    have hxSplit : x ∈ before ++ aG :: after := hsplit ▸ hxP
    rcases List.mem_append.mp hxSplit with hxb | hxa'
    · exact hxb
    · rcases List.mem_cons.mp hxa' with hxa' | hxa'
      · have hfalse : False := hxa (congrArg Subtype.val hxa')
        exact hfalse.elim
      · by_cases hxBefore : x ∈ before
        · exact hxBefore
        · have hidxLower : before.length ≤ p.support.idxOf x := by
            rw [hsplit, List.idxOf_append_of_notMem hxBefore]
            omega
          have hidxUpper : p.support.idxOf x < before.length := by
            simpa [hidxA] using hxIdxLtA
          omega
  have hxNoHit := hbefore x hxBefore
  simpa [hits] using hxNoHit

/-- A simple path with all nonterminal vertices outside `S` keeps those vertices
in the complementary component of its starting point. -/
private theorem arxiv_path_vertices_in_hole_component {d : ℕ} {S : Set (Site d)}
    {b u v : Site d} (p : (lattice d).Walk u v) (hp : p.IsPath)
    (hbase : u ∈ componentIn Sᶜ b)
    (houtside : ∀ x ∈ p.support, x ≠ v → x ∉ S) :
    ∀ x ∈ p.support, x ≠ v → x ∈ componentIn Sᶜ b := by
  induction p with
  | nil =>
      intro x hx hne
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact (hne rfl).elim
  | @cons u v w hadj p ih =>
      have htailPath : p.IsPath :=
        (SimpleGraph.Walk.cons_isPath_iff hadj p).mp hp |>.1
      intro x hx hxw
      have hx' : x = u ∨ x ∈ p.support := by
        simpa [SimpleGraph.Walk.support_cons] using hx
      rcases hx' with hxu | hxTail
      · subst x
        exact hbase
      · by_cases hvw : v = w
        · subst w
          have hpNil : p.Nil := (SimpleGraph.Walk.isPath_iff_nil).mp htailPath
          cases hpNil
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hxTail
          subst x
          exact (hxw rfl).elim
        · have hvWhole : v ∈ (SimpleGraph.Walk.cons hadj p).support := by
            simp [SimpleGraph.Walk.support_cons]
          have hvNotS : v ∉ S := houtside v hvWhole hvw
          rcases hbase with ⟨hb, huNotS, hbu⟩
          have hvNot : v ∈ Sᶜ := by simpa using hvNotS
          have huNot : u ∈ Sᶜ := huNotS
          have hadjHole : ((lattice d).induce Sᶜ).Adj
              ⟨u, huNot⟩ ⟨v, hvNot⟩ := by simpa using hadj
          have huvHole : ((lattice d).induce Sᶜ).Reachable
              ⟨u, huNot⟩ ⟨v, hvNot⟩ := SimpleGraph.Adj.reachable hadjHole
          have hvBase : v ∈ componentIn Sᶜ b :=
            ⟨hb, hvNot, hbu.trans huvHole⟩
          have houtsideTail : ∀ y ∈ p.support, y ≠ w → y ∉ S := by
            intro y hy hyw
            exact houtside y (by simp [SimpleGraph.Walk.support_cons, hy]) hyw
          exact ih htailPath hvBase houtsideTail x hxTail hxw

/-- A walk inside `S` lifts to its component when both endpoints belong to it. -/
private theorem arxiv_lift_walk_to_component {d : ℕ} {S : Set (Site d)}
    {z : Site d} {u v : S} (p : ((lattice d).induce S).Walk u v)
    (hu : (u : Site d) ∈ componentIn S z) (hv : (v : Site d) ∈ componentIn S z) :
    ∃ q : ((lattice d).induce (componentIn S z)).Walk ⟨u, hu⟩ ⟨v, hv⟩,
      q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons u v w hadj p ih =>
      have hvComp : (v : Site d) ∈ componentIn S z := by
        rcases hu with ⟨hzS, huS, hzu⟩
        have huv : ((lattice d).induce S).Reachable u v :=
          SimpleGraph.Adj.reachable hadj
        exact ⟨hzS, v.property, hzu.trans huv⟩
      obtain ⟨q, hqLength⟩ := ih hvComp hv
      have hadjComp : ((lattice d).induce (componentIn S z)).Adj
          ⟨u, hu⟩ ⟨v, hvComp⟩ := by
        simpa using hadj
      refine ⟨SimpleGraph.Walk.cons hadjComp q, ?_⟩
      simp [hqLength]

/-- A finite-hole set inside `G` can be reached from every vertex in its `G`-component.
The walk is contained in that component and its length is bounded by the starting hole size
plus one. -/
theorem arxiv_core_attachment_of_finite_holes {d : ℕ} {S G : Set (Site d)}
    (hSG : S ⊆ G) (hholes : ∀ x, x ∉ S → (componentIn Sᶜ x).Finite)
    (z : Site d) (hz : z ∈ S) (u : Site d) (hu : u ∈ componentIn G z) :
    ∃ a : Site d, ∃ _ha : a ∈ S, ∃ haComp : a ∈ componentIn G z,
      ∃ p : ((lattice d).induce (componentIn G z)).Walk ⟨u, hu⟩ ⟨a, haComp⟩,
        p.length ≤ (componentIn Sᶜ u).ncard + 1 := by
  classical
  by_cases huS : u ∈ S
  · refine ⟨u, huS, hu, SimpleGraph.Walk.nil, ?_⟩
    simp
  · have hzG : z ∈ G := hSG hz
    obtain ⟨_, huG, hzu₀⟩ := hu
    have hzu : ((lattice d).induce G).Reachable ⟨z, hzG⟩ ⟨u, huG⟩ := by
      simpa using hzu₀
    have hHoleFin : (componentIn Sᶜ u).Finite := hholes u huS
    obtain ⟨w⟩ := hzu.symm
    let w' := w.bypass
    have hw'Path : w'.IsPath := by simpa [w'] using w.bypass_isPath
    obtain ⟨a, ha, haG, q, hqPath, hqoutside⟩ :=
      arxiv_first_hit_walk w' hw'Path hz
    let q' := q
    have hqOutside : ∀ x ∈ q'.support, (x : Site d) ≠ a → (x : Site d) ∉ S := by
      intro x hx hxa
      exact hqoutside x hx hxa
    let emb : ((lattice d).induce G).Embedding (lattice d) :=
      SimpleGraph.Embedding.induce G
    let qBase : (lattice d).Walk u a := by
      simpa [emb] using q'.map emb.toHom
    have hmapInj : Function.Injective emb.toHom := emb.injective
    have hqBasePath : qBase.IsPath := by
      exact (SimpleGraph.Walk.isPath_map_iff_of_injective hmapInj).2 hqPath
    have hqBaseOutside : ∀ x ∈ qBase.support, x ≠ a → x ∉ S := by
      intro x hx hxa
      change x ∈ (q'.map emb.toHom).support at hx
      rw [SimpleGraph.Walk.support_map] at hx
      simp only [List.mem_map] at hx
      rcases hx with ⟨y, hy, rfl⟩
      exact hqOutside y hy hxa
    have huHole : u ∈ Sᶜ := by simpa using huS
    have hbase : u ∈ componentIn Sᶜ u :=
      ⟨huHole, huHole, SimpleGraph.Reachable.refl _⟩
    have hqComp : ∀ x ∈ qBase.support, x ≠ a → x ∈ componentIn Sᶜ u :=
      arxiv_path_vertices_in_hole_component qBase hqBasePath hbase hqBaseOutside
    let supportSites := qBase.support
    have hsupportNodup : supportSites.Nodup := hqBasePath.support_nodup
    have hsupportCard : supportSites.toFinset.card = qBase.length + 1 := by
      rw [List.toFinset_card_of_nodup hsupportNodup]
      simp [supportSites, qBase, SimpleGraph.Walk.length_support]
    have hsupportSubset : (supportSites.toFinset : Set (Site d)) ⊆
        componentIn Sᶜ u ∪ {a} := by
      intro x hx
      have hx' : x ∈ supportSites := List.mem_toFinset.mp hx
      by_cases hxa : x = a
      · exact Set.mem_union_right _ (Set.mem_singleton_iff.mpr hxa)
      · exact Set.mem_union_left _ (hqComp x hx' hxa)
    have hsupportFinite : (componentIn Sᶜ u ∪ {a}).Finite :=
      hHoleFin.union (Set.finite_singleton a)
    have hlengthBound : qBase.length + 1 ≤ (componentIn Sᶜ u ∪ {a}).ncard := by
      calc
        qBase.length + 1 = supportSites.toFinset.card := hsupportCard.symm
        _ = (supportSites.toFinset : Set (Site d)).ncard :=
          (Set.ncard_coe_finset _).symm
        _ ≤ (componentIn Sᶜ u ∪ {a}).ncard :=
          Set.ncard_le_ncard hsupportSubset hsupportFinite
    have hlengthBound' : qBase.length ≤ (componentIn Sᶜ u).ncard + 1 := by
      calc
        qBase.length ≤ qBase.length + 1 := Nat.le_succ _
        _ ≤ (componentIn Sᶜ u ∪ {a}).ncard := hlengthBound
        _ ≤ (componentIn Sᶜ u).ncard + 1 := by
          rw [Set.union_singleton]
          exact Set.ncard_insert_le a (componentIn Sᶜ u)
    have hStartComp : u ∈ componentIn G z := ⟨hzG, huG, hzu⟩
    have haComp : a ∈ componentIn G z := by
      refine ⟨hzG, haG, hzu.trans ?_⟩
      exact ⟨q'⟩
    obtain ⟨p, hpLength⟩ :=
      arxiv_lift_walk_to_component q' hStartComp haComp
    have hqBaseLength : qBase.length = q'.length := by
      change (q'.map emb.toHom).length = q'.length
      cases q' <;> simp [SimpleGraph.Walk.map]
    exact ⟨a, ha, haComp, p, by rw [hpLength, ← hqBaseLength]; exact hlengthBound'⟩

/-- Every point in the maximal good-site component can reach the selected core with a
walk whose length is bounded by its finite complementary hole plus one. -/
theorem arxiv_core_attachment {d : ℕ} (η : Site d → ℤ) (k : ℕ)
    {C : Set (Site d)} (hC : IsInfiniteConnectedGoodSet η k C)
    (hholes : RnHoleProp d C) (z : Site d) (hz : z ∈ C)
    (u : Site d) (hu : u ∈ componentIn (goodSites η k) z) :
    ∃ a : Site d, ∃ _ha : a ∈ C,
      ∃ haComp : a ∈ componentIn (goodSites η k) z,
        ∃ p : ((lattice d).induce (componentIn (goodSites η k) z)).Walk
            ⟨u, hu⟩ ⟨a, haComp⟩,
          p.length ≤ (componentIn Cᶜ u).ncard + 1 := by
  have hCgood : C ⊆ goodSites η k := hC.2.1
  have hfinite : ∀ x, x ∉ C → (componentIn Cᶜ x).Finite := by
    intro x hx
    obtain ⟨n₀, hn₀⟩ := hholes
    let n : ℕ := max n₀ (mnorm x).toNat
    have hn₀n : n₀ ≤ n := Nat.le_max_left _ _
    have hxcent : x ∈ (cent d n : Set (Site d)) := by
      intro i
      have hcoord : |x i| ≤ mnorm x := by
        unfold mnorm
        exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
      have hnorm : 0 ≤ mnorm x := by
        unfold mnorm
        exact Finset.sum_nonneg fun j _ => abs_nonneg (x j)
      have hcast : ((mnorm x).toNat : ℤ) = mnorm x := Int.toNat_of_nonneg hnorm
      have hncoord : (mnorm x).toNat ≤ n := Nat.le_max_right _ _
      omega
    exact (hn₀ n hn₀n x hxcent hx).1
  exact arxiv_core_attachment_of_finite_holes hCgood hfinite z hz u hu

end Exploding
