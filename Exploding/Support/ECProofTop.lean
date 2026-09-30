/-
The planar duality used in the Peierls estimate of Proposition 7.1: a finite set of
the square lattice containing the origin is enclosed by a `*`-connected chain of
boundary vertices running from the positive to the negative `x`-axis.
-/
import Exploding.Support.ECProofStar

namespace Exploding

open Relation

/-! ### Straight segments -/

/-- A horizontal segment of vertices satisfying `NA` is a nearest-neighbour chain. -/
theorem ec_hseg (NA : ℤ × ℤ → Prop) (y a : ℤ) :
    ∀ b : ℤ, a ≤ b → (∀ t, a ≤ t → t ≤ b → NA (t, y)) →
      ReflTransGen (fun u v => NA u ∧ NA v ∧ ec_adj4 u v) (a, y) (b, y) := by
  intro b hab
  induction b, hab using Int.leInduction with
  | base => intro _; exact ReflTransGen.refl
  | succ b hab ih =>
    intro h
    refine (ih fun t h1 h2 => h t h1 (by omega)).tail ⟨h b hab (by omega),
      h (b + 1) (by omega) le_rfl, ?_⟩
    unfold ec_adj4
    simp

/-- A vertical segment of vertices satisfying `NA` is a nearest-neighbour chain. -/
theorem ec_vseg (NA : ℤ × ℤ → Prop) (x a : ℤ) :
    ∀ b : ℤ, a ≤ b → (∀ t, a ≤ t → t ≤ b → NA (x, t)) →
      ReflTransGen (fun u v => NA u ∧ NA v ∧ ec_adj4 u v) (x, a) (x, b) := by
  intro b hab
  induction b, hab using Int.leInduction with
  | base => intro _; exact ReflTransGen.refl
  | succ b hab ih =>
    intro h
    refine (ih fun t h1 h2 => h t h1 (by omega)).tail ⟨h b hab (by omega),
      h (b + 1) (by omega) le_rfl, ?_⟩
    unfold ec_adj4
    simp

theorem ec_seg_symm (NA : ℤ × ℤ → Prop) :
    ∀ a b, ReflTransGen (fun u v => NA u ∧ NA v ∧ ec_adj4 u v) a b →
      ReflTransGen (fun u v => NA u ∧ NA v ∧ ec_adj4 u v) b a :=
  fun _ _ h => ec_rtg_symm (fun _ _ huv => ⟨huv.2.1, huv.1, ec_adj4_symm huv.2.2⟩) h

/-! ### The king-move graph on a boundary -/

/-- The simple graph of king moves between vertices of a set `D`. -/
def ec_starGraph (D : ℤ × ℤ → Prop) : SimpleGraph (ℤ × ℤ) where
  Adj a b := D a ∧ D b ∧ ec_adj8 a b
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, ec_adj8_symm h.2.2⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

theorem ec_starGraph_adj (D : ℤ × ℤ → Prop) (a b : ℤ × ℤ) :
    (ec_starGraph D).Adj a b ↔ D a ∧ D b ∧ ec_adj8 a b := Iff.rfl

theorem ec_starGraph_support_mem (D : ℤ × ℤ → Prop) {u v : ℤ × ℤ}
    (w : (ec_starGraph D).Walk u v) (hu : D u) : ∀ z ∈ w.support, D z := by
  induction w with
  | nil => intro z hz; simp at hz; subst hz; exact hu
  | cons h w ih =>
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih ((ec_starGraph_adj D _ _).1 h).2.1 z hz

theorem ec_starGraph_length (D : ℤ × ℤ → Prop) {u v : ℤ × ℤ}
    (w : (ec_starGraph D).Walk u v) : |u.1 - v.1| ≤ (w.length : ℤ) := by
  induction w with
  | nil => simp
  | @cons a b c h w ih =>
    rw [SimpleGraph.Walk.length_cons]
    have h1 : |a.1 - b.1| ≤ 1 := ((ec_starGraph_adj D _ _).1 h).2.2.2.1
    have h2 : |a.1 - c.1| ≤ |a.1 - b.1| + |b.1 - c.1| := by
      have := abs_add_le (a.1 - b.1) (b.1 - c.1)
      rwa [sub_add_sub_cancel] at this
    push_cast
    linarith

/-- **Planar duality.**  A finite set `F ∋ 0` of the square lattice has a `*`-connected
chain of pairwise distinct vertices outside `F`, each adjacent to `F`, starting at a
point `(j + 1, 0)` of the positive `x`-axis and of length at least `j + 3`. -/
theorem ec_top (F : Set (ℤ × ℤ)) (hF : F.Finite) (h0 : ((0 : ℤ), (0 : ℤ)) ∈ F) :
    ∃ j : ℕ, ∃ l : List (ℤ × ℤ), l.Nodup ∧ List.IsChain ec_adj8 l ∧
      l.head? = some ((j : ℤ) + 1, 0) ∧ j + 3 ≤ l.length ∧
      ∀ z ∈ l, z ∉ F ∧ ∃ a ∈ F, ec_adj4 a z := by
  classical
  -- the component `A` of the origin in `F`
  set RF : ℤ × ℤ → ℤ × ℤ → Prop := fun a b => a ∈ F ∧ b ∈ F ∧ ec_adj4 a b with hRF
  set A : Set (ℤ × ℤ) := {a | ReflTransGen RF (0, 0) a} with hAdef
  have h0A : ((0 : ℤ), (0 : ℤ)) ∈ A := ReflTransGen.refl
  have hAF : ∀ a ∈ A, a ∈ F := by
    intro a ha
    rcases ReflTransGen.cases_tail ha with h | ⟨b, _, hba⟩
    · rw [h]; exact h0
    · exact hba.2.1
  have hAfin : A.Finite := hF.subset hAF
  have hAconn0 : ∀ u ∈ A, ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ ec_adj4 a b) (0, 0) u := by
    intro u hu
    have key : ∀ u, ReflTransGen RF (0, 0) u →
        ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ ec_adj4 a b) (0, 0) u := by
      intro u h
      induction h with
      | refl => exact ReflTransGen.refl
      | tail hb hbc ih => exact ih.tail ⟨hb, hb.tail hbc, hbc.2.2⟩
    exact key u hu
  have hA : ∀ u ∈ A, ∀ v ∈ A,
      ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ ec_adj4 a b) u v := by
    intro u hu v hv
    exact (ec_rtg_symm (fun _ _ h => ⟨h.2.1, h.1, ec_adj4_symm h.2.2⟩) (hAconn0 u hu)).trans
      (hAconn0 v hv)
  have hnotF : ∀ z, z ∉ A → (∃ a ∈ A, ec_adj4 a z) → z ∉ F := by
    intro z hz ⟨a, ha, hadj⟩ hzF
    exact hz (ha.tail ⟨hAF a ha, hzF, hadj⟩)
  -- a box containing `A`
  obtain ⟨Q, hQ⟩ := (hAfin.image (fun a : ℤ × ℤ => |a.1| + |a.2|)).bddAbove
  have hQ' : ∀ a ∈ A, |a.1| ≤ Q ∧ |a.2| ≤ Q := by
    intro a ha
    have := hQ ⟨a, ha, rfl⟩
    simp only at this
    constructor <;> linarith [abs_nonneg a.1, abs_nonneg a.2]
  have hQ0 : 0 ≤ Q := by
    have := (hQ' _ h0A).1
    simp at this
    exact this
  -- the extreme points of `A` on the `x`-axis
  obtain ⟨jmax, hjmax, hjmax'⟩ := Int.exists_greatest_of_bdd
    (P := fun j => ((j, (0 : ℤ)) ∈ A)) ⟨Q, fun z hz => by
      have := (hQ' _ hz).1; simp at this; exact (le_abs_self z).trans this⟩ ⟨0, h0A⟩
  obtain ⟨jmin, hjmin, hjmin'⟩ := Int.exists_least_of_bdd
    (P := fun j => ((j, (0 : ℤ)) ∈ A)) ⟨-Q, fun z hz => by
      have := (hQ' _ hz).1; simp at this; exact (neg_le_abs z).trans this |> fun h => by linarith⟩
      ⟨0, h0A⟩
  have hjmax0 : 0 ≤ jmax := hjmax' 0 h0A
  have hjmin0 : jmin ≤ 0 := hjmin' 0 h0A
  have hjmaxQ : jmax ≤ Q := by
    have := (hQ' _ hjmax).1; simp at this; exact (le_abs_self _).trans this
  have hjminQ : -Q ≤ jmin := by
    have := (hQ' _ hjmin).1; simp at this; linarith [neg_abs_le jmin]
  set p : ℤ × ℤ := (jmax + 1, 0) with hp
  set q : ℤ × ℤ := (jmin - 1, 0) with hq
  have hpA : p ∉ A := fun h => by have := hjmax' _ h; simp at this
  have hqA : q ∉ A := fun h => by have := hjmin' _ h; simp at this
  -- the component `B` of `p` in the complement of `A`
  set BR : ℤ × ℤ → ℤ × ℤ → Prop := fun a b => a ∉ A ∧ b ∉ A ∧ ec_adj4 a b with hBR
  set B : Set (ℤ × ℤ) := {z | ReflTransGen BR p z} with hBdef
  have hpB : p ∈ B := ReflTransGen.refl
  have hBnA : ∀ z ∈ B, z ∉ A := by
    intro z hz
    rcases ReflTransGen.cases_tail hz with h | ⟨b, _, hbz⟩
    · rw [h]; exact hpA
    · exact hbz.2.1
  have hBconn0 : ∀ u ∈ B, ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ ec_adj4 a b) p u := by
    intro u hu
    have key : ∀ u, ReflTransGen BR p u →
        ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ ec_adj4 a b) p u := by
      intro u h
      induction h with
      | refl => exact ReflTransGen.refl
      | tail hb hbc ih => exact ih.tail ⟨hb, hb.tail hbc, hbc.2.2⟩
    exact key u hu
  have hB : ∀ u ∈ B, ∀ v ∈ B, ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ ec_adj4 a b) u v := by
    intro u hu v hv
    exact (ec_rtg_symm (fun _ _ h => ⟨h.2.1, h.1, ec_adj4_symm h.2.2⟩) (hBconn0 u hu)).trans
      (hBconn0 v hv)
  have hclose : ∀ b ∈ B, ∀ z, ec_adj4 b z → z ∉ A → z ∈ B :=
    fun b hb z hbz hz => hb.tail ⟨hBnA b hb, hz, hbz⟩
  have hdisj : ∀ z, z ∈ A → z ∈ B → False := fun z hz hzB => hBnA z hzB hz
  -- the far point `q` lies in `B`
  have hqB : q ∈ B := by
    set m : ℤ := Q + 1 with hm
    have NA : ∀ t : ℤ × ℤ, (t ∈ A → False) → t ∉ A := fun t h => h
    have s1 := ec_hseg (fun z => z ∉ A) 0 (jmax + 1) m (by omega) (fun t h1 h2 hmem => by
      have := hjmax' t hmem; omega)
    have s2 := ec_vseg (fun z => z ∉ A) m 0 m (by omega) (fun t h1 h2 hmem => by
      have := (hQ' _ hmem).1; simp only at this
      rw [abs_of_nonneg (by omega)] at this; omega)
    have s3 := ec_seg_symm (fun z => z ∉ A) _ _ (ec_hseg (fun z => z ∉ A) m (-m) m (by omega)
      (fun t h1 h2 hmem => by
        have := (hQ' _ hmem).2; simp only at this
        rw [abs_of_nonneg (by omega)] at this; omega))
    have s4 := ec_seg_symm (fun z => z ∉ A) _ _ (ec_vseg (fun z => z ∉ A) (-m) 0 m (by omega)
      (fun t h1 h2 hmem => by
        have := (hQ' _ hmem).1; simp only at this
        rw [abs_of_nonpos (by omega)] at this; omega))
    have s5 := ec_hseg (fun z => z ∉ A) 0 (-m) (jmin - 1) (by omega) (fun t h1 h2 hmem => by
      have := hjmin' t hmem; omega)
    exact (s1.trans (s2.trans (s3.trans (s4.trans s5))))
  -- the boundary chain
  have hpd : p ∈ B ∧ ∃ c ∈ A, ec_adj4 c p := ⟨hpB, (jmax, 0), hjmax, by unfold ec_adj4; simp [hp]⟩
  have hqd : q ∈ B ∧ ∃ c ∈ A, ec_adj4 c q := ⟨hqB, (jmin, 0), hjmin, by unfold ec_adj4; simp [hq]⟩
  have hstar := ec_star_conn A B hA hB hdisj hclose p q hpd hqd
  set D : ℤ × ℤ → Prop := fun a => a ∈ B ∧ ∃ c ∈ A, ec_adj4 c a with hD
  have hreach : (ec_starGraph D).Reachable p q :=
    (SimpleGraph.reachable_iff_reflTransGen p q).2 hstar
  obtain ⟨w, hw⟩ := hreach.exists_isPath
  have hlen := ec_starGraph_length D w
  have hsupp := ec_starGraph_support_mem D w hpd
  refine ⟨jmax.toNat, w.support, hw.support_nodup, ?_, ?_, ?_, ?_⟩
  · exact (w.isChain_adj_support).imp fun a b h => h.2.2
  · have h := SimpleGraph.Walk.cons_tail_support w
    have h2 : w.support.head? = some p := by
      conv_lhs => rw [← h]
      rfl
    rw [h2, hp, Int.toNat_of_nonneg hjmax0]
  · rw [SimpleGraph.Walk.length_support]
    have e : (jmax.toNat : ℤ) = jmax := Int.toNat_of_nonneg hjmax0
    have h1 : |p.1 - q.1| = jmax - jmin + 2 := by
      simp only [hp, hq]
      rw [abs_of_nonneg (by omega)]
      ring
    rw [h1] at hlen
    omega
  · intro z hz
    obtain ⟨hzB, c, hc, hadj⟩ := hsupp z hz
    exact ⟨hnotF z (hBnA z hzB) ⟨c, hc, hadj⟩, c, hAF c hc, hadj⟩

end Exploding
