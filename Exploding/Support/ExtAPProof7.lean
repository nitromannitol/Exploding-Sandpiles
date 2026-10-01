/-
The covering-walk lemma: a finite connected graph on `n` vertices has a closed
walk from any root visiting every vertex, of length at most `2n` (depth-first
traversal of a spanning tree).  Applied to the king graph on a finite
`*`-connected set, it turns the star-walk count into the `(3^d)^{2s}` count of
`*`-connected sets of size `s`, which feeds the finite-cluster case of the Peierls
estimate.
-/
import Exploding.Support.ExtAPProof6
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Exploding LatticeProb MeasureTheory
open scoped Classical

universe u

namespace Exploding

/-- **Covering walk.**  A finite connected graph has a closed walk from any root
visiting every vertex, of length at most twice the vertex count. -/
theorem xap7_gen_closed_walk : ∀ (n : ℕ) (V : Type u) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V), Fintype.card V = n → G.Connected →
    ∃ p : G.Walk r r, p.support.toFinset = Finset.univ ∧ p.length ≤ 2 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V instF instD G r hcard hconn
    letI := instF
    letI := instD
    by_cases h1 : n ≤ 1
    · have hc : Fintype.card V = 1 := by
        have := Fintype.card_pos_iff.mpr ⟨r⟩
        omega
      obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hc
      have hall : ∀ w : V, w = r := by intro w; rw [hx w, hx r]
      refine ⟨SimpleGraph.Walk.nil, ?_, ?_⟩
      · rw [SimpleGraph.Walk.support_nil]
        ext w; simp [hall w]
      · simp
    · push Not at h1
      have hlt : 1 < Fintype.card V := by omega
      haveI : Nontrivial V := ⟨Fintype.one_lt_card_iff.mp hlt⟩
      obtain ⟨v, hv⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
      have hcard' : Fintype.card ↥(({v}ᶜ : Set V)) = n - 1 := by
        rw [Fintype.card_compl_set (s := ({v} : Set V)), hcard]
        have hsing : Fintype.card ↥(({v} : Set V)) = 1 :=
          Fintype.card_eq_one_iff.mpr
            ⟨⟨v, Set.mem_singleton v⟩, fun x => Subtype.ext (Set.mem_singleton_iff.mp x.prop)⟩
        rw [hsing]
      have hlt' : Fintype.card ↥(({v}ᶜ : Set V)) < n := by omega
      haveI : Nonempty ↥(({v}ᶜ : Set V)) := by
        rw [← Fintype.card_pos_iff]; omega
      let r' : ↥(({v}ᶜ : Set V)) := Classical.arbitrary _
      obtain ⟨q, hqsup, hqlen⟩ :=
        ih (Fintype.card ↥(({v}ᶜ : Set V))) hlt' ↥(({v}ᶜ : Set V))
          (G.induce ({v}ᶜ)) r' rfl hv
      let φ : (G.induce ({v}ᶜ : Set V)) →g G := ⟨Subtype.val, fun h => h⟩
      have hqsup' : (q.map φ).support.toFinset = (Finset.univ : Finset V).erase v := by
        rw [SimpleGraph.Walk.support_map]
        apply Finset.ext
        intro w
        rw [List.mem_toFinset, List.mem_map, Finset.mem_erase]
        constructor
        · rintro ⟨x, -, rfl⟩
          exact ⟨x.prop, Finset.mem_univ _⟩
        · intro hw
          refine ⟨⟨w, hw.1⟩, ?_, rfl⟩
          rw [← List.mem_toFinset, hqsup]; exact Finset.mem_univ _
      have hex : ∃ u, u ≠ v ∧ G.Adj v u := by
        obtain ⟨w, hw⟩ : ∃ w : V, w ≠ v := by
          by_contra hcon
          push Not at hcon
          have hcv : Fintype.card V = 1 := Fintype.card_eq_one_iff.mpr ⟨v, fun w => hcon w⟩
          omega
        obtain ⟨p⟩ := hconn v w
        cases p with
        | nil => exact absurd rfl hw
        | cons h p' => exact ⟨_, h.ne.symm, h⟩
      obtain ⟨u, huv_ne, huv⟩ := hex
      have hu_mem : u ∈ (q.map φ).support := by
        rw [← List.mem_toFinset, hqsup']
        exact Finset.mem_erase.mpr ⟨huv_ne, Finset.mem_univ _⟩
      let q2 : G.Walk u u := ((q.map φ).rotate u hu_mem).append
        (SimpleGraph.Walk.cons huv.symm (SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil))
      have hq2len : q2.length ≤ 2 * n := by
        have h1 : q2.length = ((q.map φ).rotate u hu_mem).length + 2 := by
          simp [q2, SimpleGraph.Walk.length_append]
        rw [h1, SimpleGraph.Walk.length_rotate, SimpleGraph.Walk.length_map]
        omega
      have hq2sup : (q2.support.toFinset : Finset V) = Finset.univ := by
        rw [Finset.eq_univ_iff_forall]
        intro w
        rw [List.mem_toFinset]
        have hsplit : q2.support
            = ((q.map φ).rotate u hu_mem).support
              ++ (SimpleGraph.Walk.cons huv.symm
                  (SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil)).support.tail :=
          SimpleGraph.Walk.support_append ..
        rw [hsplit]
        by_cases hwv : w = v
        · subst hwv
          exact List.mem_append_right _ (by simp)
        · refine List.mem_append_left _ ?_
          rw [SimpleGraph.Walk.mem_support_rotate_iff, SimpleGraph.Walk.support_map]
          exact List.mem_map.mpr ⟨⟨w, hwv⟩, by
            rw [← List.mem_toFinset, hqsup]; exact Finset.mem_univ _, rfl⟩
      have hr_mem : r ∈ q2.support := by
        have : r ∈ q2.support.toFinset := by rw [hq2sup]; exact Finset.mem_univ r
        exact List.mem_toFinset.mp this
      refine ⟨q2.rotate r hr_mem, ?_, ?_⟩
      · apply Finset.ext
        intro w
        rw [List.mem_toFinset, SimpleGraph.Walk.mem_support_rotate_iff,
          ← List.mem_toFinset, hq2sup]
      · rw [SimpleGraph.Walk.length_rotate]
        exact hq2len

variable {d : ℕ}

/-- The king-graph version: a finite `*`-connected set through the origin is the
support of a closed star-walk from the origin of length at most twice its size. -/
theorem xap7_coveringWalk (S : Finset (Site d)) (h0 : (0 : Site d) ∈ S)
    (hconn : ((xap2_kingGraph d).induce (↑S : Set (Site d))).Connected) :
    ∃ p : (xap2_kingGraph d).Walk (0 : Site d) (0 : Site d),
      p.support.toFinset = S ∧ p.length ≤ 2 * S.card := by
  obtain ⟨q, hqsup, hqlen⟩ := xap7_gen_closed_walk (Fintype.card ↥S) ↥S
    ((xap2_kingGraph d).induce (↑S)) ⟨0, h0⟩ rfl hconn
  rw [Fintype.card_coe] at hqlen
  refine ⟨q.map ⟨Subtype.val, fun h => h⟩, ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_map]
    apply Finset.ext
    intro x
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨a, -, rfl⟩; exact a.prop
    · intro hx
      exact ⟨⟨x, hx⟩, by rw [← List.mem_toFinset, hqsup]; exact Finset.mem_univ _, rfl⟩
  · rw [SimpleGraph.Walk.length_map]; exact hqlen

end Exploding
