/-
Infrastructure for the `(3^d)^{2s}` count of finite `*`-connected sets through the
origin, from the closed star-walk cover of `ExtAPProof7`: each such set is the
support of a closed star-walk of length at most `2s`, and a closed star-walk is
determined by its star-step direction sequence, of which there are at most
`(3^d)^{2s}`.  The direction code and its injectivity are set up here; the count
feeds `xap6_biUnion_bad_prob_le` for the finite-cluster case of the Peierls
estimate.
-/
import Exploding.Support.ExtAPProof7

open Exploding LatticeProb MeasureTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- The star-step directions of the origin, as a type. -/
abbrev xap8_Dir (d : ℕ) := ↥(xap5_dirFinset d)

/-- The direction of a star-step. -/
noncomputable def xap8_stepDir {a b : Site d} (h : (xap2_kingGraph d).Adj a b) :
    xap8_Dir d :=
  ⟨b - a, by
    rw [xap5_mem_dirFinset]
    refine ⟨?_, fun i => ?_⟩
    · intro hba
      exact h.1 (sub_eq_zero.mp hba.symm).symm
    · simpa [Pi.sub_apply, abs_sub_comm] using h.2 i⟩

/-- The direction sequence of a closed star-walk. -/
noncomputable def xap8_code (p : (xap2_kingGraph d).Walk (0 : Site d) (0 : Site d)) :
    Fin p.length → xap8_Dir d :=
  fun i => xap8_stepDir (p.adj_getVert_succ i.isLt)

theorem xap8_stepDir_val {a b : Site d} (h : (xap2_kingGraph d).Adj a b) :
    (xap8_stepDir h).val = b - a := rfl

/-- Each vertex is the previous vertex plus the step direction. -/
theorem xap8_getVert_succ (p : (xap2_kingGraph d).Walk (0 : Site d) (0 : Site d))
    (i : Fin p.length) :
    p.getVert (i.val + 1) = p.getVert i.val + (xap8_code p i).val := by
  rw [xap8_code, xap8_stepDir_val]
  abel

/-- Two closed star-walks with the same length and the same direction sequence
have the same vertices. -/
theorem xap8_getVert_eq {p q : (xap2_kingGraph d).Walk (0 : Site d) (0 : Site d)}
    (hlen : p.length = q.length)
    (hcode : ∀ (i : Fin p.length), xap8_code p i = xap8_code q ⟨i.val, by omega⟩) :
    ∀ i : ℕ, i ≤ p.length → p.getVert i = q.getVert i := by
  intro i
  induction i with
  | zero => intro _; rw [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_zero]
  | succ i ih =>
      intro hi
      rw [xap8_getVert_succ p ⟨i, by omega⟩, xap8_getVert_succ q ⟨i, by omega⟩,
        ih (by omega), hcode ⟨i, by omega⟩]

/-- Two closed star-walks with the same length and direction sequence have the
same support, hence their covering sets are equal. -/
theorem xap8_support_eq_of_code {p q : (xap2_kingGraph d).Walk (0 : Site d) (0 : Site d)}
    (hlen : p.length = q.length)
    (hcode : ∀ (i : Fin p.length), xap8_code p i = xap8_code q ⟨i.val, by omega⟩) :
    p.support.toFinset = q.support.toFinset := by
  have hv := xap8_getVert_eq hlen hcode
  have hlist : p.support = q.support := by
    apply List.ext_getElem
    · rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_support, hlen]
    · intro n h1 h2
      rw [SimpleGraph.Walk.support_getElem_eq_getVert, SimpleGraph.Walk.support_getElem_eq_getVert]
      exact hv n (by rw [SimpleGraph.Walk.length_support] at h1; omega)
  rw [hlist]

/-- The finite sets contained in `X` that contain the origin, have `s` sites and
are `*`-connected. -/
noncomputable def xap8_starSets (X : Finset (Site d)) (s : ℕ) : Finset (Finset (Site d)) :=
  X.powerset.filter (fun S => (0 : Site d) ∈ S ∧ S.card = s ∧
    ((xap2_kingGraph d).induce (↑S : Set (Site d))).Connected)

/-- The padded direction code of a closed star-walk: the first `p.length`
entries are its directions, the rest are `none`.  It has type
`Fin (2 * s) → Option (xap8_Dir d)`, a type with `(3^d)^{2s}` elements.  Two
covering walks with the same padded code have the same length and directions
(`xap8_padCode_some_iff`), hence by `xap8_support_eq_of_code` the same support,
so the map `S ↦ xap8_padCode` is injective and `xap8_starSets X s` has at most
`(3^d)^{2s}` elements. -/
noncomputable def xap8_padCode {s : ℕ} (p : (xap2_kingGraph d).Walk (0 : Site d) (0 : Site d)) :
    Fin (2 * s) → Option (xap8_Dir d) :=
  fun i => if h : i.val < p.length then some (xap8_code p ⟨i.val, h⟩) else none

theorem xap8_padCode_some_iff {s : ℕ}
    (p : (xap2_kingGraph d).Walk (0 : Site d) (0 : Site d)) (i : Fin (2 * s)) :
    (xap8_padCode (s := s) p i).isSome ↔ i.val < p.length := by
  rw [xap8_padCode]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The number of `some` entries of the padded code is the walk length. -/
theorem xap8_padCode_len {s : ℕ} (p : (xap2_kingGraph d).Walk (0 : Site d) (0 : Site d))
    (hlen : p.length ≤ 2 * s) :
    (Finset.univ.filter (fun i : Fin (2 * s) => (xap8_padCode (s := s) p i).isSome)).card
      = p.length := by
  have hf : (Finset.univ.filter (fun i : Fin (2 * s) => (xap8_padCode (s := s) p i).isSome))
      = (Finset.univ.filter (fun i : Fin (2 * s) => i.val < p.length)) := by
    apply Finset.filter_congr
    intro i _
    exact xap8_padCode_some_iff p i
  rw [hf, ← Fintype.card_subtype]
  let e : {i : Fin (2 * s) // i.val < p.length} ≃ Fin p.length :=
    { toFun := fun i => ⟨i.val.val, i.prop⟩
      invFun := fun j => ⟨⟨j.val, by omega⟩, by simp⟩
      left_inv := fun i => by ext; rfl
      right_inv := fun j => by ext; rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- There are at most `(3^d)^{2s}` such sets: each is the support of a closed
star-walk of length at most `2s`, and the padded direction code of that walk is
injective and takes `(3^d)^{2s}` values. -/
theorem xap8_starSets_card_le (X : Finset (Site d)) (s : ℕ) :
    (xap8_starSets X s).card ≤ (3 ^ d) ^ (2 * s) := by
  classical
  have hmem : ∀ S ∈ xap8_starSets X s, (0 : Site d) ∈ S ∧ S.card = s ∧
      ((xap2_kingGraph d).induce (↑S : Set (Site d))).Connected := by
    intro S hS
    rw [xap8_starSets, Finset.mem_filter] at hS
    exact hS.2
  rw [← Fintype.card_coe (xap8_starSets X s)]
  refine le_trans (Fintype.card_le_of_injective
    (fun S : ↥(xap8_starSets X s) => xap8_padCode (s := s)
      (Classical.choose (xap7_coveringWalk S.1 (hmem S.1 S.2).1 (hmem S.1 S.2).2.2))) ?_) ?_
  · intro S1 S2 h
    have h1 := hmem S1.1 S1.2
    have h2 := hmem S2.1 S2.2
    set p1 := Classical.choose (xap7_coveringWalk S1.1 h1.1 h1.2.2) with hp1
    set p2 := Classical.choose (xap7_coveringWalk S2.1 h2.1 h2.2.2) with hp2
    have hs1 := Classical.choose_spec (xap7_coveringWalk S1.1 h1.1 h1.2.2)
    have hs2 := Classical.choose_spec (xap7_coveringWalk S2.1 h2.1 h2.2.2)
    have hlen1 : p1.length ≤ 2 * s := by
      calc p1.length ≤ 2 * S1.1.card := hs1.2
        _ = 2 * s := by rw [h1.2.1]
    have hlen2 : p2.length ≤ 2 * s := by
      calc p2.length ≤ 2 * S2.1.card := hs2.2
        _ = 2 * s := by rw [h2.2.1]
    have heq_len : p1.length = p2.length := by
      have hh : xap8_padCode (s := s) p1 = xap8_padCode (s := s) p2 := by
        simpa [hp1, hp2] using h
      rw [← xap8_padCode_len p1 hlen1, ← xap8_padCode_len p2 hlen2, hh]
    have heq_code : ∀ (i : Fin p1.length), xap8_code p1 i = xap8_code p2
        ⟨i.val, by rw [← heq_len]; exact i.isLt⟩ := by
      intro i
      have hh : xap8_padCode (s := s) p1 = xap8_padCode (s := s) p2 := by
        simpa [hp1, hp2] using h
      have hc := congrFun hh ⟨i.val, by omega⟩
      rw [xap8_padCode, dif_pos i.isLt, xap8_padCode, dif_pos (by rw [← heq_len]; exact i.isLt)] at hc
      exact Option.some.inj hc
    have hsupp := xap8_support_eq_of_code heq_len heq_code
    exact Subtype.ext (by rw [← hs1.1, ← hs2.1]; exact hsupp)
  · rw [Fintype.card_fun, Fintype.card_fin]
    have hopt : Fintype.card (Option (xap8_Dir d)) = 3 ^ d := by
      rw [Fintype.card_option, Fintype.card_coe, xap5_dirFinset]
      rw [Finset.card_erase_add_one]
      · exact xap_card_cubeFinset (0 : Site d)
      · rw [xap_mem_cubeFinset]; exact xap_mem_cube_self (0 : Site d)
    rw [hopt]

/-- The high-density union bound over all `*`-connected `s`-sets in `X` through
the origin: the probability that one of them is all bad is at most
`(3^d)^{2s} (1 - δ)^{s / 3^d}`.  This is the finite-cluster Peierls term. -/
theorem xap8_starSets_bad_prob_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (X : Finset (Site d)) (s : ℕ) :
    bondPercolation d q {ω | ∃ Γ ∈ xap8_starSets X s, ∀ z ∈ Γ, ¬ xap_Good ω z} ≤
      ((3 ^ d) ^ (2 * s) : ENNReal) * (1 - xap6_delta d q) ^ (s / 3 ^ d) := by
  have hcard : ∀ Γ ∈ xap8_starSets X s, Γ.card = s := by
    intro Γ hΓ
    rw [xap8_starSets, Finset.mem_filter] at hΓ
    exact hΓ.2.2.1
  refine (xap6_biUnion_bad_prob_le h0 h1 (xap8_starSets X s) s hcard).trans ?_
  exact mul_le_mul_left (by exact_mod_cast xap8_starSets_card_le X s) _

end Exploding
