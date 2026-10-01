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

end Exploding
