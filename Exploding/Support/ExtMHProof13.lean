/-
`xmh8_BoundaryInfinite`: an infinite connected component of the complement of an infinite
open cluster has infinite inner boundary.  The proof is purely geometric: a finite inner
boundary would make the outer boundary finite, and an infinite connected set with finite
outer boundary is separated from the rest by finitely many sites, which is impossible in
`ℤ^d` for `d ≥ 2` because the complement of a box is connected.
-/
import Exploding.Support.ExtMHProof12

namespace Exploding

open LatticeProb MeasureTheory Filter Relation
open scoped BigOperators

variable {d : ℕ}
variable {q : ℝ}

/-- The relation of a nearest-neighbour step inside a set. -/
def xmh9_R (S : Set (Site d)) : Site d → Site d → Prop :=
  fun a b => a ∈ S ∧ b ∈ S ∧ (lattice d).Adj a b

/-- A set closed under internal adjacency is stable under internal paths. -/
theorem xmh9_closed_rtg {S U : Set (Site d)}
    (hcl : ∀ s ∈ S, ∀ t ∈ U, (lattice d).Adj s t → t ∈ S)
    {u v : Site d} (hu : u ∈ S) (h : ReflTransGen (xmh9_R U) u v) : v ∈ S := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih => exact hcl _ ih _ hbc.2.1 hbc.2.2

/-- Shifting the `k`-th coordinate up by one is a nearest-neighbour step. -/
theorem xmh9_step (p : Site d) (k : Fin d) (t : ℤ) :
    Function.update p k t + unit k = Function.update p k (t + 1) := by
  ext j
  by_cases hj : j = k
  · subst hj; simp [unit, Pi.single]
  · simp [unit, Pi.single, hj]

/-- A path along one coordinate line, staying outside the box. -/
theorem xmh9_line (N : ℕ) {k i : Fin d} (hki : k ≠ i) (p : Site d) {a b : ℤ}
    (hu : ¬ |p i| ≤ (N : ℤ)) (h : a ≤ b) :
    ReflTransGen (xmh9_R {x : Site d | x ∉ cent d N})
      (Function.update p k a) (Function.update p k b) := by
  have hci : ∀ t : ℤ, (Function.update p k t) i = p i := by
    intro t
    simp only [Function.update_apply]
    rw [if_neg]
    exact Ne.symm hki
  have hmem : ∀ t : ℤ, Function.update p k t ∈ {x : Site d | x ∉ cent d N} := by
    intro t hx
    exact hu (by rw [← hci t]; exact hx i)
  have key : ∀ n : ℕ, ReflTransGen (xmh9_R {x : Site d | x ∉ cent d N})
      (Function.update p k a) (Function.update p k (a + n)) := by
    intro n
    induction n with
    | zero => simpa using ReflTransGen.refl
    | succ n ih =>
        refine ih.tail ⟨hmem _, hmem _, ?_⟩
        rw [show a + (n + 1 : ℕ) = (a + (n : ℤ)) + 1 by push_cast; ring,
          ← xmh9_step p k (a + (n : ℤ))]
        exact ⟨k, Or.inl rfl⟩
  have hb : b = a + (b - a).toNat := by omega
  rw [hb]
  exact key (b - a).toNat

/-- The same line, in either direction. -/
theorem xmh9_line_any (N : ℕ) {k i : Fin d} (hki : k ≠ i) (p : Site d) (a b : ℤ)
    (hu : ¬ |p i| ≤ (N : ℤ)) :
    ReflTransGen (xmh9_R {x : Site d | x ∉ cent d N})
      (Function.update p k a) (Function.update p k b) := by
  rcases le_total a b with h | h
  · exact xmh9_line N hki p hu h
  · have := xmh9_line N hki p hu h
    exact (xmh_rtg_symm (fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩) this)

/-- There is a second coordinate. -/
theorem xmh9_exists_ne (hd : 2 ≤ d) (i : Fin d) : ∃ j : Fin d, j ≠ i := by
  by_cases h : i = ⟨0, by omega⟩
  · refine ⟨⟨1, by omega⟩, fun hh => ?_⟩
    rw [h] at hh
    exact absurd (congrArg Fin.val hh) (by simp)
  · exact ⟨⟨0, by omega⟩, fun hh => h hh.symm⟩

/-- Changing all coordinates except `i` to `N+1` keeps the `i`-th coordinate, hence stays
outside the box. -/
theorem xmh9_change_others (N : ℕ) (u : Site d) {i : Fin d} (hu : ¬ |u i| ≤ (N : ℤ)) :
    ReflTransGen (xmh9_R {x : Site d | x ∉ cent d N}) u
      (Function.update (fun _ => (N : ℤ) + 1) i (u i)) := by
  classical
  let g : Finset (Fin d) → Site d := fun S j => if j ∈ S then (N : ℤ) + 1 else u j
  have hmain : ∀ S : Finset (Fin d), i ∉ S →
      ReflTransGen (xmh9_R {x : Site d | x ∉ cent d N}) u (g S) := by
    intro S
    induction S using Finset.induction with
    | empty =>
        intro _
        rw [show g ∅ = u from funext fun j => by simp [g]]
    | insert j S hjs ih =>
        intro hiS
        have hj : j ≠ i := fun h => hiS (h ▸ Finset.mem_insert_self j S)
        have hiS' : i ∉ S := fun h => hiS (Finset.mem_insert_of_mem h)
        have hgi : (g S) i = u i := by
          simp only [g]
          exact if_neg hiS'
        have hout : ¬ |(g S) i| ≤ (N : ℤ) := by rw [hgi]; exact hu
        have hstep := xmh9_line_any N (k := j) (i := i) hj (g S) ((g S) j) ((N : ℤ) + 1) hout
        rw [show Function.update (g S) j ((g S) j) = g S from
          Function.update_eq_self j (g S)] at hstep
        refine (ih hiS').trans ?_
        have hg : Function.update (g S) j ((N : ℤ) + 1) = g (insert j S) := by
          funext j'
          by_cases hj' : j' = j
          · subst hj'; simp [g]
          · simp [g, Finset.mem_insert, hj']
        rw [hg] at hstep
        exact hstep
  have hgoal : g (Finset.univ.erase i) = Function.update (fun _ => (N : ℤ) + 1) i (u i) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [g, Finset.mem_erase]
    · simp [g, Finset.mem_erase, hj]
  rw [← hgoal]
  exact hmain _ (by simp)

/-- **The complement of a box in `ℤ^d` is connected for `d ≥ 2`.** -/
theorem xmh9_conn_compl_cent (hd : 2 ≤ d) (N : ℕ) :
    ∀ u : Site d, u ∉ cent d N → ∀ v : Site d, v ∉ cent d N →
      ReflTransGen (xmh9_R {x : Site d | x ∉ cent d N}) u v := by
  have hsymm : ∀ a b, xmh9_R {x : Site d | x ∉ cent d N} a b →
      xmh9_R {x : Site d | x ∉ cent d N} b a :=
    fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩
  intro u hu v hv
  have key : ∀ z : Site d, z ∉ cent d N →
      ReflTransGen (xmh9_R {x : Site d | x ∉ cent d N}) z (fun _ => (N : ℤ) + 1) := by
    intro z hz
    obtain ⟨i, hi⟩ : ∃ i : Fin d, ¬ |z i| ≤ (N : ℤ) := by
      by_contra h
      push Not at h
      exact hz h
    obtain ⟨j, hji⟩ := xmh9_exists_ne hd i
    have h1 := xmh9_change_others N z hi
    have hzj : (Function.update (fun _ => (N : ℤ) + 1) i (z i)) j = (N : ℤ) + 1 := by
      rw [Function.update_apply, if_neg hji]
    have hout : ¬ |(Function.update (fun _ => (N : ℤ) + 1) i (z i)) j| ≤ (N : ℤ) := by
      rw [hzj, abs_of_nonneg (by positivity)]
      omega
    have h2 := xmh9_line_any N (k := i) (i := j) (Ne.symm hji)
      (Function.update (fun _ => (N : ℤ) + 1) i (z i)) (z i) ((N : ℤ) + 1) hout
    simp only [Function.update_idem, Function.update_eq_self] at h2
    exact h1.trans h2
  exact (key u hu).trans (xmh_rtg_symm hsymm (key v hv))

end Exploding
