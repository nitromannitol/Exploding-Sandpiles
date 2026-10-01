/-
The finite-cluster geometric-series estimate, reworked so that the all-bad
`*`-connected set does **not** have to contain the origin (the origin can be good
while its cluster is finite, which is exactly why `xap9_FiniteClusterReduction`
is false, `xap10_not_finiteClusterReduction`).  The counting object is
`xap11_starSets X s`, the `*`-connected `s`-subsets of a finite region `X`:
there are at most `X.card * (3^d)^{2s}` of them (`xap11_starSets_card_le`), so
the packed bad-set bound gives `xap11_starSets_bad_prob_le`.  The finite-cluster
event is then bounded by the geometric series
`∑_s (ball s).card * (3^d)^{2s} * (1 - δ)^{s/3^d}` once one supplies the standard
geometric input `xap11_FiniteClusterReduction` that a finite cluster has an
all-bad `*`-connected boundary of `s` sites inside the ball of radius `s`.
-/
import Exploding.Support.ExtAPProof10
import Mathlib.Data.Fintype.EquivFin

open Exploding LatticeProb MeasureTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-! ### Direction codes for star-walks from an arbitrary root -/

/-- The star-step directions of the origin, as a type. -/
abbrev xap11_Dir (d : ℕ) := xap8_Dir d

/-- The direction sequence of a closed star-walk from an arbitrary root. -/
noncomputable def xap11_code {r : Site d} (p : (xap2_kingGraph d).Walk r r) :
    Fin p.length → xap11_Dir d :=
  fun i => xap8_stepDir (p.adj_getVert_succ i.isLt)

/-- Each vertex is the previous vertex plus the step direction. -/
theorem xap11_getVert_succ {r : Site d} (p : (xap2_kingGraph d).Walk r r)
    (i : Fin p.length) :
    p.getVert (i.val + 1) = p.getVert i.val + (xap11_code p i).val := by
  rw [xap11_code, xap8_stepDir_val]
  abel

/-- Two closed star-walks from the same root with the same length and direction
sequence have the same vertices. -/
theorem xap11_getVert_eq {r : Site d} {p q : (xap2_kingGraph d).Walk r r}
    (hlen : p.length = q.length)
    (hcode : ∀ (i : Fin p.length), xap11_code p i = xap11_code q ⟨i.val, by omega⟩) :
    ∀ i : ℕ, i ≤ p.length → p.getVert i = q.getVert i := by
  intro i
  induction i with
  | zero => intro _; rw [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_zero]
  | succ i ih =>
      intro hi
      rw [xap11_getVert_succ p ⟨i, by omega⟩, xap11_getVert_succ q ⟨i, by omega⟩,
        ih (by omega), hcode ⟨i, by omega⟩]

/-- Two closed star-walks from the same root with the same length and direction
sequence have the same support. -/
theorem xap11_support_eq_of_code {r : Site d} {p q : (xap2_kingGraph d).Walk r r}
    (hlen : p.length = q.length)
    (hcode : ∀ (i : Fin p.length), xap11_code p i = xap11_code q ⟨i.val, by omega⟩) :
    p.support.toFinset = q.support.toFinset := by
  have hv := xap11_getVert_eq hlen hcode
  have hlist : p.support = q.support := by
    apply List.ext_getElem
    · rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_support, hlen]
    · intro n h1 h2
      rw [SimpleGraph.Walk.support_getElem_eq_getVert, SimpleGraph.Walk.support_getElem_eq_getVert]
      exact hv n (by rw [SimpleGraph.Walk.length_support] at h1; omega)
  rw [hlist]

/-- Two closed star-walks from equal roots with the same length and direction
sequence have the same support. -/
theorem xap11_support_eq_of_code' {r1 r2 : Site d} (hr : r1 = r2)
    {p : (xap2_kingGraph d).Walk r1 r1} {q : (xap2_kingGraph d).Walk r2 r2}
    (hlen : p.length = q.length)
    (hcode : ∀ (i : Fin p.length), xap11_code p i = xap11_code q ⟨i.val, by omega⟩) :
    p.support.toFinset = q.support.toFinset := by
  subst hr
  exact xap11_support_eq_of_code hlen hcode

/-- The padded direction code of a closed star-walk from an arbitrary root. -/
noncomputable def xap11_padCode {s : ℕ} {r : Site d} (p : (xap2_kingGraph d).Walk r r) :
    Fin (2 * s) → Option (xap11_Dir d) :=
  fun i => if h : i.val < p.length then some (xap11_code p ⟨i.val, h⟩) else none

theorem xap11_padCode_some_iff {s : ℕ} {r : Site d}
    (p : (xap2_kingGraph d).Walk r r) (i : Fin (2 * s)) :
    (xap11_padCode (s := s) p i).isSome ↔ i.val < p.length := by
  rw [xap11_padCode]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The value of the padded code at an index inside the walk length. -/
theorem xap11_padCode_apply {s : ℕ} {r : Site d} (p : (xap2_kingGraph d).Walk r r)
    (i : Fin (2 * s)) (h : i.val < p.length) :
    xap11_padCode (s := s) p i = some (xap11_code p ⟨i.val, h⟩) := by
  rw [xap11_padCode]
  exact dif_pos h

/-- The number of `some` entries of the padded code is the walk length. -/
theorem xap11_padCode_len {s : ℕ} {r : Site d} (p : (xap2_kingGraph d).Walk r r)
    (hlen : p.length ≤ 2 * s) :
    (Finset.univ.filter (fun i : Fin (2 * s) => (xap11_padCode (s := s) p i).isSome)).card
      = p.length := by
  have hf : (Finset.univ.filter (fun i : Fin (2 * s) => (xap11_padCode (s := s) p i).isSome))
      = (Finset.univ.filter (fun i : Fin (2 * s) => i.val < p.length)) := by
    apply Finset.filter_congr
    intro i _
    exact xap11_padCode_some_iff p i
  rw [hf, ← Fintype.card_subtype]
  let e : {i : Fin (2 * s) // i.val < p.length} ≃ Fin p.length :=
    { toFun := fun i => ⟨i.val.val, i.prop⟩
      invFun := fun j => ⟨⟨j.val, by omega⟩, by simp⟩
      left_inv := fun i => by ext; rfl
      right_inv := fun j => by ext; rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]

/-! ### The origin-free connected-set count -/

/-- The `*`-connected subsets of a finite region `X` with `s` sites.  No base
point is required, so this is the right counting object for the bad boundary of a
finite cluster. -/
noncomputable def xap11_starSets (X : Finset (Site d)) (s : ℕ) : Finset (Finset (Site d)) :=
  X.powerset.filter (fun S => S.card = s ∧
    ((xap2_kingGraph d).induce (↑S : Set (Site d))).Connected)

/-- A chosen root of a nonempty finset. -/
noncomputable def xap11_root (S : Finset (Site d)) (hne : Nonempty ↥S) : Site d :=
  (Classical.choice hne).1

theorem xap11_root_mem (S : Finset (Site d)) (hne : Nonempty ↥S) :
    xap11_root S hne ∈ S := (Classical.choice hne).2

/-- The chosen closed covering walk of a connected finset, in the induced graph. -/
noncomputable def xap11_coverRaw (S : Finset (Site d))
    (hconn : ((xap2_kingGraph d).induce (↑S : Set (Site d))).Connected) :
    ((xap2_kingGraph d).induce (↑S : Set (Site d))).Walk
      ⟨xap11_root S hconn.2, xap11_root_mem S hconn.2⟩
      ⟨xap11_root S hconn.2, xap11_root_mem S hconn.2⟩ :=
  Classical.choose (xap7_gen_closed_walk (Fintype.card ↥S) ↥S
    ((xap2_kingGraph d).induce (↑S : Set (Site d)))
    ⟨xap11_root S hconn.2, xap11_root_mem S hconn.2⟩ rfl hconn)

theorem xap11_coverRaw_support (S : Finset (Site d))
    (hconn : ((xap2_kingGraph d).induce (↑S : Set (Site d))).Connected) :
    (xap11_coverRaw S hconn).support.toFinset = Finset.univ :=
  (Classical.choose_spec (xap7_gen_closed_walk (Fintype.card ↥S) ↥S
    ((xap2_kingGraph d).induce (↑S : Set (Site d)))
    ⟨xap11_root S hconn.2, xap11_root_mem S hconn.2⟩ rfl hconn)).1

theorem xap11_coverRaw_length (S : Finset (Site d))
    (hconn : ((xap2_kingGraph d).induce (↑S : Set (Site d))).Connected) :
    (xap11_coverRaw S hconn).length ≤ 2 * Fintype.card ↥S :=
  (Classical.choose_spec (xap7_gen_closed_walk (Fintype.card ↥S) ↥S
    ((xap2_kingGraph d).induce (↑S : Set (Site d)))
    ⟨xap11_root S hconn.2, xap11_root_mem S hconn.2⟩ rfl hconn)).2

/-- The chosen closed covering walk of a connected finset, in the king graph. -/
noncomputable def xap11_cover (S : Finset (Site d))
    (hconn : ((xap2_kingGraph d).induce (↑S : Set (Site d))).Connected) :
    (xap2_kingGraph d).Walk (xap11_root S hconn.2) (xap11_root S hconn.2) :=
  (xap11_coverRaw S hconn).map ⟨Subtype.val, fun hh => hh⟩

theorem xap11_cover_support (S : Finset (Site d))
    (hconn : ((xap2_kingGraph d).induce (↑S : Set (Site d))).Connected) :
    (xap11_cover S hconn).support.toFinset = S := by
  rw [xap11_cover, SimpleGraph.Walk.support_map]
  apply Finset.ext
  intro x
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨a, -, rfl⟩; exact a.2
  · intro hx
    exact ⟨⟨x, hx⟩, by rw [← List.mem_toFinset, xap11_coverRaw_support]; exact Finset.mem_univ _, rfl⟩

theorem xap11_cover_length (S : Finset (Site d))
    (hconn : ((xap2_kingGraph d).induce (↑S : Set (Site d))).Connected) :
    (xap11_cover S hconn).length ≤ 2 * Fintype.card ↥S := by
  rw [xap11_cover, SimpleGraph.Walk.length_map]
  exact xap11_coverRaw_length S hconn

/-- There are at most `X.card * (3^d)^{2s}` `*`-connected `s`-subsets of `X`:
each is the support of a closed covering star-walk from a chosen root, encoded by
the pair (root, padded direction sequence). -/
theorem xap11_starSets_card_le (X : Finset (Site d)) (s : ℕ) :
    (xap11_starSets X s).card ≤ X.card * (3 ^ d) ^ (2 * s) := by
  classical
  have hmem : ∀ S ∈ xap11_starSets X s, S ⊆ X ∧ S.card = s ∧
      ((xap2_kingGraph d).induce (↑S : Set (Site d))).Connected := by
    intro S hS
    rw [xap11_starSets, Finset.mem_filter, Finset.mem_powerset] at hS
    exact ⟨hS.1, hS.2.1, hS.2.2⟩
  rw [← Fintype.card_coe (xap11_starSets X s)]
  let Φ : ↥(xap11_starSets X s) → ↥X × (Fin (2 * s) → Option (xap11_Dir d)) := fun S =>
    (⟨xap11_root S.1 (hmem S.1 S.2).2.2.2,
      (hmem S.1 S.2).1 (xap11_root_mem S.1 (hmem S.1 S.2).2.2.2)⟩,
      xap11_padCode (s := s) (xap11_cover S.1 (hmem S.1 S.2).2.2))
  refine le_trans (Fintype.card_le_of_injective Φ ?_) ?_
  · intro S1 S2 heq
    have hroot : xap11_root S1.1 (hmem S1.1 S1.2).2.2.2
        = xap11_root S2.1 (hmem S2.1 S2.2).2.2.2 := by
      have h := congrArg (fun t => (t.1 : Site d)) heq
      simpa [Φ] using h
    have hcode : xap11_padCode (s := s) (xap11_cover S1.1 (hmem S1.1 S1.2).2.2)
        = xap11_padCode (s := s) (xap11_cover S2.1 (hmem S2.1 S2.2).2.2) := by
      have h := congrArg Prod.snd heq
      simpa [Φ] using h
    set p1 := xap11_cover S1.1 (hmem S1.1 S1.2).2.2 with hp1
    set p2 := xap11_cover S2.1 (hmem S2.1 S2.2).2.2 with hp2
    have hspec1 : p1.support.toFinset = S1.1 := by
      rw [hp1]; exact xap11_cover_support S1.1 (hmem S1.1 S1.2).2.2
    have hspec2 : p2.support.toFinset = S2.1 := by
      rw [hp2]; exact xap11_cover_support S2.1 (hmem S2.1 S2.2).2.2
    have hlen1 : p1.length ≤ 2 * s := by
      have h := xap11_cover_length S1.1 (hmem S1.1 S1.2).2.2
      have h2 : Fintype.card ↥S1.1 = s := by
        rw [Fintype.card_coe, (hmem S1.1 S1.2).2.1]
      rw [← hp1, h2] at h
      exact h
    have hlen2 : p2.length ≤ 2 * s := by
      have h := xap11_cover_length S2.1 (hmem S2.1 S2.2).2.2
      have h2 : Fintype.card ↥S2.1 = s := by
        rw [Fintype.card_coe, (hmem S2.1 S2.2).2.1]
      rw [← hp2, h2] at h
      exact h
    have heq_len : p1.length = p2.length := by
      rw [← xap11_padCode_len p1 hlen1, ← xap11_padCode_len p2 hlen2, hcode]
    have heq_code : ∀ (i : Fin p1.length), xap11_code p1 i =
        xap11_code p2 ⟨i.val, by rw [← heq_len]; exact i.isLt⟩ := by
      intro i
      have hc := congrFun hcode (⟨i.val, by have := i.isLt; omega⟩ : Fin (2 * s))
      rw [xap11_padCode_apply p1 _ i.isLt,
        xap11_padCode_apply p2 _ (by rw [← heq_len]; exact i.isLt)] at hc
      exact Option.some.inj hc
    have hsupp := xap11_support_eq_of_code' hroot heq_len heq_code
    exact Subtype.ext (by rw [← hspec1, ← hspec2]; exact hsupp)
  · rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_option]
    have hopt : Fintype.card (xap11_Dir d) + 1 = 3 ^ d := by
      rw [Fintype.card_coe, xap5_dirFinset]
      rw [Finset.card_erase_add_one]
      · exact xap_card_cubeFinset (0 : Site d)
      · rw [xap_mem_cubeFinset]; exact xap_mem_cube_self (0 : Site d)
    rw [hopt]

/-! ### The bad-set union bound -/

theorem xap11_starSets_bad_prob_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (X : Finset (Site d)) (s : ℕ) :
    bondPercolation d q {ω | ∃ Γ ∈ xap11_starSets X s, ∀ z ∈ Γ, ¬ xap_Good ω z} ≤
      ((X.card * (3 ^ d) ^ (2 * s) : ℕ) : ENNReal) * (1 - xap6_delta d q) ^ (s / 3 ^ d) := by
  have hcard : ∀ Γ ∈ xap11_starSets X s, Γ.card = s := by
    intro Γ hΓ
    rw [xap11_starSets, Finset.mem_filter] at hΓ
    exact hΓ.2.1
  refine (xap6_biUnion_bad_prob_le h0 h1 (xap11_starSets X s) s hcard).trans ?_
  exact mul_le_mul_left (by exact_mod_cast xap11_starSets_card_le X s) _

/-! ### The finite-cluster geometric series -/

/-- The `mnorm`-ball of radius `s`. -/
noncomputable def xap11_ball (d s : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(s : ℤ)) (s : ℤ)

theorem xap11_ball_card (d s : ℕ) : (xap11_ball d s).card = (2 * s + 1) ^ d := by
  simp only [xap11_ball, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- The standard geometric input of the Peierls estimate, with the origin
excluded: a finite good cluster of the origin has an all-bad `*`-connected
boundary of `s` sites lying inside the `mnorm`-ball of radius `s`.  This is
stated, not proved. -/
def xap11_FiniteClusterReduction (d : ℕ) : Prop :=
  ∀ ω : Site d × Fin d → Bool, xap5_SmallCluster ω →
    ∃ s : ℕ, ∃ Γ ∈ xap11_starSets (xap11_ball d s) s, ∀ z ∈ Γ, ¬ xap_Good ω z

/-- Conditional on `xap11_FiniteClusterReduction`, the finite-cluster event is at
most the geometric series `∑_s (2s+1)^d (3^d)^{2s} (1 - δ)^{s/3^d}`, which
converges as soon as `3^{2d} (1 - δ)^{1/3^d} < 1`. -/
theorem xap11_smallCluster_prob_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hred : xap11_FiniteClusterReduction d) :
    bondPercolation d q {ω | xap5_SmallCluster ω} ≤
      ∑' s : ℕ, (((xap11_ball d s).card * (3 ^ d) ^ (2 * s) : ℕ) : ENNReal) *
        (1 - xap6_delta d q) ^ (s / 3 ^ d) := by
  have hsub : {ω : Site d × Fin d → Bool | xap5_SmallCluster ω} ⊆
      ⋃ s : ℕ, {ω | ∃ Γ ∈ xap11_starSets (xap11_ball d s) s, ∀ z ∈ Γ, ¬ xap_Good ω z} := by
    intro ω hω
    obtain ⟨s, Γ, hΓ, hbad⟩ := hred ω hω
    exact Set.mem_iUnion.2 ⟨s, Γ, hΓ, hbad⟩
  calc bondPercolation d q {ω | xap5_SmallCluster ω}
      ≤ bondPercolation d q (⋃ s : ℕ,
          {ω | ∃ Γ ∈ xap11_starSets (xap11_ball d s) s, ∀ z ∈ Γ, ¬ xap_Good ω z}) :=
        measure_mono hsub
    _ ≤ ∑' s : ℕ, bondPercolation d q
          {ω | ∃ Γ ∈ xap11_starSets (xap11_ball d s) s, ∀ z ∈ Γ, ¬ xap_Good ω z} :=
        measure_iUnion_le _
    _ ≤ ∑' s : ℕ, (((xap11_ball d s).card * (3 ^ d) ^ (2 * s) : ℕ) : ENNReal) *
          (1 - xap6_delta d q) ^ (s / 3 ^ d) :=
        ENNReal.tsum_le_tsum fun s => xap11_starSets_bad_prob_le h0 h1 (xap11_ball d s) s

end Exploding
