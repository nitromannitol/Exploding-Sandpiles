/-
Proposition 5.1 of the paper (generalized last wave): the dependence graph of the good-edge field of
a finite-range dependent field of tiles, its degree bound and the lower bound on its marginals.
-/
import Exploding.Support.GLWSec3AF

open MeasureTheory ProbabilityTheory Exploding LatticeProb Filter

namespace Exploding

variable {d : ℕ}

/-- The graph on the bonds of `ℤ^d` in which two distinct bonds are adjacent when they have
endpoints at `ℓ¹` distance at most `K`. -/
def glws_bondGraph (d K : ℕ) : SimpleGraph (RnBond d) where
  Adj e e' := e ≠ e' ∧ ∃ u ∈ rn_ends e, ∃ v ∈ rn_ends e', mnorm (u - v) ≤ (K : ℤ)
  symm := ⟨fun e e' h => by
    obtain ⟨hne, u, hu, v, hv, hd⟩ := h
    refine ⟨hne.symm, v, hv, u, hu, ?_⟩
    rw [glws_mnorm_sub_comm]; exact hd⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The sites at `ℓ^∞` distance at most `K` from the origin. -/
noncomputable def glws_ballF (d K : ℕ) : Finset (Site d) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(K : ℤ)) (K : ℤ))

/-- A finite set containing the neighbours of a bond in `glws_bondGraph`. -/
noncomputable def glws_nbrs (d K : ℕ) (e : RnBond d) : Finset (RnBond d) :=
  (rn_ends e).biUnion (fun u => (glws_ballF d K).biUnion (fun w => rn_incident d (u + w)))

/-- The degree bound of the bond graph. -/
theorem glws_bondGraph_degree (K : ℕ) (e : RnBond d) :
    ((glws_bondGraph d K).neighborSet e).Finite ∧
      ((glws_bondGraph d K).neighborSet e).ncard ≤ 2 * ((glws_ballF d K).card * (2 * d)) := by
  have hsub : (glws_bondGraph d K).neighborSet e ⊆ ↑(glws_nbrs d K e) := by
    intro e' he'
    obtain ⟨hne, u, hu, v, hv, hdist⟩ := (he' : (glws_bondGraph d K).Adj e e')
    simp only [glws_nbrs, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
    refine ⟨u, hu, v - u, ?_, ?_⟩
    · simp only [glws_ballF, Fintype.mem_piFinset, Finset.mem_Icc]
      intro l
      have h1 := abs_coord_le_mnorm (u - v) l
      have h2 : |(v - u) l| = |(u - v) l| := by
        simp only [Pi.sub_apply]; exact abs_sub_comm _ _
      have h3 : |(v - u) l| ≤ (K : ℤ) := by rw [h2]; exact le_trans h1 hdist
      exact abs_le.mp h3
    · have : u + (v - u) = v := by abel
      rw [this]
      exact rn_mem_incident_of_mem_ends hv
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  unfold glws_nbrs
  refine Finset.card_biUnion_le.trans ?_
  have hends : (rn_ends e).card ≤ 2 := Finset.card_le_two
  have hone : ∀ u : Site d, ((glws_ballF d K).biUnion (fun w => rn_incident d (u + w))).card ≤
      (glws_ballF d K).card * (2 * d) := by
    intro u
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ w ∈ glws_ballF d K, (rn_incident d (u + w)).card ≤
          ∑ _w ∈ glws_ballF d K, 2 * d := Finset.sum_le_sum fun w _ => rn_card_incident_le _
      _ = (glws_ballF d K).card * (2 * d) := by rw [Finset.sum_const, smul_eq_mul]
  calc ∑ u ∈ rn_ends e, ((glws_ballF d K).biUnion (fun w => rn_incident d (u + w))).card
      ≤ ∑ _u ∈ rn_ends e, (glws_ballF d K).card * (2 * d) := Finset.sum_le_sum fun u _ => hone u
    _ = (rn_ends e).card * ((glws_ballF d K).card * (2 * d)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * ((glws_ballF d K).card * (2 * d)) := Nat.mul_le_mul_right _ hends

open scoped Classical in
/-- The finite set of sites of a tile. -/
noncomputable def glws_tileF (k : Fin d → ℕ) (j : Site d) : Finset (Site d) :=
  (glws_tile_finite k j).toFinset

theorem glws_mem_tileF (k : Fin d → ℕ) (j x : Site d) : x ∈ glws_tileF k j ↔ x ∈ rboxShift k j := by
  unfold glws_tileF
  exact Set.Finite.mem_toFinset _

open scoped Classical in
/-- The bit of a tile: whether it is strongly box-crossing. -/
noncomputable def glws_X (k : Fin d → ℕ) (x : Site d) (η : Site d → ℤ) : Bool :=
  decide (StronglyBoxCrossed η k x)

theorem glws_X_congr (k : Fin d → ℕ) (x : Site d) (η η' : Site d → ℤ)
    (h : ∀ a ∈ rboxShift k x, η a = η' a) : glws_X k x η = glws_X k x η' := by
  unfold glws_X
  simp only [decide_eq_decide]
  exact glws_sbc_congr k x η η' h

theorem glws_X_meas (k : Fin d → ℕ) (x : Site d) : Measurable (glws_X k x) :=
  glws_local_meas (glws_tileF k x) _ (fun η η' h =>
    glws_X_congr k x η η' (fun a ha => h a ((glws_mem_tileF k x a).mpr ha)))

/-- The good-edge field. -/
noncomputable def glws_Phi (k : Fin d → ℕ) (e : RnBond d) (η : Site d → ℤ) : Bool :=
  glws_X k e.1 η && glws_X k (e.1 + unit e.2) η

/-- The sites on which the good-edge bit of a bond depends. -/
noncomputable def glws_vs (k : Fin d → ℕ) (e : RnBond d) : Finset (Site d) :=
  glws_tileF k e.1 ∪ glws_tileF k (e.1 + unit e.2)

/-- **The dependence graph of the good-edge field.**  Under finite range of dependence `K`, the
good-edge field of the tiles has dependence graph `glws_bondGraph d K`. -/
theorem glws_edge_dependence (P : Measure (Site d → ℤ)) [IsProbabilityMeasure P] (K : ℕ)
    (hFR : ∀ I J : Finset (Site d), (∀ a ∈ I, ∀ b ∈ J, (K : ℤ) < mnorm (a - b)) →
      IndepFun (fun η : Site d → ℤ => fun i : I => η i)
        (fun η : Site d → ℤ => fun j : J => η j) P)
    (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) :
    Measurable (fun (η : Site d → ℤ) (e : RnBond d) => glws_Phi k e η) ∧
      HasDependenceGraph (glws_bondGraph d K)
        (P.map (fun (η : Site d → ℤ) (e : RnBond d) => glws_Phi k e η)) := by
  refine glws_dependence_graph P K hFR (glws_bondGraph d K) (glws_vs k) (glws_Phi k) ?_ ?_
  · intro e η η' h
    unfold glws_Phi
    rw [glws_X_congr k e.1 η η' (fun a ha => h a (Finset.mem_union_left _
      ((glws_mem_tileF k e.1 a).mpr ha))),
      glws_X_congr k (e.1 + unit e.2) η η' (fun a ha => h a (Finset.mem_union_right _
      ((glws_mem_tileF k (e.1 + unit e.2) a).mpr ha)))]
  · intro e e' hne hadj a ha b hb
    have hfar : ∀ u ∈ rn_ends e, ∀ v ∈ rn_ends e', (K : ℤ) < mnorm (u - v) := by
      intro u hu v hv
      by_contra hcon
      exact hadj ⟨hne, u, hu, v, hv, not_lt.mp hcon⟩
    have hends : ∀ x, x ∈ glws_vs k e → ∃ u ∈ rn_ends e, x ∈ rboxShift k u := by
      intro x hx
      unfold glws_vs at hx
      rcases Finset.mem_union.mp hx with h | h
      · exact ⟨e.1, by simp [rn_ends], (glws_mem_tileF k _ _).mp h⟩
      · exact ⟨e.1 + unit e.2, by simp [rn_ends], (glws_mem_tileF k _ _).mp h⟩
    have hends' : ∀ x, x ∈ glws_vs k e' → ∃ u ∈ rn_ends e', x ∈ rboxShift k u := by
      intro x hx
      unfold glws_vs at hx
      rcases Finset.mem_union.mp hx with h | h
      · exact ⟨e'.1, by simp [rn_ends], (glws_mem_tileF k _ _).mp h⟩
      · exact ⟨e'.1 + unit e'.2, by simp [rn_ends], (glws_mem_tileF k _ _).mp h⟩
    obtain ⟨u, hu, hau⟩ := hends a ha
    obtain ⟨v, hv, hbv⟩ := hends' b hb
    exact lt_of_lt_of_le (hfar u hu v hv) (glws_tile_dist k hk hau hbv)

end Exploding
