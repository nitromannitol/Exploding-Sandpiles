/-
Proposition 5.1 of the paper (generalized last wave): connectivity of lit regions.  A box is
connected inside any set containing it, adjacent tiles contain adjacent sites, and two sites of a
finite set that are connected inside it are joined by a path of distinct sites of the set.
-/
import Exploding.Support.GLWSec3M
import Exploding.Support.PCloseProofGeom

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- A tile is a box with prescribed corners. -/
theorem glws_tile_eq_box (k : Fin d → ℕ) (j : Site d) :
    rboxShift k j = pcloseBox (fun i => 1 + (k i : ℤ) * j i) (fun i => (k i : ℤ) * j i + k i) :=
  rfl

/-- **A box is connected inside any set containing it.** -/
theorem glws_box_reach (S : Set (Site d)) (m M : Site d) (hS : pcloseBox m M ⊆ S) :
    ∀ (N : ℕ) (u v : Site d) (hu : u ∈ pcloseBox m M) (hv : v ∈ pcloseBox m M),
      (mnorm (u - v)).toNat = N →
      ((lattice d).induce S).Reachable ⟨u, hS hu⟩ ⟨v, hS hv⟩ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro u v hu hv hN
    by_cases huv : u = v
    · subst huv
      exact SimpleGraph.Reachable.refl _
    · obtain ⟨l, hl⟩ := Function.ne_iff.mp huv
      set s : ℤ := if u l < v l then 1 else -1 with hs
      set u' : Site d := Function.update u l (u l + s) with hu'
      have hu'l : u' l = u l + s := by simp [hu']
      have hu'i : ∀ i, i ≠ l → u' i = u i := fun i hi => by simp [hu', hi]
      have hmem : u' ∈ pcloseBox m M := by
        intro i
        by_cases hi : i = l
        · subst hi
          rw [hu'l]
          have h1 := hu i
          have h2 := hv i
          by_cases hlt : u i < v i
          · simp only [hs, if_pos hlt]
            constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
          · simp only [hs, if_neg hlt]
            have : v i < u i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hl)
            constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        · rw [hu'i i hi]; exact hu i
      have hadj : (lattice d).Adj u u' := by
        by_cases hlt : u l < v l
        · refine ⟨l, Or.inl ?_⟩
          funext i
          by_cases hi : i = l
          · subst hi
            simp [hu'l, hs, hlt, glws_unit_apply]
          · simp [hu'i i hi, glws_unit_apply, hi]
        · refine ⟨l, Or.inr ?_⟩
          funext i
          by_cases hi : i = l
          · subst hi
            simp [hu'l, hs, hlt, glws_unit_apply]
          · simp [hu'i i hi, glws_unit_apply, hi]
      have hlt : mnorm (u' - v) < mnorm (u - v) := by
        unfold mnorm
        refine Finset.sum_lt_sum (fun i _ => ?_) ⟨l, Finset.mem_univ l, ?_⟩
        · by_cases hi : i = l
          · subst hi
            simp only [Pi.sub_apply, hu'l, hs]
            by_cases hlt : u i < v i
            · simp only [if_pos hlt]
              rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
              linarith
            · simp only [if_neg hlt]
              have : v i < u i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hl)
              rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
              linarith
          · simp [hu'i i hi]
        · simp only [Pi.sub_apply, hu'l, hs]
          by_cases hlt : u l < v l
          · simp only [if_pos hlt]
            rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
            linarith
          · simp only [if_neg hlt]
            have : v l < u l := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hl)
            rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
            linarith
      have hlt' : (mnorm (u' - v)).toNat < N := by
        rw [← hN]
        have h0 : 0 ≤ mnorm (u' - v) := by
          unfold mnorm; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
        omega
      have h1 := ih _ hlt' u' v hmem hv rfl
      refine SimpleGraph.Reachable.trans ?_ h1
      exact SimpleGraph.Adj.reachable (by simpa [SimpleGraph.induce_adj] using hadj)

/-- **Adjacent tiles contain adjacent sites.** -/
theorem glws_tile_adj_pts (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (i j : Site d)
    (hij : (lattice d).Adj i j) :
    ∃ u ∈ rboxShift k i, ∃ u' ∈ rboxShift k j, (lattice d).Adj u u' := by
  have hk1 : ∀ m, (1 : ℤ) ≤ (k m : ℤ) := fun m => by exact_mod_cast hk m
  obtain ⟨l, hl | hl⟩ := hij
  · -- `j = i + unit l`
    refine ⟨fun m => if m = l then (k l : ℤ) * i l + k l else 1 + (k m : ℤ) * i m, ?_,
      fun m => if m = l then (k l : ℤ) * i l + k l + 1 else 1 + (k m : ℤ) * i m, ?_, ?_⟩
    · intro m
      by_cases hm : m = l
      · subst hm
        simp only [if_true]
        have := hk1 m
        constructor <;> linarith
      · simp only [hm, if_false]
        have := hk1 m
        constructor <;> linarith
    · intro m
      have hj : j m = i m + (if m = l then 1 else 0) := by
        have := congrFun hl m
        simpa [glws_unit_apply] using this
      by_cases hm : m = l
      · subst hm
        simp only [if_true] at hj ⊢
        rw [hj]
        have := hk1 m
        have e : (k m : ℤ) * (i m + 1) = (k m : ℤ) * i m + k m := by ring
        rw [e]
        constructor <;> linarith
      · simp only [hm, if_false, add_zero] at hj ⊢
        rw [hj]
        have := hk1 m
        constructor <;> linarith
    · refine ⟨l, Or.inl ?_⟩
      funext m
      by_cases hm : m = l
      · subst hm
        simp [glws_unit_apply]
      · simp [glws_unit_apply, hm]
  · -- `i = j + unit l`
    refine ⟨fun m => if m = l then (k l : ℤ) * i l + 1 else 1 + (k m : ℤ) * i m, ?_,
      fun m => if m = l then (k l : ℤ) * i l else 1 + (k m : ℤ) * i m, ?_, ?_⟩
    · intro m
      by_cases hm : m = l
      · subst hm
        simp only [if_true]
        have := hk1 m
        constructor <;> linarith
      · simp only [hm, if_false]
        have := hk1 m
        constructor <;> linarith
    · intro m
      have hi : i m = j m + (if m = l then 1 else 0) := by
        have := congrFun hl m
        simpa [glws_unit_apply] using this
      by_cases hm : m = l
      · subst hm
        simp only [if_true] at hi ⊢
        have := hk1 m
        have e : (k m : ℤ) * i m = (k m : ℤ) * j m + k m := by rw [hi]; ring
        constructor <;> nlinarith
      · simp only [hm, if_false, add_zero] at hi ⊢
        rw [hi]
        have := hk1 m
        constructor <;> linarith
    · refine ⟨l, Or.inr ?_⟩
      funext m
      by_cases hm : m = l
      · subst hm
        simp [glws_unit_apply]
      · simp [glws_unit_apply, hm]

/-- Along a walk of macroscopic sites, the union of the tiles over a stretch of the walk is
connected inside any set containing it. -/
theorem glws_walk_reach (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (S : Set (Site d)) (c : ℕ → Site d)
    (s1 : ℕ) (s2 : ℕ) (hadj : ∀ s, s1 ≤ s → s < s2 → (lattice d).Adj (c s) (c (s + 1)))
    (hS : ∀ s, s1 ≤ s → s ≤ s2 → rboxShift k (c s) ⊆ S) :
    ∀ (q : ℕ) (hq : s1 + q ≤ s2) (u v : Site d) (hu : u ∈ rboxShift k (c s1))
      (hv : v ∈ rboxShift k (c (s1 + q))),
      ((lattice d).induce S).Reachable ⟨u, hS s1 le_rfl (by omega) hu⟩
        ⟨v, hS (s1 + q) (by omega) (by omega) hv⟩ := by
  intro q
  induction q with
  | zero =>
    intro hq u v hu hv
    exact glws_box_reach S _ _ (hS s1 le_rfl (by omega)) _ u v hu hv rfl
  | succ q ih =>
    intro hq u v hu hv
    obtain ⟨u0, hu0, u0', hu0', hadj0⟩ :=
      glws_tile_adj_pts k hk (c (s1 + q)) (c (s1 + q + 1)) (hadj (s1 + q) (by omega) (by omega))
    have h1 := ih (by omega) u u0 hu hu0
    have h2 : ((lattice d).induce S).Reachable
        ⟨u0, hS (s1 + q) (by omega) (by omega) hu0⟩
        ⟨u0', hS (s1 + (q + 1)) (by omega) (by omega) hu0'⟩ :=
      SimpleGraph.Adj.reachable (by simpa [SimpleGraph.induce_adj] using hadj0)
    have h3 := glws_box_reach S _ _ (hS (s1 + (q + 1)) (by omega) (by omega)) _ u0' v
      hu0' hv rfl
    exact (h1.trans h2).trans h3

/-- A path of distinct sites between two connected sites of a finite set, inside the set. -/
theorem glws_path_of_reach (S : Set (Site d)) (hSfin : S.Finite) {a b : Site d} (ha : a ∈ S)
    (hb : b ∈ S) (h : ((lattice d).induce S).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∃ (m : ℕ) (z : ℕ → Site d), z 0 = a ∧ z m = b ∧ (∀ i, i ≤ m → z i ∈ S) ∧
      (∀ i j, i ≤ m → j ≤ m → z i = z j → i = j) ∧
      (∀ i, i < m → (lattice d).Adj (z i) (z (i + 1))) ∧ m + 1 ≤ S.ncard := by
  classical
  obtain ⟨w⟩ := h
  set p := w.bypass with hp
  have hpath : p.IsPath := SimpleGraph.Walk.bypass_isPath w
  refine ⟨p.length, fun i => (p.getVert i).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp only
    rw [SimpleGraph.Walk.getVert_length]
  · intro i _
    exact (p.getVert i).2
  · intro i j hi hj hij
    have := hpath.getVert_injOn (show i ∈ {i | i ≤ p.length} from hi)
      (show j ∈ {i | i ≤ p.length} from hj) (Subtype.ext hij)
    exact this
  · intro i hi
    have := p.adj_getVert_succ hi
    simpa [SimpleGraph.induce_adj] using this
  · -- the number of vertices is at most the size of `S`
    set z : ℕ → Site d := fun i => (p.getVert i).1 with hz
    have hinj : Set.InjOn z {i : ℕ | i < p.length + 1} := by
      intro i hi j hj hij
      have hi' : i ≤ p.length := Nat.lt_succ_iff.mp hi
      have hj' : j ≤ p.length := Nat.lt_succ_iff.mp hj
      exact hpath.getVert_injOn hi' hj' (Subtype.ext hij)
    have hsub : z '' {i : ℕ | i < p.length + 1} ⊆ S := by
      rintro y ⟨i, hi, rfl⟩
      exact (p.getVert i).2
    have h1 := Set.ncard_le_ncard hsub hSfin
    rw [hinj.ncard_image] at h1
    have h2 : ({i : ℕ | i < p.length + 1} : Set ℕ).ncard = p.length + 1 := by
      have : ({i : ℕ | i < p.length + 1} : Set ℕ) = ↑(Finset.range (p.length + 1)) := by
        ext i; simp
      rw [this, Set.ncard_coe_finset, Finset.card_range]
    omega

end Exploding
