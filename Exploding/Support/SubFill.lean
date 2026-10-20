/-
The time bound of the filling lemma of Lemma 2.1 (`lemma:local_convexity` in `paper/corrected-arxiv/exploding-corrected-arxiv.tex`): on the
extremal background the terminal support of the frozen odometer is reached
within the cardinality of the bounding rectangle.  The paper's argument is that
the support grows by at least one site at every step until it saturates, and
that it never leaves the bounding rectangle.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubGeom
import Exploding.Support.SubBox

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### The support at a fixed time -/

/-- The support of the frozen odometer on the extremal background at time `t`. -/
def supp (A : Set (Site d)) (t : ℕ) : Set (Site d) :=
  {x | fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x = 1}

theorem supp_subset_fillSet (A : Set (Site d)) (t : ℕ) : supp A t ⊆ fillSet A :=
  fun _ hx => ⟨t, hx⟩

theorem supp_mono (A : Set (Site d)) (t : ℕ) : supp A t ⊆ supp A (t + 1) := by
  intro x hx
  have h1 := fodo_mono_time A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x
  have h2 := fodo_indicator_le_one A (t + 1) x
  simp only [supp, Set.mem_setOf_eq] at hx ⊢
  omega

theorem supp_le_of_le (A : Set (Site d)) {s t : ℕ} (h : s ≤ t) : supp A s ⊆ supp A t := by
  induction t, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ t _ ih => exact fun _ hx => supp_mono A t (ih hx)

theorem min_succ_le (t c : ℕ) : min (t + 1) c ≤ min t c + 1 := by
  rcases lt_or_ge (t + 1) c with h | h
  · rw [min_eq_left (le_of_lt h), min_eq_left (by omega : t ≤ c)]
  · rw [min_eq_right h]
    rcases lt_or_ge t c with h2 | h2
    · rw [min_eq_left (le_of_lt h2)]
      omega
    · rw [min_eq_right h2]
      omega

/-- The frozen odometer at the next time depends only on its value now. -/
theorem fodo_succ_congr (S : Set (Site d)) (s0 w0 : Site d → ℤ) {t t' : ℕ}
    (h : ∀ x, fodo S s0 w0 t x = fodo S s0 w0 t' x) (x : Site d) :
    fodo S s0 w0 (t + 1) x = fodo S s0 w0 (t' + 1) x := by
  rw [fodo_succ S s0 w0 t x, fodo_succ S s0 w0 t' x]
  by_cases hx : x ∈ S
  · rw [if_pos hx, if_pos hx]
  · rw [if_neg hx, if_neg hx]
    have hc : fconf S s0 w0 t x = fconf S s0 w0 t' x := by
      simp only [fconf, lap]
      rw [nbrSumZ_congr h x, h x]
    rw [hc, h x]

/-- If the frozen odometer does not change from `t` to `t + 1`, it never changes
again. -/
theorem fodo_eq_of_succ_eq (S : Set (Site d)) (s0 w0 : Site d → ℤ) {t : ℕ}
    (h : ∀ x, fodo S s0 w0 t x = fodo S s0 w0 (t + 1) x) :
    ∀ k x, fodo S s0 w0 (t + k) x = fodo S s0 w0 t x := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have h2 := fodo_succ_congr S s0 w0 (t := t + k) (t' := t) ih x
    have h3 : t + (k + 1) = t + k + 1 := rfl
    rw [h3, h2, ← h x]

/-- If the support does not grow from `t` to `t + 1`, it is already the terminal
support. -/
theorem supp_eq_of_succ_eq (A : Set (Site d)) (t : ℕ) (h : supp A t = supp A (t + 1)) :
    ∀ t' ≥ t, supp A t' = supp A t := by
  have hfun : ∀ x, fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x =
      fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) (t + 1) x := by
    intro x
    have hx : (x ∈ supp A t) ↔ (x ∈ supp A (t + 1)) := by rw [h]
    simp only [supp, Set.mem_setOf_eq] at hx
    have hle := fodo_indicator_le_one A t x
    have hmono := fodo_mono_time A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x
    have hle' := fodo_indicator_le_one A (t + 1) x
    have hnn := fodo_indicator_nonneg A t x
    have hnn' := fodo_indicator_nonneg A (t + 1) x
    omega
  intro t' ht'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht'
  ext x
  simp only [supp, Set.mem_setOf_eq]
  rw [fodo_eq_of_succ_eq A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) hfun k x]

/-! ### The filling never leaves the bounding rectangle -/

theorem mem_br_of_mem (A : Set (Site d)) {x : Site d} (hx : x ∈ A) : x ∈ br A :=
  fun _ => ⟨⟨x, hx, le_refl _⟩, ⟨x, hx, le_refl _⟩⟩

theorem unit_injective : Function.Injective (LatticeProb.unit : Fin d → Site d) := by
  intro i j h
  have h1 := congrFun h i
  simp only [LatticeProb.unit, Pi.single_eq_same] at h1
  by_contra hij
  rw [Pi.single_eq_of_ne hij] at h1
  exact one_ne_zero h1

theorem unit_ne_neg_unit (i j : Fin d) : LatticeProb.unit i ≠ -LatticeProb.unit j := by
  intro h
  have h1 := congrFun h i
  by_cases hij : i = j
  · subst hij
    simp only [LatticeProb.unit, Pi.single_eq_same, Pi.neg_apply] at h1
    norm_num at h1
  · simp only [LatticeProb.unit, Pi.single_eq_same, Pi.neg_apply,
      Pi.single_eq_of_ne hij] at h1
    norm_num at h1

theorem adj_coord_le {x y : Site d} (h : (lattice d).Adj y x) (i : Fin d) : y i ≤ x i + 1 := by
  obtain ⟨j, hj | hj⟩ := h
  · rw [hj]
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
    split_ifs with h1 <;> omega
  · rw [hj]
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
    split_ifs with h1 <;> omega

theorem adj_coord_ge {x y : Site d} (h : (lattice d).Adj y x) (i : Fin d) : x i - 1 ≤ y i := by
  obtain ⟨j, hj | hj⟩ := h
  · rw [hj]
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
    split_ifs with h1 <;> omega
  · rw [hj]
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
    split_ifs with h1 <;> omega

/-- A neighbour of `x` whose `i`-th coordinate exceeds `x`'s is `x + e_i`. -/
theorem eq_add_unit_of_coord {x y : Site d} (h : (lattice d).Adj y x) (i : Fin d)
    (hi : x i < y i) : y = x + LatticeProb.unit i := by
  obtain ⟨j, hj | hj⟩ := h
  · exfalso
    have h1 : y i ≤ x i := by
      rw [hj]
      simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
      split_ifs <;> omega
    omega
  · rw [hj] at hi ⊢
    have hji : j = i := by
      by_contra hne
      simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne (Ne.symm hne), add_zero] at hi
      omega
    rw [hji]

/-- A neighbour of `x` whose `i`-th coordinate is below `x`'s is `x - e_i`. -/
theorem eq_sub_unit_of_coord {x y : Site d} (h : (lattice d).Adj y x) (i : Fin d)
    (hi : y i < x i) : y = x - LatticeProb.unit i := by
  obtain ⟨j, hj | hj⟩ := h
  · rw [hj] at hi
    have hji : j = i := by
      by_contra hne
      simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne (Ne.symm hne), add_zero] at hi
      omega
    rw [hji] at hj
    rw [hj]
    abel
  · exfalso
    have h1 : x i ≤ y i := by
      rw [hj]
      simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
      split_ifs <;> omega
    omega

/-- A site with two distinct neighbours in the bounding rectangle is itself in
the bounding rectangle. -/
theorem br_of_two_nbrs (A : Set (Site d)) {x y z : Site d}
    (hy : y ∈ br A) (hz : z ∈ br A) (hyz : y ≠ z)
    (hxy : (lattice d).Adj y x) (hxz : (lattice d).Adj z x) : x ∈ br A := by
  intro i
  constructor
  · by_cases hyi : x i < y i
    · -- `y = x + e_i`; then `z` cannot also be above `x`, so `z i ≤ x i`
      have hy' : y = x + LatticeProb.unit i := eq_add_unit_of_coord hxy i hyi
      have hzi : ¬ x i < z i := by
        intro hzi
        exact hyz (by rw [hy', eq_add_unit_of_coord hxz i hzi])
      obtain ⟨a, ha, ha'⟩ := (hz i).1
      exact ⟨a, ha, le_trans ha' (le_of_not_gt hzi)⟩
    · obtain ⟨a, ha, ha'⟩ := (hy i).1
      exact ⟨a, ha, le_trans ha' (le_of_not_gt hyi)⟩
  · by_cases hyi : y i < x i
    · have hy' : y = x - LatticeProb.unit i := eq_sub_unit_of_coord hxy i hyi
      have hzi : ¬ z i < x i := by
        intro hzi
        exact hyz (by rw [hy', eq_sub_unit_of_coord hxz i hzi])
      obtain ⟨a, ha, ha'⟩ := (hz i).2
      exact ⟨a, ha, le_trans (le_of_not_gt hzi) ha'⟩
    · obtain ⟨a, ha, ha'⟩ := (hy i).2
      exact ⟨a, ha, le_trans (le_of_not_gt hyi) ha'⟩

/-- Two distinct neighbours of a site carry the value `1` when the neighbour sum
is at least `2` and the function is `{0,1}`-valued. -/
theorem exists_two_nbrs_of_nbrSumZ (u : Site d → ℤ) (hu : ∀ y, 0 ≤ u y) (hu1 : ∀ y, u y ≤ 1)
    (x : Site d) (h : 2 ≤ nbrSumZ u x) :
    ∃ y z : Site d, y ≠ z ∧ (lattice d).Adj y x ∧ (lattice d).Adj z x ∧ u y = 1 ∧ u z = 1 := by
  classical
  set A : Finset (Fin d) := Finset.univ.filter (fun i => u (x + LatticeProb.unit i) = 1) with hA
  set B : Finset (Fin d) := Finset.univ.filter (fun i => u (x - LatticeProb.unit i) = 1) with hB
  have hsum : nbrSumZ u x = (A.card : ℤ) + (B.card : ℤ) := by
    simp only [nbrSumZ]
    have h1 : ∀ i : Fin d, u (x + LatticeProb.unit i) = if i ∈ A then (1 : ℤ) else 0 := by
      intro i
      have h2 := hu (x + LatticeProb.unit i)
      have h3 := hu1 (x + LatticeProb.unit i)
      by_cases hi : i ∈ A
      · rw [if_pos hi]; exact (Finset.mem_filter.mp hi).2
      · rw [if_neg hi]
        have hne : u (x + LatticeProb.unit i) ≠ 1 :=
          fun hc => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)
        omega
    have h4 : ∀ i : Fin d, u (x - LatticeProb.unit i) = if i ∈ B then (1 : ℤ) else 0 := by
      intro i
      have h2 := hu (x - LatticeProb.unit i)
      have h3 := hu1 (x - LatticeProb.unit i)
      by_cases hi : i ∈ B
      · rw [if_pos hi]; exact (Finset.mem_filter.mp hi).2
      · rw [if_neg hi]
        have hne : u (x - LatticeProb.unit i) ≠ 1 :=
          fun hc => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)
        omega
    rw [Finset.sum_congr rfl (fun i _ => by rw [h1 i, h4 i]), Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_filter]
      simp [Finset.sum_const]
    · rw [← Finset.sum_filter]
      simp [Finset.sum_const]
  have h2 : 2 ≤ A.card + B.card := by
    rw [hsum] at h
    omega
  by_cases hAc : A.card ≤ 1
  · by_cases hBc : B.card ≤ 1
    · -- both are exactly `1`
      have hAe : A.card = 1 := by omega
      have hBe : B.card = 1 := by omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hAe
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hBe
      have hiA : i ∈ A := by rw [hi]; exact Finset.mem_singleton_self i
      have hjB : j ∈ B := by rw [hj]; exact Finset.mem_singleton_self j
      refine ⟨x + LatticeProb.unit i, x - LatticeProb.unit j, ?_,
        ⟨i, Or.inr (by abel)⟩, ⟨j, Or.inl (by abel)⟩,
        (Finset.mem_filter.mp hiA).2, (Finset.mem_filter.mp hjB).2⟩
      intro hcon
      apply unit_ne_neg_unit i j
      have h1 : (x + LatticeProb.unit i) - x = LatticeProb.unit i := by abel
      have h2' : (x - LatticeProb.unit j) - x = -LatticeProb.unit j := by abel
      rw [hcon, h2'] at h1
      exact h1.symm
    · -- `B` has at least two elements
      obtain ⟨i, hiB, j, hjB, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
      refine ⟨x - LatticeProb.unit i, x - LatticeProb.unit j, ?_,
        ⟨i, Or.inl (by abel)⟩, ⟨j, Or.inl (by abel)⟩,
        (Finset.mem_filter.mp hiB).2, (Finset.mem_filter.mp hjB).2⟩
      intro hcon
      apply hij
      have h1 : (x - LatticeProb.unit i) - x = -LatticeProb.unit i := by abel
      have h2' : (x - LatticeProb.unit j) - x = -LatticeProb.unit j := by abel
      rw [hcon, h2'] at h1
      exact unit_injective (neg_injective h1.symm)
  · -- `A` has at least two elements
    obtain ⟨i, hiA, j, hjA, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    refine ⟨x + LatticeProb.unit i, x + LatticeProb.unit j, ?_,
      ⟨i, Or.inr (by abel)⟩, ⟨j, Or.inr (by abel)⟩,
      (Finset.mem_filter.mp hiA).2, (Finset.mem_filter.mp hjA).2⟩
    intro hcon
    apply hij
    have h1 : (x + LatticeProb.unit i) - x = LatticeProb.unit i := by abel
    have h2' : (x + LatticeProb.unit j) - x = LatticeProb.unit j := by abel
    rw [hcon, h2'] at h1
    exact unit_injective h1.symm

/-- The terminal support of the frozen odometer on the extremal background is
contained in the bounding rectangle of its seed. -/
theorem supp_subset_br (A : Set (Site d)) (t : ℕ) : supp A t ⊆ br A := by
  induction t with
  | zero =>
    intro x hx
    simp only [supp, Set.mem_setOf_eq, fodo_zero] at hx
    exact mem_br_of_mem A (by
      by_contra h
      rw [Set.indicator_of_notMem h] at hx
      exact one_ne_zero hx.symm)
  | succ t ih =>
    intro x hx
    simp only [supp, Set.mem_setOf_eq] at hx
    rw [fodo_succ] at hx
    by_cases hxA : x ∈ A
    · exact mem_br_of_mem A hxA
    · rw [if_neg hxA] at hx
      by_cases hc : 2 * (d : ℤ) ≤ fconf A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x
      · rw [if_pos hc] at hx
        have h0 : fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x = 0 := by
          have := fodo_indicator_le_one A t x
          omega
        simp only [fconf, lap, h0, mul_zero, sub_zero] at hc
        have h2 : 2 ≤ nbrSumZ (fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t) x := by
          linarith
        obtain ⟨y, z, hyz, hxy, hxz, hy1, hz1⟩ :=
          exists_two_nbrs_of_nbrSumZ
            (u := fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t)
            (fun y => fodo_indicator_nonneg A t y)
            (fun y => fodo_indicator_le_one A t y) x h2
        exact br_of_two_nbrs A (ih hy1) (ih hz1) hyz hxy hxz
      · rw [if_neg hc] at hx
        have hx' : fodo A (fun _ => 2 * (d : ℤ) - 2) (Set.indicator A 1) t x = 1 := by
          simpa using hx
        exact ih hx'

/-- The terminal support of the frozen odometer on the extremal background is
contained in the bounding rectangle of its seed. -/
theorem fillSet_subset_br (A : Set (Site d)) : fillSet A ⊆ br A := by
  intro x hx
  obtain ⟨t, ht⟩ := hx
  exact supp_subset_br A t ht

/-- The terminal support is reached within the cardinality of the bounding
rectangle: the support grows by at least one site at every step until it
saturates, and it never leaves the rectangle. -/
theorem br_subset_supp_card (A : Set (Site d)) (hfin : (br A).Finite)
    (hbr : br A ⊆ fillSet A) : br A ⊆ supp A hfin.toFinset.card := by
  classical
  have hsub : fillSet A ⊆ br A := fillSet_subset_br A
  have hmem : ∀ t, ∀ x ∈ br A, x ∈ supp A t → x ∈ hfin.toFinset :=
    fun t x _ _ => hfin.mem_toFinset.mpr ‹x ∈ br A›
  have hcard : ∀ t, (hfin.toFinset.filter (fun x => x ∈ supp A t)).card ≤ hfin.toFinset.card :=
    fun t => Finset.card_filter_le _ _
  have hmono : ∀ t, (hfin.toFinset.filter (fun x => x ∈ supp A t)).card ≤
      (hfin.toFinset.filter (fun x => x ∈ supp A (t + 1))).card := by
    intro t
    refine Finset.card_le_card ?_
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, supp_mono A t hx.2⟩
  have hgrow : ∀ t, (hfin.toFinset.filter (fun x => x ∈ supp A t)).card < hfin.toFinset.card →
      (hfin.toFinset.filter (fun x => x ∈ supp A t)).card + 1 ≤
        (hfin.toFinset.filter (fun x => x ∈ supp A (t + 1))).card := by
    intro t ht
    by_contra hcon
    have hcon' : (hfin.toFinset.filter (fun x => x ∈ supp A (t + 1))).card ≤
        (hfin.toFinset.filter (fun x => x ∈ supp A t)).card := by omega
    have heq : (hfin.toFinset.filter (fun x => x ∈ supp A t)).card =
        (hfin.toFinset.filter (fun x => x ∈ supp A (t + 1))).card :=
      le_antisymm (hmono t) hcon'
    have hset : hfin.toFinset.filter (fun x => x ∈ supp A t) =
        hfin.toFinset.filter (fun x => x ∈ supp A (t + 1)) :=
      Finset.eq_of_subset_of_card_le (by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, supp_mono A t hx.2⟩) (le_of_eq heq.symm)
    have hsupp : supp A t = supp A (t + 1) := by
      refine Set.Subset.antisymm (supp_mono A t) ?_
      intro x hx
      have hxbr : x ∈ br A := hsub (supp_subset_fillSet A (t + 1) hx)
      have h1 : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr hxbr
      have h2 : x ∈ hfin.toFinset.filter (fun x => x ∈ supp A (t + 1)) :=
        Finset.mem_filter.mpr ⟨h1, hx⟩
      rw [← hset] at h2
      exact (Finset.mem_filter.mp h2).2
    have hfill : supp A t = fillSet A := by
      refine Set.Subset.antisymm (supp_subset_fillSet A t) ?_
      intro x hx
      obtain ⟨t', ht'⟩ := hx
      have hmem : x ∈ supp A t' := ht'
      rcases lt_or_ge t t' with hlt | hle
      · have h1 : supp A t' = supp A t := supp_eq_of_succ_eq A t hsupp t' (le_of_lt hlt)
        rw [h1] at hmem
        exact hmem
      · exact supp_le_of_le A hle hmem
    have hlt2 : (hfin.toFinset.filter (fun x => x ∈ supp A t)).card < hfin.toFinset.card := by
      simpa only [hfill] using ht
    obtain ⟨x, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt2
    rw [Finset.mem_filter] at hx
    exact hx.2 ⟨hx.1, by
      rw [hfill]
      exact hbr (hfin.mem_toFinset.mp hx.1)⟩
  have hkey : ∀ t, min t hfin.toFinset.card ≤
      (hfin.toFinset.filter (fun x => x ∈ supp A t)).card := by
    intro t
    induction t with
    | zero => exact Nat.zero_le _
    | succ t ih =>
      rcases lt_or_ge (hfin.toFinset.filter (fun x => x ∈ supp A t)).card hfin.toFinset.card with
        hlt | hge
      · have := hgrow t hlt
        have h1 : min t hfin.toFinset.card + 1 ≤
            (hfin.toFinset.filter (fun x => x ∈ supp A (t + 1))).card := by omega
        exact le_trans (min_succ_le t hfin.toFinset.card) h1
      · have h1 : hfin.toFinset.card ≤
            (hfin.toFinset.filter (fun x => x ∈ supp A (t + 1))).card :=
          le_trans hge (hmono t)
        exact le_trans (min_le_right _ _) h1
  intro x hx
  have h1 := hkey hfin.toFinset.card
  rw [min_self] at h1
  have h2 : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr hx
  have h3 : x ∈ hfin.toFinset.filter (fun x => x ∈ supp A hfin.toFinset.card) := by
    by_contra hcon
    have h4 : (hfin.toFinset.filter (fun x => x ∈ supp A hfin.toFinset.card)).card <
        hfin.toFinset.card := by
      refine Finset.card_lt_card ?_
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨Finset.filter_subset _ _, fun heq => hcon (heq.symm ▸ h2)⟩
    omega
  exact (Finset.mem_filter.mp h3).2

end Exploding
