import Exploding.Support.Vocab

/-!
# Bounding rectangles of paths

The bounding rectangle of a finite path, in the form the local-convexity
argument of `paper/exploding.tex` uses it: the coordinatewise minimum and
maximum of the first `j+1` points of a path, the identification of the
bounding rectangle `br` of the path's image with the box they define, and the
fact that a point of the box off the path has a neighbour in the box.
-/
namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The minimum of `z k i` over `k ≤ j`. -/
def bmin (z : ℕ → Site d) (j : ℕ) (i : Fin d) : ℤ :=
  (Finset.range (j + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩ (fun k => z k i)

/-- The maximum of `z k i` over `k ≤ j`. -/
def bmax (z : ℕ → Site d) (j : ℕ) (i : Fin d) : ℤ :=
  (Finset.range (j + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩ (fun k => z k i)

/-- The bounding box of the first `j+1` points of the path. -/
def box (z : ℕ → Site d) (j : ℕ) : Set (Site d) :=
  {p | ∀ i, bmin z j i ≤ p i ∧ p i ≤ bmax z j i}

/-- The minimum is a lower bound for the path's coordinates. -/
theorem bmin_le (z : ℕ → Site d) (j : ℕ) (i : Fin d) {k : ℕ} (hk : k ≤ j) :
    bmin z j i ≤ z k i :=
  Finset.inf'_le (fun k => z k i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- The maximum is an upper bound for the path's coordinates. -/
theorem le_bmax (z : ℕ → Site d) (j : ℕ) (i : Fin d) {k : ℕ} (hk : k ≤ j) :
    z k i ≤ bmax z j i :=
  Finset.le_sup' (fun k => z k i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- The minimum is attained on the path. -/
theorem bmin_attained (z : ℕ → Site d) (j : ℕ) (i : Fin d) :
    ∃ k ≤ j, z k i = bmin z j i := by
  have hne : (Finset.range (j + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
  obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_eq_inf' hne (fun k => z k i)
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hk'.symm⟩

/-- The maximum is attained on the path. -/
theorem bmax_attained (z : ℕ → Site d) (j : ℕ) (i : Fin d) :
    ∃ k ≤ j, z k i = bmax z j i := by
  have hne : (Finset.range (j + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
  obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_eq_sup' hne (fun k => z k i)
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hk'.symm⟩

/-- The bounding rectangle of the first `j+1` points of the path is the box
their coordinatewise extrema define. -/
theorem br_image_eq_box (z : ℕ → Site d) (j : ℕ) :
    br (z '' {i : ℕ | i ≤ j}) = box z j := by
  ext p
  simp only [br, Set.mem_setOf_eq, Set.mem_image, box]
  constructor
  · intro h i
    obtain ⟨⟨y, hy, hyi⟩, ⟨y', hy', hy'i⟩⟩ := h i
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨k', hk', rfl⟩ := hy'
    exact ⟨le_trans (bmin_le z j i hk) hyi, le_trans hy'i (le_bmax z j i hk')⟩
  · intro h i
    obtain ⟨k, hk, hk'⟩ := bmin_attained z j i
    obtain ⟨k', hk'', hk'''⟩ := bmax_attained z j i
    exact ⟨⟨z k, ⟨k, hk, rfl⟩, by rw [hk']; exact (h i).1⟩,
      ⟨z k', ⟨k', hk'', rfl⟩, by rw [hk''']; exact (h i).2⟩⟩

/-- The `j+1`-st point of a path lies in the box of the first `j+2` points. -/
theorem path_mem_box_succ (z : ℕ → Site d) (j : ℕ) : z (j + 1) ∈ box z (j + 1) := by
  intro i
  exact ⟨bmin_le z (j + 1) i (Nat.le_refl (j + 1)),
    le_bmax z (j + 1) i (Nat.le_refl (j + 1))⟩

/-- The box of the first `j+2` points contains the box of the first `j+1`. -/
theorem box_mono (z : ℕ → Site d) (j : ℕ) : box z j ⊆ box z (j + 1) := by
  intro p hp i
  have h1 : bmin z (j + 1) i ≤ bmin z j i := by
    show (Finset.range (j + 1 + 1)).inf' _ (fun k => z k i) ≤
      (Finset.range (j + 1)).inf' _ (fun k => z k i)
    rw [Finset.le_inf'_iff]
    intro k hk
    have hk' : k ≤ j + 1 := by
      have := Finset.mem_range.mp hk
      omega
    exact bmin_le z (j + 1) i hk'
  have h2 : bmax z j i ≤ bmax z (j + 1) i := by
    show (Finset.range (j + 1)).sup' _ (fun k => z k i) ≤
      (Finset.range (j + 1 + 1)).sup' _ (fun k => z k i)
    rw [Finset.sup'_le_iff]
    intro k hk
    have hk' : k ≤ j + 1 := by
      have := Finset.mem_range.mp hk
      omega
    exact le_bmax z (j + 1) i hk'
  exact ⟨le_trans h1 (hp i).1, le_trans (hp i).2 h2⟩

/-- A point of the bounding box of a path that is not on the path has a
neighbour in the box. -/
theorem box_point_has_nbr (m : ℕ) (z : ℕ → Site d) (p : Site d)
    (hp : p ∈ br (z '' {i : ℕ | i ≤ m})) (hnot : p ∉ z '' {i : ℕ | i ≤ m}) :
    ∃ q ∈ br (z '' {i : ℕ | i ≤ m}), (lattice d).Adj q p := by
  by_contra hcon
  have hcon' : ∀ q ∈ br (z '' {i : ℕ | i ≤ m}), ¬ (lattice d).Adj q p := by
    intro q hq h
    exact hcon ⟨q, hq, h⟩
  clear hcon
  apply hnot
  have hA : ∀ y ∈ z '' {i : ℕ | i ≤ m}, y = p := by
    intro y hy
    funext i
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem : p - unit i ∈ br (z '' {i : ℕ | i ≤ m}) := by
        intro j
        constructor
        · by_cases hji : j = i
          · subst hji
            exact ⟨y, hy, by simp [LatticeProb.unit, Pi.sub_apply]; omega⟩
          · obtain ⟨y', hy', hle⟩ := (hp j).1
            exact ⟨y', hy', by simpa [LatticeProb.unit, Pi.sub_apply, hji, Ne.symm hji] using hle⟩
        · by_cases hji : j = i
          · subst hji
            obtain ⟨y', hy', hle⟩ := (hp j).2
            exact ⟨y', hy', by simp [LatticeProb.unit, Pi.sub_apply]; omega⟩
          · obtain ⟨y', hy', hle⟩ := (hp j).2
            exact ⟨y', hy', by simpa [LatticeProb.unit, Pi.sub_apply, hji, Ne.symm hji] using hle⟩
      exact hcon' (p - unit i) hmem ⟨i, Or.inl (by simp [sub_add_cancel])⟩
    · have hmem : p + unit i ∈ br (z '' {i : ℕ | i ≤ m}) := by
        intro j
        constructor
        · by_cases hji : j = i
          · subst hji
            obtain ⟨y', hy', hle⟩ := (hp j).1
            exact ⟨y', hy', by simp [LatticeProb.unit, Pi.add_apply]; omega⟩
          · obtain ⟨y', hy', hle⟩ := (hp j).1
            exact ⟨y', hy', by simpa [LatticeProb.unit, Pi.add_apply, hji, Ne.symm hji] using hle⟩
        · by_cases hji : j = i
          · subst hji
            exact ⟨y, hy, by simp [LatticeProb.unit, Pi.add_apply]; omega⟩
          · obtain ⟨y', hy', hle⟩ := (hp j).2
            exact ⟨y', hy', by simpa [LatticeProb.unit, Pi.add_apply, hji, Ne.symm hji] using hle⟩
      exact hcon' (p + unit i) hmem ⟨i, Or.inr rfl⟩
  have hz : z 0 ∈ z '' {i : ℕ | i ≤ m} := ⟨0, Nat.zero_le m, rfl⟩
  exact (hA (z 0) hz) ▸ hz

/-- A point of the bounding box of a nonempty set that is not in the set has a
neighbour in the box. -/
theorem br_has_nbr (A : Set (Site d)) (i : Fin d) {p : Site d}
    (hp : p ∈ br A) (hnot : p ∉ A) :
    ∃ q ∈ br A, (lattice d).Adj q p := by
  by_contra hcon
  have hcon' : ∀ q ∈ br A, ¬ (lattice d).Adj q p := fun q hq h => hcon ⟨q, hq, h⟩
  clear hcon
  apply hnot
  have hA' : ∀ y ∈ A, y = p := by
    intro y hy
    funext i
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem : p - unit i ∈ br A := by
        intro j
        constructor
        · by_cases hji : j = i
          · rw [hji]
            refine ⟨y, hy, ?_⟩
            have h1 : (p - unit i) i = p i - 1 := by
              simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same]
            have h2 : y i ≤ p i - 1 := by omega
            rw [h1]
            exact h2
          · obtain ⟨y', hy', hle⟩ := (hp j).1
            refine ⟨y', hy', ?_⟩
            have h1 : (p - unit i) j = p j := by
              simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_of_ne hji, sub_zero]
            rw [h1]
            exact hle
        · by_cases hji : j = i
          · rw [hji]
            obtain ⟨y', hy', hle⟩ := (hp i).2
            refine ⟨y', hy', ?_⟩
            have h1 : (p - unit i) i = p i - 1 := by
              simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same]
            rw [h1]
            omega
          · obtain ⟨y', hy', hle⟩ := (hp j).2
            refine ⟨y', hy', ?_⟩
            have h1 : (p - unit i) j = p j := by
              simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_of_ne hji, sub_zero]
            rw [h1]
            exact hle
      have hadj : (lattice d).Adj (p - unit i) p := ⟨i, Or.inl (by abel)⟩
      exact hcon' _ hmem hadj
    · have hmem : p + unit i ∈ br A := by
        intro j
        constructor
        · by_cases hji : j = i
          · rw [hji]
            obtain ⟨y', hy', hle⟩ := (hp i).1
            refine ⟨y', hy', ?_⟩
            have h1 : (p + unit i) i = p i + 1 := by
              simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
            rw [h1]
            omega
          · obtain ⟨y', hy', hle⟩ := (hp j).1
            refine ⟨y', hy', ?_⟩
            have h1 : (p + unit i) j = p j := by
              simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne hji, add_zero]
            rw [h1]
            exact hle
        · by_cases hji : j = i
          · rw [hji]
            refine ⟨y, hy, ?_⟩
            have h1 : (p + unit i) i = p i + 1 := by
              simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
            have h2 : p i + 1 ≤ y i := by omega
            rw [h1]
            exact h2
          · obtain ⟨y', hy', hle⟩ := (hp j).2
            refine ⟨y', hy', ?_⟩
            have h1 : (p + unit i) j = p j := by
              simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne hji, add_zero]
            rw [h1]
            exact hle
      have hadj : (lattice d).Adj (p + unit i) p := ⟨i, Or.inr (by abel)⟩
      exact hcon' _ hmem hadj
  obtain ⟨y, hy, _⟩ := (hp i).1
  have hy' : y = p := hA' y hy
  rw [← hy']
  exact hy

/-- The bounding box of a finite set is finite. -/
theorem br_finite (A : Set (Site d)) (hA : A.Finite) : (br A).Finite := by
  classical
  have hsub : br A ⊆ {z | ∀ i, (∃ y ∈ A, y i ≤ z i) ∧ (∃ y ∈ A, z i ≤ y i)} :=
    fun z hz => hz
  refine Set.Finite.subset ?_ hsub
  have hset : {z : Site d | ∀ i, (∃ y ∈ A, y i ≤ z i) ∧ (∃ y ∈ A, z i ≤ y i)} =
      {z | ∀ i, z i ∈ ⋃ y ∈ A, ⋃ y' ∈ A, Set.Icc (y i) (y' i)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc]
    constructor
    · intro h i
      obtain ⟨⟨y1, hy1, h1⟩, ⟨y2, hy2, h2⟩⟩ := h i
      exact ⟨y1, hy1, y2, hy2, h1, h2⟩
    · intro h i
      obtain ⟨y1, hy1, y2, hy2, h1, h2⟩ := h i
      exact ⟨⟨y1, hy1, h1⟩, ⟨y2, hy2, h2⟩⟩
  rw [hset]
  refine Set.Finite.pi' fun i => ?_
  refine Set.Finite.biUnion hA fun y _ => ?_
  exact Set.Finite.biUnion hA fun y' _ => Set.finite_Icc (y i) (y' i)

/-- A point of the bounding box of a finite set that is not in the set has two
distinct neighbours in the box. -/
theorem br_two_nbrs (A : Set (Site d)) (hA : A.Finite) (i0 : Fin d) {p : Site d}
    (hp : p ∈ br A) (hnot : p ∉ A) :
    ∃ q ∈ br A, ∃ z ∈ br A, (lattice d).Adj q p ∧ (lattice d).Adj z p ∧ q ≠ z := by
  classical
  have hne : (hA.toFinset).Nonempty := by
    obtain ⟨y, hy, _⟩ := (hp i0).1
    exact ⟨y, hA.mem_toFinset.mpr hy⟩
  choose m hmA hm using fun i : Fin d =>
    Finset.exists_min_image hA.toFinset (fun y => y i) hne
  choose M hMA hM using fun i : Fin d =>
    Finset.exists_max_image hA.toFinset (fun y => y i) hne
  have hmA' : ∀ i, m i ∈ A := fun i => hA.mem_toFinset.mp (hmA i)
  have hMA' : ∀ i, M i ∈ A := fun i => hA.mem_toFinset.mp (hMA i)
  have hmle : ∀ i y, y ∈ A → m i i ≤ y i := fun i y hy => hm i y (hA.mem_toFinset.mpr hy)
  have hMle : ∀ i y, y ∈ A → y i ≤ M i i := fun i y hy => hM i y (hA.mem_toFinset.mpr hy)
  -- the box is the product of the coordinatewise intervals
  have hbox : br A = {x | ∀ i, m i i ≤ x i ∧ x i ≤ M i i} := by
    ext x
    constructor
    · intro hx i
      obtain ⟨⟨y1, hy1, h1⟩, ⟨y2, hy2, h2⟩⟩ := hx i
      exact ⟨le_trans (hmle i y1 hy1) h1, le_trans h2 (hMle i y2 hy2)⟩
    · intro hx i
      exact ⟨⟨m i, hmA' i, (hx i).1⟩, ⟨M i, hMA' i, (hx i).2⟩⟩
  have hpbox : ∀ i, m i i ≤ p i ∧ p i ≤ M i i := by
    rw [hbox] at hp
    exact hp
  -- `p - e_i` is in the box when `m i i < p i`
  have hdown : ∀ i, m i i < p i → p - unit i ∈ br A := by
    intro i hi
    rw [hbox]
    intro j
    constructor
    · by_cases hji : j = i
      · rw [hji]
        have h1 : (p - unit i) i = p i - 1 := by
          simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same]
        have h2 : m i i ≤ p i - 1 := by linarith [(hpbox i).1, hi]
        rw [h1]; exact h2
      · have h1 : (p - unit i) j = p j := by
          simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_of_ne hji, sub_zero]
        rw [h1]; exact (hpbox j).1
    · by_cases hji : j = i
      · rw [hji]
        have h1 : (p - unit i) i = p i - 1 := by
          simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same]
        have h2 : p i - 1 ≤ M i i := by linarith [(hpbox i).2]
        rw [h1]; exact h2
      · have h1 : (p - unit i) j = p j := by
          simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_of_ne hji, sub_zero]
        rw [h1]; exact (hpbox j).2
  -- `p + e_i` is in the box when `p i < M i i`
  have hup : ∀ i, p i < M i i → p + unit i ∈ br A := by
    intro i hi
    rw [hbox]
    intro j
    constructor
    · by_cases hji : j = i
      · rw [hji]
        have h1 : (p + unit i) i = p i + 1 := by
          simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
        have h2 : m i i ≤ p i + 1 := by linarith [(hpbox i).1]
        rw [h1]; exact h2
      · have h1 : (p + unit i) j = p j := by
          simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne hji, add_zero]
        rw [h1]; exact (hpbox j).1
    · by_cases hji : j = i
      · rw [hji]
        have h1 : (p + unit i) i = p i + 1 := by
          simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
        have h2 : p i + 1 ≤ M i i := by linarith [(hpbox i).2, hi]
        rw [h1]; exact h2
      · have h1 : (p + unit i) j = p j := by
          simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne hji, add_zero]
        rw [h1]; exact (hpbox j).2
  -- the two neighbours are distinct
  have hne' : ∀ i : Fin d, p - unit i ≠ p + unit i := by
    intro i hcon
    have := congrFun hcon i
    simp only [Pi.sub_apply, Pi.add_apply, LatticeProb.unit, Pi.single_eq_same] at this
    omega
  -- case 1: some coordinate is strictly inside
  by_cases h1 : ∃ i : Fin d, m i i < p i ∧ p i < M i i
  · obtain ⟨i, hlo, hhi⟩ := h1
    exact ⟨p - unit i, hdown i hlo, p + unit i, hup i hhi,
      ⟨i, Or.inl (by abel)⟩, ⟨i, Or.inr (by abel)⟩, hne' i⟩
  push Not at h1
  -- case 2: two distinct free coordinates
  by_cases h2 : ∃ i j : Fin d, i ≠ j ∧ (m i i < p i ∨ p i < M i i) ∧
      (m j j < p j ∨ p j < M j j)
  · obtain ⟨i, j, hij, hi, hj⟩ := h2
    have hqi : p - unit i ∈ br A ∨ p + unit i ∈ br A := by
      rcases hi with h | h
      · exact Or.inl (hdown i h)
      · exact Or.inr (hup i h)
    have hqj : p - unit j ∈ br A ∨ p + unit j ∈ br A := by
      rcases hj with h | h
      · exact Or.inl (hdown j h)
      · exact Or.inr (hup j h)
    rcases hqi with hqi | hqi <;> rcases hqj with hqj | hqj
    · refine ⟨p - unit i, hqi, p - unit j, hqj, ⟨i, Or.inl (by abel)⟩,
        ⟨j, Or.inl (by abel)⟩, ?_⟩
      intro hcon
      have := congrFun hcon i
      simp only [Pi.sub_apply, LatticeProb.unit, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, sub_zero] at this
      omega
    · refine ⟨p - unit i, hqi, p + unit j, hqj, ⟨i, Or.inl (by abel)⟩,
        ⟨j, Or.inr (by abel)⟩, ?_⟩
      intro hcon
      have := congrFun hcon i
      simp only [Pi.sub_apply, Pi.add_apply, LatticeProb.unit, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, add_zero] at this
      omega
    · refine ⟨p + unit i, hqi, p - unit j, hqj, ⟨i, Or.inr (by abel)⟩,
        ⟨j, Or.inl (by abel)⟩, ?_⟩
      intro hcon
      have := congrFun hcon i
      simp only [Pi.sub_apply, Pi.add_apply, LatticeProb.unit, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, sub_zero] at this
      omega
    · refine ⟨p + unit i, hqi, p + unit j, hqj, ⟨i, Or.inr (by abel)⟩,
        ⟨j, Or.inr (by abel)⟩, ?_⟩
      intro hcon
      have := congrFun hcon i
      simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, add_zero] at this
      omega
  push Not at h2
  -- case 3: at most one free coordinate
  by_cases h3 : ∃ i : Fin d, m i i < p i ∨ p i < M i i
  · obtain ⟨i, hi⟩ := h3
    -- every other coordinate is pinned
    have hpin : ∀ j, j ≠ i → m j j = p j ∧ p j = M j j := by
      intro j hji
      have h2j := h2 i j (Ne.symm hji) hi
      have h1' : p j ≤ m j j := h2j.1
      have h2' : M j j ≤ p j := h2j.2
      exact ⟨le_antisymm (hpbox j).1 h1', le_antisymm (hpbox j).2 h2'⟩
    -- every element of `A` has coordinate `p j` in a pinned coordinate `j`
    have hpin' : ∀ j, j ≠ i → ∀ y ∈ A, y j = p j := by
      intro j hji y hy
      have h1j := (hpin j hji).1
      have h2j := (hpin j hji).2
      exact le_antisymm (le_trans (hMle j y hy) (le_of_eq h2j.symm))
        (le_trans (le_of_eq h1j.symm) (hmle j y hy))
    -- `p` is one of the two extremal points of `A`
    have hpA : p ∈ A := by
      rcases hi with hlo | hhi
      · -- `m i i < p i`, so `p i = M i i` and `M i = p`
        have hMi : M i i = p i := by
          have h' : ¬(p i < M i i) := not_lt.mpr (h1 i hlo)
          exact le_antisymm (not_lt.mp h') (hpbox i).2
        have hMp : M i = p := by
          funext j
          by_cases hji : j = i
          · subst hji
            exact hMi
          · exact hpin' j hji (M i) (hMA' i)
        rw [← hMp]
        exact hMA' i
      · -- `p i < M i i`, so `p i = m i i` and `m i = p`
        have hmi : m i i = p i := by
          have h' : ¬(m i i < p i) := fun hc => absurd hhi (not_lt.mpr (h1 i hc))
          exact le_antisymm (hpbox i).1 (not_lt.mp h')
        have hmp : m i = p := by
          funext j
          by_cases hji : j = i
          · subst hji
            exact hmi
          · exact hpin' j hji (m i) (hmA' i)
        rw [← hmp]
        exact hmA' i
    exact absurd hpA hnot
  · -- no free coordinate: the box is a single point, which must be `p`
    have hall : ∀ j, m j j = p j ∧ p j = M j j := by
      intro j
      have h : ¬(m j j < p j ∨ p j < M j j) := not_exists.mp h3 j
      rw [not_or, not_lt, not_lt] at h
      exact ⟨le_antisymm (hpbox j).1 h.1, le_antisymm (hpbox j).2 h.2⟩
    have hboxp : br A = {p} := by
      rw [hbox]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hx
        funext j
        have h1 := (hall j).1
        have h2 := (hall j).2
        exact le_antisymm (le_trans (hx j).2 (le_of_eq h2.symm)) (le_trans (le_of_eq h1.symm) (hx j).1)
      · intro hx
        rw [hx]
        intro j
        exact ⟨le_of_eq (hall j).1, le_of_eq (hall j).2⟩
    have hpA : p ∈ A := by
      obtain ⟨y, hy, _⟩ := (hp i0).1
      have hyb : y ∈ br A := fun i => ⟨⟨y, hy, le_rfl⟩, ⟨y, hy, le_rfl⟩⟩
      rw [hboxp] at hyb
      have hyp : y = p := by simpa using hyb
      rw [hyp] at hy
      exact hy
    exact absurd hpA hnot

/-- The coordinatewise extrema of a finite nonempty set, as a box. -/
theorem br_eq_box (A : Set (Site d)) (hA : A.Finite) (hne : A.Nonempty) :
    ∃ m M : Site d, (∀ i, m i ∈ (fun y => y i) '' A) ∧ (∀ i, M i ∈ (fun y => y i) '' A) ∧
      br A = {x | ∀ i, m i ≤ x i ∧ x i ≤ M i} := by
  classical
  have hne' : (hA.toFinset).Nonempty := hA.toFinset_nonempty.mpr hne
  have hmin : ∀ i : Fin d, ∃ y ∈ A, ∀ y' ∈ A, y i ≤ y' i := by
    intro i
    obtain ⟨y, hy, hle⟩ := Finset.exists_min_image hA.toFinset (fun y => y i) hne'
    exact ⟨y, hA.mem_toFinset.mp hy, fun y' hy' => hle y' (hA.mem_toFinset.mpr hy')⟩
  have hmax : ∀ i : Fin d, ∃ y ∈ A, ∀ y' ∈ A, y' i ≤ y i := by
    intro i
    obtain ⟨y, hy, hle⟩ := Finset.exists_max_image hA.toFinset (fun y => y i) hne'
    exact ⟨y, hA.mem_toFinset.mp hy, fun y' hy' => hle y' (hA.mem_toFinset.mpr hy')⟩
  choose m hmA hm using hmin
  choose M hMA hM using hmax
  refine ⟨fun i => m i i, fun i => M i i,
    fun i => ⟨m i, hmA i, rfl⟩, fun i => ⟨M i, hMA i, rfl⟩, ?_⟩
  ext x
  constructor
  · intro hx i
    obtain ⟨⟨y1, hy1, h1⟩, ⟨y2, hy2, h2⟩⟩ := hx i
    exact ⟨le_trans (hm i y1 hy1) h1, le_trans h2 (hM i y2 hy2)⟩
  · intro hx i
    exact ⟨⟨m i, hmA i, (hx i).1⟩, ⟨M i, hMA i, (hx i).2⟩⟩

/-- The maximum over `range (j+2)` is the maximum of the maximum over
`range (j+1)` and the value at `j+1`. -/
theorem bmax_succ (z : ℕ → Site d) (j : ℕ) (i : Fin d) :
    bmax z (j + 1) i = max (bmax z j i) (z (j + 1) i) := by
  have hne : (Finset.range (j + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
  have hne' : (Finset.range (j + 1 + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos (j + 1))⟩
  have hset : Finset.range (j + 1 + 1) = insert (j + 1) (Finset.range (j + 1)) := by
    rw [show (j + 1 + 1) = (j + 1) + 1 from rfl, Finset.range_add_one]
  have h1 : (Finset.range (j + 1 + 1)).sup' hne' (fun k => z k i) =
      (insert (j + 1) (Finset.range (j + 1))).sup' (hset ▸ hne')
        (fun k => z k i) := by
    congr 1
  rw [bmax, bmax, h1, Finset.sup'_insert hne]
  exact max_comm _ _

/-- The minimum over `range (j+2)` is the minimum of the minimum over
`range (j+1)` and the value at `j+1`. -/
theorem bmin_succ (z : ℕ → Site d) (j : ℕ) (i : Fin d) :
    bmin z (j + 1) i = min (bmin z j i) (z (j + 1) i) := by
  have hne : (Finset.range (j + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos j)⟩
  have hne' : (Finset.range (j + 1 + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos (j + 1))⟩
  have hset : Finset.range (j + 1 + 1) = insert (j + 1) (Finset.range (j + 1)) := by
    rw [show (j + 1 + 1) = (j + 1) + 1 from rfl, Finset.range_add_one]
  have h1 : (Finset.range (j + 1 + 1)).inf' hne' (fun k => z k i) =
      (insert (j + 1) (Finset.range (j + 1))).inf' (hset ▸ hne')
        (fun k => z k i) := by
    congr 1
  rw [bmin, bmin, h1, Finset.inf'_insert hne]
  exact min_comm _ _

/-- In the UP case the coordinatewise minimum does not change. -/
theorem bmin_succ_up (z : ℕ → Site d) (j : ℕ) (i : Fin d)
    (hstep : z (j + 1) = z j + unit i) (k : Fin d) :
    bmin z (j + 1) k = bmin z j k := by
  rw [bmin_succ, hstep]
  by_cases hk : k = i
  · rw [hk]
    have h1 : (z j + unit i) i = z j i + 1 := by
      simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_same]
    rw [h1]
    exact min_eq_left (by linarith [bmin_le z j i (le_refl j)])
  · have h1 : (z j + unit i) k = z j k := by
      simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne hk, add_zero]
    rw [h1]
    exact min_eq_left (bmin_le z j k (le_refl j))

/-- In the UP case the coordinatewise maximum changes only in direction `i`. -/
theorem bmax_succ_up (z : ℕ → Site d) (j : ℕ) (i : Fin d)
    (hstep : z (j + 1) = z j + unit i) (k : Fin d) (hk : k ≠ i) :
    bmax z (j + 1) k = bmax z j k := by
  rw [bmax_succ, hstep]
  have h1 : (z j + unit i) k = z j k := by
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_eq_of_ne hk, add_zero]
  rw [h1]
  exact max_eq_left (le_bmax z j k (le_refl j))

end Exploding
