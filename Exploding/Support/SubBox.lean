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
theorem br_has_nbr (A : Set (Site d)) (hA : A.Nonempty) {p : Site d}
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
  obtain ⟨y, hy⟩ := hA
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

end Exploding
