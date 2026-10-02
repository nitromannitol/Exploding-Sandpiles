/-
Layers of the growth schedule: the positions of the directions of `J`, the shape of one step
(no growth, one layer above, or one layer below the box in the visited direction), the layers
as near-cubes of the lower dimension whose size grows by one every round, and the number of
layers of each size.
-/
import Exploding.Support.ExtSchSched

namespace Exploding

open LatticeProb

variable {d : ℕ}

section Layer

/-- The position is strictly monotone along `J`: a smaller element of `J` has a smaller
position. -/
theorem xsl_pos_lt_pos (J : Finset (Fin d)) {j₁ j₂ : Fin d} (h₁ : j₁ ∈ J) (h : j₁ < j₂) :
    xss_pos J j₁ < xss_pos J j₂ := by
  unfold xss_pos
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨j₁, by simp [h₁, h], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h⟩

/-- The position of a direction of `J` is less than the number of directions of `J`. -/
theorem xss_pos_lt (J : Finset (Fin d)) {j : Fin d} (hj : j ∈ J) : xss_pos J j < J.card := by
  unfold xss_pos
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨j, hj, lt_irrefl j⟩)

/-- Distinct directions of `J` have distinct positions. -/
theorem xss_pos_injOn (J : Finset (Fin d)) : Set.InjOn (xss_pos J) (↑J : Set (Fin d)) := by
  intro j₁ h₁ j₂ h₂ h
  rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
  · exact absurd h (xsl_pos_lt_pos J h₁ hlt).ne
  · exact heq
  · exact absurd h.symm (xsl_pos_lt_pos J h₂ hgt).ne

/-- Every position below `|J|` is the position of a direction of `J`. -/
theorem xss_exists_pos (J : Finset (Fin d)) {m : ℕ} (hm : m < J.card) :
    ∃ j ∈ J, xss_pos J j = m := by
  have hsub : J.image (xss_pos J) ⊆ Finset.range J.card := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (xss_pos_lt J hj)
  have hcard : (Finset.range J.card).card ≤ (J.image (xss_pos J)).card := by
    rw [Finset.card_range, Finset.card_image_of_injOn (xss_pos_injOn J)]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : m ∈ J.image (xss_pos J) := by
    rw [heq]
    exact Finset.mem_range.mpr hm
  obtain ⟨j, hj, hjm⟩ := Finset.mem_image.mp hmem
  exact ⟨j, hj, hjm⟩

/-- The successor of the time in terms of the round and the position within the round. -/
theorem xsl_succ_divmod {k : ℕ} (hk : 1 ≤ k) (t : ℕ) :
    ((t + 1) / k = t / k ∧ (t + 1) % k = t % k + 1) ∨
      ((t + 1) / k = t / k + 1 ∧ (t + 1) % k = 0 ∧ t % k + 1 = k) := by
  have hm : t % k < k := Nat.mod_lt _ hk
  have ht : t % k + k * (t / k) = t := Nat.mod_add_div t k
  rcases Nat.lt_or_ge (t % k + 1) k with h | h
  · left
    have := (Nat.div_mod_unique (b := k) (a := t + 1) (d := t / k) (c := t % k + 1)
      (by omega)).mpr ⟨by omega, h⟩
    exact this
  · right
    have hk' : t % k + 1 = k := by omega
    have := (Nat.div_mod_unique (b := k) (a := t + 1) (d := t / k + 1) (c := 0)
      (by omega)).mpr ⟨by rw [Nat.mul_add]; omega, by omega⟩
    exact ⟨this.1, this.2, hk'⟩

variable (P : xss_Plan d) {s : ℕ}

/-- The visited direction belongs to `J`. -/
theorem xss_dir_mem (hJ : P.J.Nonempty) (t : ℕ) : xss_dir P hJ t ∈ P.J := by
  have hk : t % P.J.card < P.J.card := Nat.mod_lt _ (Finset.card_pos.mpr hJ)
  have h : ∃ j ∈ P.J, xss_pos P.J j = t % P.J.card := xss_exists_pos P.J hk
  unfold xss_dir
  rw [dif_pos h]
  exact h.choose_spec.1

/-- The visited direction has position `t mod |J|`. -/
theorem xss_pos_dir (hJ : P.J.Nonempty) (t : ℕ) :
    xss_pos P.J (xss_dir P hJ t) = t % P.J.card := by
  have hk : t % P.J.card < P.J.card := Nat.mod_lt _ (Finset.card_pos.mpr hJ)
  have h : ∃ j ∈ P.J, xss_pos P.J j = t % P.J.card := xss_exists_pos P.J hk
  unfold xss_dir
  rw [dif_pos h]
  exact h.choose_spec.2

/-- The sides of the box are the sides of the schedule. -/
theorem xsl_len_box (t : ℕ) (j : Fin d) : xss_hi P t j - xss_lo P t j + 1 = xss_side P t j := by
  unfold xss_hi xss_lo xss_grown xss_len
  omega

/-- Off `J` the box is a single point at every time. -/
theorem xsl_thin (hP : xss_Valid P s) (t : ℕ) {i : Fin d} (hi : i ∉ P.J) :
    xss_lo P t i = xss_hi P t i := by
  have h1 := xsl_len_box P t i
  have h2 := hP.2.2.1.2 i hi
  unfold xss_side xss_len at h1
  rw [if_neg hi] at h1
  omega

/-- The sides of the schedule are nonnegative. -/
theorem xsl_side_nonneg (hP : xss_Valid P s) (t : ℕ) (j : Fin d) : 0 ≤ xss_side P t j := by
  by_cases hj : j ∈ P.J
  · have h1 := hP.2.1.1 j hj
    have h2 := hP.2.2.1.1 j hj
    unfold xss_side xss_len at *
    rw [if_pos hj]
    split_ifs <;> omega
  · have h2 := hP.2.2.1.2 j hj
    unfold xss_side xss_len
    rw [if_neg hj]
    omega

/-- The lower corner is at most one above the upper corner: the box has nonnegative sides. -/
theorem xsl_lo_le_hi (hP : xss_Valid P s) (t : ℕ) (j : Fin d) :
    xss_lo P t j ≤ xss_hi P t j + 1 := by
  have h1 := xsl_len_box P t j
  have h2 := xsl_side_nonneg P hP t j
  omega

/-- At one step only the visited direction changes its side, and it grows by `0` or `1`. -/
theorem xsl_side_step (hP : xss_Valid P s) (t : ℕ) :
    (∀ j, j ≠ xss_dir P hP.1 t → xss_side P (t + 1) j = xss_side P t j) ∧
      xss_side P t (xss_dir P hP.1 t) ≤ xss_side P (t + 1) (xss_dir P hP.1 t) ∧
      xss_side P (t + 1) (xss_dir P hP.1 t) ≤ xss_side P t (xss_dir P hP.1 t) + 1 := by
  have hk : 1 ≤ P.J.card := Finset.card_pos.mpr hP.1
  have hj₀ : xss_dir P hP.1 t ∈ P.J := xss_dir_mem P hP.1 t
  have hpos₀ : xss_pos P.J (xss_dir P hP.1 t) = t % P.J.card := xss_pos_dir P hP.1 t
  have hdm := xsl_succ_divmod hk t
  refine ⟨?_, ?_, ?_⟩
  · intro j hne
    by_cases hj : j ∈ P.J
    · have hpj : xss_pos P.J j ≠ t % P.J.card := by
        rw [← hpos₀]
        exact fun h => hne (xss_pos_injOn P.J hj hj₀ h)
      have hlt := xss_pos_lt P.J hj
      unfold xss_side
      rw [if_pos hj, if_pos hj]
      rcases hdm with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · rw [h1, h2]
        congr 2
        split_ifs <;> omega
      · rw [h1, h2]
        congr 2
        push_cast
        split_ifs <;> omega
    · unfold xss_side
      rw [if_neg hj, if_neg hj]
  · unfold xss_side
    rw [if_pos hj₀, if_pos hj₀, hpos₀]
    rcases hdm with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2]
      split_ifs <;> push_cast <;> omega
    · rw [h1, h2]
      split_ifs <;> push_cast <;> omega
  · unfold xss_side
    rw [if_pos hj₀, if_pos hj₀, hpos₀]
    rcases hdm with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2]
      split_ifs <;> push_cast <;> omega
    · rw [h1, h2]
      split_ifs <;> push_cast <;> omega

/-- Growing the upper corner in direction `i` adds the layer above. -/
theorem xsl_diff_up (lo hi : Site d) (i : Fin d) (h : lo i ≤ hi i + 1) :
    xsb_box lo (Function.update hi i (hi i + 1)) \ xsb_box lo hi = xsb_layerUp lo hi i := by
  ext x
  simp only [Set.mem_sdiff, xsb_layerUp, xsb_mem_box]
  constructor
  · rintro ⟨hx, hn⟩
    have hxi : hi i < x i := by
      by_contra hle
      refine hn fun j => ?_
      by_cases hj : j = i
      · subst hj
        exact ⟨(hx j).1, not_lt.mp hle⟩
      · have := (hx j).2
        rw [Function.update_of_ne hj] at this
        exact ⟨(hx j).1, this⟩
    intro j
    by_cases hj : j = i
    · subst hj
      have := (hx j).2
      rw [Function.update_self] at this
      rw [Function.update_self, Function.update_self]
      omega
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      have := (hx j).2
      rw [Function.update_of_ne hj] at this
      exact ⟨(hx j).1, this⟩
  · intro hx
    have hxi : x i = hi i + 1 := by
      have := hx i
      rw [Function.update_self, Function.update_self] at this
      omega
    refine ⟨fun j => ?_, fun hb => ?_⟩
    · by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        omega
      · have := hx j
        rw [Function.update_of_ne hj, Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]
        exact this
    · have := (hb i).2
      omega

/-- Growing the lower corner in direction `i` adds the layer below. -/
theorem xsl_diff_down (lo hi : Site d) (i : Fin d) (h : lo i ≤ hi i + 1) :
    xsb_box (Function.update lo i (lo i - 1)) hi \ xsb_box lo hi = xsb_layerDown lo hi i := by
  ext x
  simp only [Set.mem_sdiff, xsb_layerDown, xsb_mem_box]
  constructor
  · rintro ⟨hx, hn⟩
    have hxi : x i < lo i := by
      by_contra hle
      refine hn fun j => ?_
      by_cases hj : j = i
      · subst hj
        exact ⟨not_lt.mp hle, (hx j).2⟩
      · have := (hx j).1
        rw [Function.update_of_ne hj] at this
        exact ⟨this, (hx j).2⟩
    intro j
    by_cases hj : j = i
    · subst hj
      have := (hx j).1
      rw [Function.update_self] at this
      rw [Function.update_self, Function.update_self]
      omega
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      have := (hx j).1
      rw [Function.update_of_ne hj] at this
      exact ⟨this, (hx j).2⟩
  · intro hx
    have hxi : x i = lo i - 1 := by
      have := hx i
      rw [Function.update_self, Function.update_self] at this
      omega
    refine ⟨fun j => ?_, fun hb => ?_⟩
    · by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        omega
      · have := hx j
        rw [Function.update_of_ne hj, Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]
        exact this
    · have := (hb i).1
      omega

/-- The corners move only in the visited direction, by one, upward or downward. -/
theorem xsl_corner_aux (t : ℕ) (j₀ : Fin d)
    (h1 : ∀ j, j ≠ j₀ → xss_grown P (t + 1) j = xss_grown P t j)
    (h2 : xss_grown P t j₀ ≤ xss_grown P (t + 1) j₀)
    (h3 : xss_grown P (t + 1) j₀ ≤ xss_grown P t j₀ + 1) :
    (xss_lo P (t + 1) = xss_lo P t ∧ xss_hi P (t + 1) = xss_hi P t) ∨
    (xss_lo P (t + 1) = xss_lo P t ∧
      xss_hi P (t + 1) = Function.update (xss_hi P t) j₀ (xss_hi P t j₀ + 1)) ∨
    (xss_lo P (t + 1) = Function.update (xss_lo P t) j₀ (xss_lo P t j₀ - 1) ∧
      xss_hi P (t + 1) = xss_hi P t) := by
  have hother : ∀ j, j ≠ j₀ →
      xss_lo P (t + 1) j = xss_lo P t j ∧ xss_hi P (t + 1) j = xss_hi P t j := by
    intro j hj
    unfold xss_lo xss_hi
    rw [h1 j hj]
    exact ⟨rfl, rfl⟩
  by_cases hg : xss_grown P (t + 1) j₀ = xss_grown P t j₀
  · left
    refine ⟨funext fun j => ?_, funext fun j => ?_⟩
    · by_cases hj : j = j₀
      · subst hj
        unfold xss_lo
        omega
      · exact (hother j hj).1
    · by_cases hj : j = j₀
      · subst hj
        unfold xss_hi
        omega
      · exact (hother j hj).2
  · have hg' : xss_grown P (t + 1) j₀ = xss_grown P t j₀ + 1 := by omega
    by_cases hu : xss_grown P t j₀ < P.HI j₀ - P.hi0 j₀
    · right
      left
      refine ⟨funext fun j => ?_, funext fun j => ?_⟩
      · by_cases hj : j = j₀
        · subst hj
          unfold xss_lo
          omega
        · exact (hother j hj).1
      · by_cases hj : j = j₀
        · subst hj
          rw [Function.update_self]
          unfold xss_hi
          omega
        · rw [Function.update_of_ne hj]
          exact (hother j hj).2
    · right
      right
      refine ⟨funext fun j => ?_, funext fun j => ?_⟩
      · by_cases hj : j = j₀
        · subst hj
          rw [Function.update_self]
          unfold xss_lo
          omega
        · rw [Function.update_of_ne hj]
          exact (hother j hj).1
      · by_cases hj : j = j₀
        · subst hj
          unfold xss_hi
          omega
        · exact (hother j hj).2

/-- **The shape of one step.**  The box either does not change, or grows by the layer above it
or by the layer below it in the visited direction. -/
theorem xss_step_shape (hP : xss_Valid P s) (t : ℕ) :
    xss_box P (t + 1) = xss_box P t ∨
    (xss_box P (t + 1) = xsb_box (xss_lo P t)
        (Function.update (xss_hi P t) (xss_dir P hP.1 t) (xss_hi P t (xss_dir P hP.1 t) + 1)) ∧
      xss_layer P t = xsb_layerUp (xss_lo P t) (xss_hi P t) (xss_dir P hP.1 t)) ∨
    (xss_box P (t + 1) = xsb_box
        (Function.update (xss_lo P t) (xss_dir P hP.1 t) (xss_lo P t (xss_dir P hP.1 t) - 1))
        (xss_hi P t) ∧
      xss_layer P t = xsb_layerDown (xss_lo P t) (xss_hi P t) (xss_dir P hP.1 t)) := by
  obtain ⟨h1, h2, h3⟩ := xsl_side_step P hP t
  have hg1 : ∀ j, j ≠ xss_dir P hP.1 t → xss_grown P (t + 1) j = xss_grown P t j := by
    intro j hj
    unfold xss_grown
    rw [h1 j hj]
  have hg2 : xss_grown P t (xss_dir P hP.1 t) ≤ xss_grown P (t + 1) (xss_dir P hP.1 t) := by
    unfold xss_grown
    omega
  have hg3 : xss_grown P (t + 1) (xss_dir P hP.1 t) ≤ xss_grown P t (xss_dir P hP.1 t) + 1 := by
    unfold xss_grown
    omega
  have hle := xsl_lo_le_hi P hP t (xss_dir P hP.1 t)
  rcases xsl_corner_aux P t _ hg1 hg2 hg3 with ⟨hl, hh⟩ | ⟨hl, hh⟩ | ⟨hl, hh⟩
  · left
    unfold xss_box
    rw [hl, hh]
  · right
    left
    have hbox : xss_box P (t + 1) = xsb_box (xss_lo P t)
        (Function.update (xss_hi P t) (xss_dir P hP.1 t) (xss_hi P t (xss_dir P hP.1 t) + 1)) := by
      unfold xss_box
      rw [hl, hh]
    refine ⟨hbox, ?_⟩
    unfold xss_layer
    rw [hbox]
    exact xsl_diff_up _ _ _ hle
  · right
    right
    have hbox : xss_box P (t + 1) = xsb_box
        (Function.update (xss_lo P t) (xss_dir P hP.1 t) (xss_lo P t (xss_dir P hP.1 t) - 1))
        (xss_hi P t) := by
      unfold xss_box
      rw [hl, hh]
    refine ⟨hbox, ?_⟩
    unfold xss_layer
    rw [hbox]
    exact xsl_diff_down _ _ _ hle

/-- The size of the layers never exceeds the size of the target. -/
theorem xss_level_le (hP : xss_Valid P s) {t : ℕ} (ht : t < xss_steps P s) :
    P.L + t / P.J.card ≤ s := by
  have hk : 0 < P.J.card := Finset.card_pos.mpr hP.1
  have h : t / P.J.card < s - P.L + 1 := (Nat.div_lt_iff_lt_mul hk).mpr ht
  have := hP.2.2.2.2
  omega

/-- Along `J` every side of the box at time `t` is the size of the current round or one more. -/
theorem xsl_side_near (hP : xss_Valid P s) {t : ℕ} (ht : t < xss_steps P s) {i : Fin d}
    (hi : i ∈ P.J) :
    xss_side P t i = ((P.L + t / P.J.card : ℕ) : ℤ) ∨
      xss_side P t i = ((P.L + t / P.J.card : ℕ) : ℤ) + 1 := by
  have hL := xss_level_le P hP ht
  have h0 := hP.2.2.1.1 i hi
  have hT := hP.2.1.1 i hi
  unfold xss_side
  rw [if_pos hi]
  unfold xss_len at *
  generalize t / P.J.card = r at hL ⊢
  push_cast at *
  split_ifs <;> omega

/-- **The layers are near-cubes.**  Every layer is empty or a near-cube of the other directions
of `J`, of size `L + ⌊t / |J|⌋`. -/
theorem xss_layer_near (hP : xss_Valid P s) {t : ℕ} (ht : t < xss_steps P s) :
    xss_layer P t = ∅ ∨ ∃ lo' hi' : Site d,
      xsb_Near (P.J.erase (xss_dir P hP.1 t)) (P.L + t / P.J.card) lo' hi' ∧
        xss_layer P t = xsb_box lo' hi' := by
  have hnear : ∀ i ∈ P.J, xss_hi P t i - xss_lo P t i + 1 = ((P.L + t / P.J.card : ℕ) : ℤ) ∨
      xss_hi P t i - xss_lo P t i + 1 = ((P.L + t / P.J.card : ℕ) : ℤ) + 1 := by
    intro i hi
    rw [xsl_len_box]
    exact xsl_side_near P hP ht hi
  rcases xss_step_shape P hP t with h | ⟨_, h⟩ | ⟨_, h⟩
  · left
    unfold xss_layer
    rw [h, Set.sdiff_self]
  · right
    refine ⟨Function.update (xss_lo P t) (xss_dir P hP.1 t) (xss_hi P t (xss_dir P hP.1 t) + 1),
      Function.update (xss_hi P t) (xss_dir P hP.1 t) (xss_hi P t (xss_dir P hP.1 t) + 1),
      ⟨?_, ?_⟩, h⟩
    · intro i hi
      have hij : i ≠ xss_dir P hP.1 t := Finset.ne_of_mem_erase hi
      rw [Function.update_of_ne hij, Function.update_of_ne hij]
      exact hnear i (Finset.mem_of_mem_erase hi)
    · intro i hi
      by_cases hij : i = xss_dir P hP.1 t
      · subst hij
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hij, Function.update_of_ne hij]
        exact xsl_thin P hP t fun hiJ => hi (Finset.mem_erase.mpr ⟨hij, hiJ⟩)
  · right
    refine ⟨Function.update (xss_lo P t) (xss_dir P hP.1 t) (xss_lo P t (xss_dir P hP.1 t) - 1),
      Function.update (xss_hi P t) (xss_dir P hP.1 t) (xss_lo P t (xss_dir P hP.1 t) - 1),
      ⟨?_, ?_⟩, h⟩
    · intro i hi
      have hij : i ≠ xss_dir P hP.1 t := Finset.ne_of_mem_erase hi
      rw [Function.update_of_ne hij, Function.update_of_ne hij]
      exact hnear i (Finset.mem_of_mem_erase hi)
    · intro i hi
      by_cases hij : i = xss_dir P hP.1 t
      · subst hij
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hij, Function.update_of_ne hij]
        exact xsl_thin P hP t fun hiJ => hi (Finset.mem_erase.mpr ⟨hij, hiJ⟩)

/-- **At most `|J|` steps have a given layer size.** -/
theorem xss_count_le (hP : xss_Valid P s) (a : ℕ) :
    ((Finset.range (xss_steps P s)).filter (fun t => P.L + t / P.J.card = a)).card
      ≤ P.J.card := by
  have hk : 0 < P.J.card := Finset.card_pos.mpr hP.1
  have hsub : (Finset.range (xss_steps P s)).filter (fun t => P.L + t / P.J.card = a) ⊆
      Finset.Ico (P.J.card * (a - P.L)) (P.J.card * (a - P.L) + P.J.card) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [Finset.mem_Ico]
    have h1 : P.J.card * (t / P.J.card) + t % P.J.card = t := Nat.div_add_mod t _
    have h2 : t % P.J.card < P.J.card := Nat.mod_lt _ hk
    generalize t / P.J.card = q at ht h1
    have h3 : a - P.L = q := by omega
    rw [h3]
    constructor <;> omega
  calc _ ≤ (Finset.Ico (P.J.card * (a - P.L)) (P.J.card * (a - P.L) + P.J.card)).card :=
        Finset.card_le_card hsub
    _ = P.J.card := by rw [Nat.card_Ico]; omega

end Layer

end Exploding
