import Exploding.Support.Vocab
import Exploding.Support.Wave

/-!
# The all-high ordinary odometer front

On the all-high background `2d - 1 + δ₀`, where every site holds `2d - 1` chips and the
origin holds one more, the parallel toppling odometer `podo` is positive at time `t` and
site `x` exactly when the Manhattan norm of `x` is below `t`.  This is the ordinary
odometer front that the `p = 1` endpoint needs.  It is a different statement from the
wave-level front of `ArxivAllHighWave`, because the odometer recursion differs.

No hypothesis on `d` is assumed, and `d = 0` is included.  The equivalence is proved by
two inductions on `t`.  Positivity forces a small norm: a site that first topples at step
`t + 1` is the origin, or has a neighbour that is positive at time `t`, and by induction
that neighbour has norm below `t`.  Conversely, a site of norm below `t + 1` that is still
zero at time `t` is the origin, which carries the extra chip, or has a neighbour one step
nearer the origin; that neighbour is positive at time `t` by induction, and its unit
contribution to the neighbour sum makes the site topple.
-/

namespace Exploding

open LatticeProb

/-! ### Norm and neighbour facts -/

/-- The parallel toppling odometer is nonnegative at every time and site. -/
theorem podo_nonneg {d : ℕ} (s0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    0 ≤ podo s0 t x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [podo_succ]
    exact add_nonneg ih (by positivity)

/-- The Manhattan norm is nonnegative. -/
theorem mnorm_nonneg {d : ℕ} (x : Site d) : 0 ≤ mnorm x := by
  unfold mnorm
  exact Finset.sum_nonneg fun j _ => abs_nonneg (x j)

/-- The Manhattan norm of the origin vanishes. -/
theorem mnorm_origin {d : ℕ} : mnorm (0 : Site d) = 0 := by
  simp [mnorm]

/-- The indicator of a single coordinate sums to one. -/
theorem sum_ite_eq_unit_one {d : ℕ} (i : Fin d) :
    ∑ j : Fin d, (if j = i then (1 : ℤ) else 0) = 1 := by
  simp

/-- The norm at `x` exceeds the norm at `x + unit i` by at most one. -/
theorem mnorm_le_add_unit_add_one {d : ℕ} (x : Site d) (i : Fin d) :
    mnorm x ≤ mnorm (x + unit i) + 1 := by
  have hpoint : ∀ j : Fin d, |x j| ≤ |(x + unit i) j| + (if j = i then (1 : ℤ) else 0) := by
    intro j
    by_cases hji : j = i
    · rw [hji, if_pos rfl]
      have hu : (unit i : Site d) i = 1 := by simp [unit]
      simp only [Pi.add_apply, hu]
      have h1 := le_abs_self (x i + 1)
      have h2 := neg_abs_le (x i + 1)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · simp [unit, hji]
  unfold mnorm
  calc ∑ j : Fin d, |x j|
      ≤ ∑ j : Fin d, (|(x + unit i) j| + (if j = i then (1 : ℤ) else 0)) :=
        Finset.sum_le_sum fun j _ => hpoint j
    _ = (∑ j : Fin d, |(x + unit i) j|) + 1 := by
        rw [Finset.sum_add_distrib, sum_ite_eq_unit_one i]

/-- The norm at `x` exceeds the norm at `x - unit i` by at most one. -/
theorem mnorm_le_sub_unit_add_one {d : ℕ} (x : Site d) (i : Fin d) :
    mnorm x ≤ mnorm (x - unit i) + 1 := by
  have hpoint : ∀ j : Fin d, |x j| ≤ |(x - unit i) j| + (if j = i then (1 : ℤ) else 0) := by
    intro j
    by_cases hji : j = i
    · rw [hji, if_pos rfl]
      have hu : (unit i : Site d) i = 1 := by simp [unit]
      simp only [Pi.sub_apply, hu]
      have h1 := le_abs_self (x i - 1)
      have h2 := neg_abs_le (x i - 1)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · simp [unit, hji]
  unfold mnorm
  calc ∑ j : Fin d, |x j|
      ≤ ∑ j : Fin d, (|(x - unit i) j| + (if j = i then (1 : ℤ) else 0)) :=
        Finset.sum_le_sum fun j _ => hpoint j
    _ = (∑ j : Fin d, |(x - unit i) j|) + 1 := by
        rw [Finset.sum_add_distrib, sum_ite_eq_unit_one i]

/-- A site other than the origin has a neighbour one step nearer the origin, obtained by
moving towards zero in a coordinate where the site is nonzero. -/
theorem exists_mnorm_pred {d : ℕ} {x : Site d} (hx : x ≠ 0) :
    ∃ i : Fin d, (0 < x i ∧ mnorm (x - unit i) + 1 ≤ mnorm x) ∨
      (x i < 0 ∧ mnorm (x + unit i) + 1 ≤ mnorm x) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin d, x i ≠ 0 := by
    by_contra h
    apply hx
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  by_cases hpos : 0 < x i
  · refine ⟨i, Or.inl ⟨hpos, ?_⟩⟩
    have hpoint : ∀ j : Fin d, |(x - unit i) j| + (if j = i then (1 : ℤ) else 0) ≤ |x j| := by
      intro j
      by_cases hji : j = i
      · rw [hji, if_pos rfl]
        have hu : (unit i : Site d) i = 1 := by simp [unit]
        simp only [Pi.sub_apply, hu]
        rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ x i - 1), abs_of_pos hpos]
        omega
      · simp [unit, hji]
    unfold mnorm
    calc (∑ j : Fin d, |(x - unit i) j|) + 1
        = ∑ j : Fin d, (|(x - unit i) j| + (if j = i then (1 : ℤ) else 0)) := by
          rw [Finset.sum_add_distrib, sum_ite_eq_unit_one i]
      _ ≤ ∑ j : Fin d, |x j| := Finset.sum_le_sum fun j _ => hpoint j
  · have hneg : x i < 0 := lt_of_le_of_ne (not_lt.mp hpos) hi
    refine ⟨i, Or.inr ⟨hneg, ?_⟩⟩
    have hpoint : ∀ j : Fin d, |(x + unit i) j| + (if j = i then (1 : ℤ) else 0) ≤ |x j| := by
      intro j
      by_cases hji : j = i
      · rw [hji, if_pos rfl]
        have hu : (unit i : Site d) i = 1 := by simp [unit]
        simp only [Pi.add_apply, hu]
        rw [abs_of_nonpos (by omega : x i + 1 ≤ 0), abs_of_neg hneg]
        omega
      · simp [unit, hji]
    unfold mnorm
    calc (∑ j : Fin d, |(x + unit i) j|) + 1
        = ∑ j : Fin d, (|(x + unit i) j| + (if j = i then (1 : ℤ) else 0)) := by
          rw [Finset.sum_add_distrib, sum_ite_eq_unit_one i]
      _ ≤ ∑ j : Fin d, |x j| := Finset.sum_le_sum fun j _ => hpoint j

/-- A positive neighbour sum of a function is carried by a neighbour in some coordinate
direction. -/
theorem exists_unit_pos_of_nbrSumZ_pos {d : ℕ} (u : Site d → ℤ) (x : Site d)
    (h : 0 < nbrSumZ u x) : ∃ i : Fin d, 0 < u (x + unit i) ∨ 0 < u (x - unit i) := by
  by_contra hcon
  have hle : ∀ i : Fin d, u (x + unit i) + u (x - unit i) ≤ 0 := by
    intro i
    have h1 : u (x + unit i) ≤ 0 := by
      by_contra hp
      exact hcon ⟨i, Or.inl (not_le.mp hp)⟩
    have h2 : u (x - unit i) ≤ 0 := by
      by_contra hp
      exact hcon ⟨i, Or.inr (not_le.mp hp)⟩
    exact add_nonpos h1 h2
  have hsum : nbrSumZ u x ≤ 0 := by
    unfold nbrSumZ
    calc ∑ i : Fin d, (u (x + unit i) + u (x - unit i))
        ≤ ∑ i : Fin d, (0 : ℤ) := Finset.sum_le_sum fun i _ => hle i
      _ = 0 := by simp
  linarith

/-- For a nonnegative function, the two neighbours of `x` in direction `i` contribute at
most the neighbour sum `nbrSumZ u x`. -/
theorem pair_le_nbrSumZ {d : ℕ} (u : Site d → ℤ) (hu : ∀ y, 0 ≤ u y) (x : Site d)
    (i : Fin d) : u (x + unit i) + u (x - unit i) ≤ nbrSumZ u x := by
  unfold nbrSumZ
  exact Finset.single_le_sum (f := fun j : Fin d => u (x + unit j) + u (x - unit j))
    (fun j _ => add_nonneg (hu _) (hu _)) (Finset.mem_univ i)

/-! ### The odometer step at a vanishing site -/

/-- Where the odometer vanishes, one more toppling step makes it positive exactly when the
origin chip together with the neighbour sum reaches one, since the threshold is `2d` and
the background is `2d - 1` plus the origin chip. -/
theorem podo_succ_pos_iff_of_zero {d : ℕ} (s0 : Site d → ℤ)
    (hs : ∀ y, s0 y = 2 * (d : ℤ) - 1 + dirac (0 : Site d) y) (t : ℕ) (x : Site d)
    (h0 : podo s0 t x = 0) :
    0 < podo s0 (t + 1) x ↔ 1 ≤ dirac (0 : Site d) x + nbrSumZ (podo s0 t) x := by
  have hp : pconf s0 t x = 2 * (d : ℤ) - 1 + dirac (0 : Site d) x + nbrSumZ (podo s0 t) x := by
    unfold pconf lap
    rw [hs x, h0]
    ring
  rw [podo_succ, h0, zero_add, hp]
  split_ifs with hc
  · exact ⟨fun _ => by omega, fun _ => one_pos⟩
  · exact ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h (by omega)⟩

/-! ### The two directions of the front -/

/-- A positive odometer at time `t` forces the Manhattan norm below `t`. -/
theorem podo_pos_imp_mnorm_lt {d : ℕ} (s0 : Site d → ℤ)
    (hs : ∀ y, s0 y = 2 * (d : ℤ) - 1 + dirac (0 : Site d) y) (t : ℕ) :
    ∀ x : Site d, 0 < podo s0 t x → mnorm x < (t : ℤ) := by
  induction t with
  | zero =>
    intro x hx
    have h0 : podo s0 0 x = 0 := rfl
    rw [h0] at hx
    exact absurd hx (lt_irrefl 0)
  | succ t ih =>
    intro x hx
    by_cases hV : 0 < podo s0 t x
    · have hlt := ih x hV
      omega
    · have h0 : podo s0 t x = 0 := le_antisymm (not_lt.mp hV) (podo_nonneg s0 t x)
      have hS := (podo_succ_pos_iff_of_zero s0 hs t x h0).mp hx
      by_cases hx0 : x = 0
      · subst hx0
        rw [mnorm_origin]
        omega
      · rw [dirac_of_ne hx0, zero_add] at hS
        obtain ⟨i, hi | hi⟩ := exists_unit_pos_of_nbrSumZ_pos (podo s0 t) x (by omega)
        · have hlt := ih _ hi
          have hstep := mnorm_le_add_unit_add_one x i
          omega
        · have hlt := ih _ hi
          have hstep := mnorm_le_sub_unit_add_one x i
          omega

/-- A site of norm below `t` is positive at time `t`. -/
theorem mnorm_lt_imp_podo_pos {d : ℕ} (s0 : Site d → ℤ)
    (hs : ∀ y, s0 y = 2 * (d : ℤ) - 1 + dirac (0 : Site d) y) (t : ℕ) :
    ∀ x : Site d, mnorm x < (t : ℤ) → 0 < podo s0 t x := by
  induction t with
  | zero =>
    intro x hx
    have := mnorm_nonneg x
    omega
  | succ t ih =>
    intro x hx
    by_cases hV : 0 < podo s0 t x
    · exact lt_of_lt_of_le hV (podo_mono_step s0 t x)
    · have h0 : podo s0 t x = 0 := le_antisymm (not_lt.mp hV) (podo_nonneg s0 t x)
      refine (podo_succ_pos_iff_of_zero s0 hs t x h0).mpr ?_
      by_cases hx0 : x = 0
      · subst hx0
        rw [dirac_self]
        have := nbrSumZ_nonneg (podo s0 t) (podo_nonneg s0 t) 0
        omega
      · rw [dirac_of_ne hx0, zero_add]
        obtain ⟨i, ⟨-, hi⟩ | ⟨-, hi⟩⟩ := exists_mnorm_pred hx0
        · have hlt := ih (x - unit i) (by omega)
          have hpair := pair_le_nbrSumZ (podo s0 t) (podo_nonneg s0 t) x i
          have hnn := podo_nonneg s0 t (x + unit i)
          omega
        · have hlt := ih (x + unit i) (by omega)
          have hpair := pair_le_nbrSumZ (podo s0 t) (podo_nonneg s0 t) x i
          have hnn := podo_nonneg s0 t (x - unit i)
          omega

/-- On the all-high background `2d - 1 + δ₀` the parallel toppling odometer is positive at
time `t` and site `x` exactly when `mnorm x < t`.  No hypothesis on `d` is needed. -/
theorem all_high_podo_pos_iff (d : ℕ) (t : ℕ) (x : Site d) :
    0 < podo (fun y : Site d => 2 * (d : ℤ) - 1 + dirac (0 : Site d) y) t x ↔
      mnorm x < (t : ℤ) :=
  ⟨podo_pos_imp_mnorm_lt (fun y : Site d => 2 * (d : ℤ) - 1 + dirac (0 : Site d) y)
      (fun _ => rfl) t x,
    mnorm_lt_imp_podo_pos (fun y : Site d => 2 * (d : ℤ) - 1 + dirac (0 : Site d) y)
      (fun _ => rfl) t x⟩

end Exploding
