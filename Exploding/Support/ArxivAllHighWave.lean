/-
The exact front of the one-wave when every site has height `2d - 1`.

This is support work for the arXiv-v2 toy law at `p = 1`.  The proof uses only
the local wave recurrence and the Manhattan norm.
-/
import Exploding.Support.Wave

namespace Exploding

open LatticeProb

private theorem arxivAllHigh_mnorm_zero {d : ℕ} : mnorm (0 : Site d) = 0 := by
  simp [mnorm]

private theorem arxivAllHigh_mnorm_pos_of_ne_zero {d : ℕ} {x : Site d} (hx : x ≠ 0) :
    0 < mnorm x := by
  obtain ⟨i, hi⟩ : ∃ i : Fin d, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  have hcoord : 0 < |x i| := abs_pos.mpr hi
  have hle : |x i| ≤ mnorm x := by
    unfold mnorm
    exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le hcoord hle

private theorem arxivAllHigh_mnorm_add_le {d : ℕ} (x y : Site d) :
    mnorm (x + y) ≤ mnorm x + mnorm y := by
  unfold mnorm
  calc
    (∑ i : Fin d, |(x + y) i|) ≤ ∑ i : Fin d, (|x i| + |y i|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply abs_le.mpr
      constructor
      · calc
          -(|x i| + |y i|) = -|x i| + -|y i| := by ring
          _ ≤ x i + y i := add_le_add (neg_abs_le _) (neg_abs_le _)
      · exact add_le_add (le_abs_self _) (le_abs_self _)
    _ = (∑ i : Fin d, |x i|) + ∑ i : Fin d, |y i| := Finset.sum_add_distrib

private theorem arxivAllHigh_mnorm_unit {d : ℕ} (i : Fin d) :
    mnorm (unit i : Site d) = 1 := by
  have hpoint : ∀ j : Fin d,
      |(unit i : Site d) j| = (if j = i then (1 : ℤ) else 0) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [unit]
    · simp [unit, hji]
  unfold mnorm
  calc
    (∑ j : Fin d, |(unit i : Site d) j|) =
        ∑ j : Fin d, (if j = i then (1 : ℤ) else 0) :=
      Finset.sum_congr rfl (fun j _ => hpoint j)
    _ = 1 := by simp

private theorem arxivAllHigh_mnorm_neg {d : ℕ} (x : Site d) : mnorm (-x) = mnorm x := by
  simp [mnorm]

private theorem arxivAllHigh_mnorm_neighbor_lower {d : ℕ} (x : Site d) (i : Fin d) :
    mnorm x ≤ mnorm (x + unit i) + 1 ∧ mnorm x ≤ mnorm (x - unit i) + 1 := by
  constructor
  · calc
      mnorm x = mnorm ((x + unit i) - unit i) := by congr 1; abel
      _ ≤ mnorm (x + unit i) + mnorm (-unit i) := arxivAllHigh_mnorm_add_le _ _
      _ = mnorm (x + unit i) + 1 := by rw [arxivAllHigh_mnorm_neg, arxivAllHigh_mnorm_unit]
  · calc
      mnorm x = mnorm ((x - unit i) + unit i) := by congr 1; abel
      _ ≤ mnorm (x - unit i) + mnorm (unit i) := arxivAllHigh_mnorm_add_le _ _
      _ = mnorm (x - unit i) + 1 := by rw [arxivAllHigh_mnorm_unit]

private theorem arxivAllHigh_mnorm_sub_unit_of_pos {d : ℕ} (x : Site d) (i : Fin d)
    (hxi : 0 < x i) : mnorm (x - unit i) + 1 = mnorm x := by
  have hpoint : ∀ j : Fin d,
      |(x - unit i) j| + (if j = i then (1 : ℤ) else 0) = |x j| := by
    intro j
    by_cases hji : j = i
    · subst j
      have hsub : 0 ≤ x i - 1 := by omega
      have hxnonneg : 0 ≤ x i := by omega
      simp only [Pi.sub_apply]
      rw [show (unit i : Site d) i = 1 by simp [unit]]
      simp only [if_true]
      rw [abs_of_nonneg hsub, abs_of_nonneg hxnonneg]
      omega
    · simp [Pi.sub_apply, unit, hji]
  have hsum :
      (∑ j : Fin d, (|(x - unit i) j| + (if j = i then (1 : ℤ) else 0))) =
        ∑ j : Fin d, |x j| :=
    Finset.sum_congr rfl (fun j _ => hpoint j)
  unfold mnorm
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hsum

private theorem arxivAllHigh_mnorm_add_unit_of_neg {d : ℕ} (x : Site d) (i : Fin d)
    (hxi : x i < 0) : mnorm (x + unit i) + 1 = mnorm x := by
  have hpoint : ∀ j : Fin d,
      |(x + unit i) j| + (if j = i then (1 : ℤ) else 0) = |x j| := by
    intro j
    by_cases hji : j = i
    · subst j
      have hnonpos : x i + 1 ≤ 0 := by omega
      have hxnonpos : x i ≤ 0 := by omega
      simp only [Pi.add_apply]
      rw [show (unit i : Site d) i = 1 by simp [unit]]
      simp only [if_true]
      rw [abs_of_nonpos hnonpos, abs_of_nonpos hxnonpos]
      omega
    · simp [Pi.add_apply, unit, hji]
  have hsum :
      (∑ j : Fin d, (|(x + unit i) j| + (if j = i then (1 : ℤ) else 0))) =
        ∑ j : Fin d, |x j| :=
    Finset.sum_congr rfl (fun j _ => hpoint j)
  unfold mnorm
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hsum

private theorem arxivAllHigh_mnorm_predecessor {d : ℕ} {x : Site d} (hx : x ≠ 0) :
    ∃ i : Fin d,
      (0 < x i ∧ mnorm (x - unit i) + 1 = mnorm x) ∨
      (x i < 0 ∧ mnorm (x + unit i) + 1 = mnorm x) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin d, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  by_cases hpos : 0 < x i
  · exact ⟨i, Or.inl ⟨hpos, arxivAllHigh_mnorm_sub_unit_of_pos x i hpos⟩⟩
  · have hneg : x i < 0 := by omega
    exact ⟨i, Or.inr ⟨hneg, arxivAllHigh_mnorm_add_unit_of_neg x i hneg⟩⟩

/-- For the all-high background, the one-wave started at zero is the indicator
of the Manhattan ball of radius `t`. -/
theorem arxivAllHigh_waveFront (d : ℕ) (hd : 2 ≤ d) (t : ℕ) (x : Site d) :
    wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 (0 : Site d) t x =
      if mnorm x ≤ (t : ℤ) then 1 else 0 := by
  induction t generalizing x with
  | zero =>
      rw [wave_zero]
      by_cases hx : x = 0
      · subst x
        simp [arxivAllHigh_mnorm_zero]
      · have hpos := arxivAllHigh_mnorm_pos_of_ne_zero hx
        simp [hx, not_le_of_gt hpos]
  | succ t ih =>
      rw [wave_succ]
      by_cases hx : x = 0
      · subst x
        simp only [if_true]
        rw [arxivAllHigh_mnorm_zero, if_pos (Int.natCast_nonneg (t + 1))]
        norm_num
      · rw [if_neg hx]
        by_cases hfront : mnorm x ≤ ((t + 1 : ℕ) : ℤ)
        · rw [if_pos hfront]
          change (nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x +
            (2 * (d : ℤ) - 1)) / (2 * (d : ℤ)) = 1
          have hdpos : 0 < 2 * (d : ℤ) := by omega
          have hbounds (y : Site d) :
              0 ≤ wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t y ∧
              wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t y ≤ 1 := by
            rw [ih y]
            split_ifs <;> norm_num
          have hsum_upper :
              nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x ≤
                2 * (d : ℤ) := by
            unfold nbrSumZ
            calc
              (∑ i : Fin d,
                (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x + unit i) +
                  wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x - unit i))) ≤
                  ∑ i : Fin d, ((1 : ℤ) + 1) := by
                apply Finset.sum_le_sum
                intro i hi
                exact add_le_add (hbounds (x + unit i)).2 (hbounds (x - unit i)).2
              _ = 2 * (d : ℤ) := by
                simp [Finset.sum_const, Fintype.card_fin]
                ring
          obtain ⟨i, hpred⟩ := arxivAllHigh_mnorm_predecessor hx
          rcases hpred with ⟨hxi, hnorm⟩ | ⟨hxi, hnorm⟩
          · have hpredtime : mnorm (x - unit i) ≤ (t : ℤ) := by omega
            have hwavepred :
                wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x - unit i) = 1 := by
              rw [ih (x - unit i)]
              simp [hpredtime]
            have hterm : 1 ≤
                wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x + unit i) +
                  wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x - unit i) := by
              have := (hbounds (x + unit i)).1
              rw [hwavepred]
              omega
            have hsingle :
                wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x + unit i) +
                    wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x - unit i) ≤
                  nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x := by
              unfold nbrSumZ
              exact Finset.single_le_sum
                (fun j _ => add_nonneg (hbounds (x + unit j)).1 (hbounds (x - unit j)).1)
                (Finset.mem_univ i)
            have hsum_lower :
                1 ≤ nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x :=
              le_trans hterm hsingle
            have hdiv_lower :
                1 ≤
                  (nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x +
                    (2 * (d : ℤ) - 1)) / (2 * (d : ℤ)) := by
              have hnum : 2 * (d : ℤ) ≤
                  nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x +
                    (2 * (d : ℤ) - 1) := by omega
              have hdiv := Int.ediv_le_ediv hdpos hnum
              simpa [ne_of_gt hdpos] using hdiv
            have hdiv_upper :
                (nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x +
                    (2 * (d : ℤ) - 1)) / (2 * (d : ℤ)) ≤ 1 := by
              refine Int.le_of_lt_add_one ?_
              rw [Int.ediv_lt_iff_lt_mul hdpos]
              omega
            exact le_antisymm hdiv_upper hdiv_lower
          · have hpredtime : mnorm (x + unit i) ≤ (t : ℤ) := by omega
            have hwavepred :
                wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x + unit i) = 1 := by
              rw [ih (x + unit i)]
              simp [hpredtime]
            have hterm : 1 ≤
                wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x + unit i) +
                  wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x - unit i) := by
              have := (hbounds (x - unit i)).1
              rw [hwavepred]
              omega
            have hsingle :
                wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x + unit i) +
                    wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x - unit i) ≤
                  nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x := by
              unfold nbrSumZ
              exact Finset.single_le_sum
                (fun j _ => add_nonneg (hbounds (x + unit j)).1 (hbounds (x - unit j)).1)
                (Finset.mem_univ i)
            have hsum_lower :
                1 ≤ nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x :=
              le_trans hterm hsingle
            have hdiv_lower :
                1 ≤
                  (nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x +
                    (2 * (d : ℤ) - 1)) / (2 * (d : ℤ)) := by
              have hnum : 2 * (d : ℤ) ≤
                  nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x +
                    (2 * (d : ℤ) - 1) := by omega
              have hdiv := Int.ediv_le_ediv hdpos hnum
              simpa [ne_of_gt hdpos] using hdiv
            have hdiv_upper :
                (nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x +
                    (2 * (d : ℤ) - 1)) / (2 * (d : ℤ)) ≤ 1 := by
              refine Int.le_of_lt_add_one ?_
              rw [Int.ediv_lt_iff_lt_mul hdpos]
              omega
            exact le_antisymm hdiv_upper hdiv_lower
        · rw [if_neg hfront]
          change (nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x +
            (2 * (d : ℤ) - 1)) / (2 * (d : ℤ)) = 0
          have hdpos : 0 < 2 * (d : ℤ) := by omega
          have hplus (i : Fin d) : (t : ℤ) < mnorm (x + unit i) := by
            have hlow := (arxivAllHigh_mnorm_neighbor_lower x i).1
            omega
          have hminus (i : Fin d) : (t : ℤ) < mnorm (x - unit i) := by
            have hlow := (arxivAllHigh_mnorm_neighbor_lower x i).2
            omega
          have hplus_zero (i : Fin d) :
              wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x + unit i) = 0 := by
            rw [ih (x + unit i)]
            have hnot : ¬ mnorm (x + unit i) ≤ (t : ℤ) := not_le.mpr (hplus i)
            simp [hnot]
          have hminus_zero (i : Fin d) :
              wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t (x - unit i) = 0 := by
            rw [ih (x - unit i)]
            have hnot : ¬ mnorm (x - unit i) ≤ (t : ℤ) := not_le.mpr (hminus i)
            simp [hnot]
          have hsum_zero :
              nbrSumZ (wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 0 t) x = 0 := by
            simp [nbrSumZ, hplus_zero, hminus_zero]
          rw [hsum_zero]
          apply Int.ediv_eq_zero_of_lt_abs
          · omega
          · rw [abs_of_pos hdpos]
            omega

private def arxivAllHigh_e1 : Site 2 := unit (0 : Fin 2)

private def arxivAllHigh_e2 : Site 2 := fun i => if i = (0 : Fin 2) then 2 else 0

private def arxivAllHigh_e3 : Site 2 := fun i => if i = (0 : Fin 2) then 3 else 0

/-- Concrete checks at times zero, one, and two: the origin, its first
neighbor, and a site at distance two have the predicted values, with an
outside site remaining zero. -/
theorem arxivAllHigh_waveFront_nonvacuity :
    wave (fun _ : Site 2 => 3) 1 (0 : Site 2) 0 0 = 1 ∧
    wave (fun _ : Site 2 => 3) 1 0 1 0 = 1 ∧
    wave (fun _ : Site 2 => 3) 1 0 2 0 = 1 ∧
    wave (fun _ : Site 2 => 3) 1 0 0 arxivAllHigh_e1 = 0 ∧
    wave (fun _ : Site 2 => 3) 1 0 1 arxivAllHigh_e1 = 1 ∧
    wave (fun _ : Site 2 => 3) 1 0 2 arxivAllHigh_e1 = 1 ∧
    wave (fun _ : Site 2 => 3) 1 0 0 arxivAllHigh_e2 = 0 ∧
    wave (fun _ : Site 2 => 3) 1 0 1 arxivAllHigh_e2 = 0 ∧
    wave (fun _ : Site 2 => 3) 1 0 2 arxivAllHigh_e2 = 1 ∧
    wave (fun _ : Site 2 => 3) 1 0 2 arxivAllHigh_e3 = 0 := by
  have hfront (t : ℕ) (x : Site 2) :
      wave (fun _ : Site 2 => 3) 1 (0 : Site 2) t x =
        if mnorm x ≤ (t : ℤ) then 1 else 0 := by
    simpa using arxivAllHigh_waveFront 2 (by omega) t x
  have he1 : mnorm arxivAllHigh_e1 = 1 := arxivAllHigh_mnorm_unit 0
  have he2 : mnorm arxivAllHigh_e2 = 2 := by
    simp [arxivAllHigh_e2, mnorm]
  have he3 : mnorm arxivAllHigh_e3 = 3 := by
    simp [arxivAllHigh_e3, mnorm]
  have h00 : wave (fun _ : Site 2 => 3) 1 0 0 0 = 1 := by
    rw [hfront 0 (0 : Site 2), arxivAllHigh_mnorm_zero]
    norm_num
  have h10 : wave (fun _ : Site 2 => 3) 1 0 1 0 = 1 := by
    rw [hfront 1 (0 : Site 2), arxivAllHigh_mnorm_zero]
    norm_num
  have h20 : wave (fun _ : Site 2 => 3) 1 0 2 0 = 1 := by
    rw [hfront 2 (0 : Site 2), arxivAllHigh_mnorm_zero]
    norm_num
  have h01 : wave (fun _ : Site 2 => 3) 1 0 0 arxivAllHigh_e1 = 0 := by
    rw [hfront 0 arxivAllHigh_e1, he1]
    norm_num
  have h11 : wave (fun _ : Site 2 => 3) 1 0 1 arxivAllHigh_e1 = 1 := by
    rw [hfront 1 arxivAllHigh_e1, he1]
    norm_num
  have h21 : wave (fun _ : Site 2 => 3) 1 0 2 arxivAllHigh_e1 = 1 := by
    rw [hfront 2 arxivAllHigh_e1, he1]
    norm_num
  have h02 : wave (fun _ : Site 2 => 3) 1 0 0 arxivAllHigh_e2 = 0 := by
    rw [hfront 0 arxivAllHigh_e2, he2]
    norm_num
  have h12 : wave (fun _ : Site 2 => 3) 1 0 1 arxivAllHigh_e2 = 0 := by
    rw [hfront 1 arxivAllHigh_e2, he2]
    norm_num
  have h22 : wave (fun _ : Site 2 => 3) 1 0 2 arxivAllHigh_e2 = 1 := by
    rw [hfront 2 arxivAllHigh_e2, he2]
    norm_num
  have h23 : wave (fun _ : Site 2 => 3) 1 0 2 arxivAllHigh_e3 = 0 := by
    rw [hfront 2 arxivAllHigh_e3, he3]
    norm_num
  exact ⟨h00, h10, h20, h01, h11, h21, h02, h12, h22, h23⟩

/-- The all-high one-wave never stabilizes, since a site at distance `T + 1`
is still reached at time `T + 1`. -/
theorem arxivAllHigh_wave_not_stabilizable (d : ℕ) (hd : 2 ≤ d) :
    ¬ WaveStabilizable (fun _ : Site d => 2 * (d : ℤ) - 1) 1 (0 : Site d) := by
  rintro ⟨T, hstable⟩
  let i : Fin d := ⟨0, by omega⟩
  let x : Site d := fun j => if j = i then ((T + 1 : ℕ) : ℤ) else 0
  have hnorm : mnorm x = ((T + 1 : ℕ) : ℤ) := by
    have hpoint : ∀ j : Fin d,
        |x j| = (if j = i then ((T + 1 : ℕ) : ℤ) else 0) := by
      intro j
      by_cases hj : j = i
      · subst j
        change |(if i = i then ((T + 1 : ℕ) : ℤ) else 0)| =
          if i = i then ((T + 1 : ℕ) : ℤ) else 0
        have hnonneg : (0 : ℤ) ≤
            (if i = i then ((T + 1 : ℕ) : ℤ) else 0) := by
          exact Int.natCast_nonneg _
        rw [abs_of_nonneg hnonneg]
      · simp [x, hj]
    unfold mnorm
    calc
      (∑ j : Fin d, |x j|) =
          ∑ j : Fin d, (if j = i then ((T + 1 : ℕ) : ℤ) else 0) := by
        exact Finset.sum_congr rfl (fun j _ => hpoint j)
      _ = ((T + 1 : ℕ) : ℤ) := by simp
  have hbefore :
      wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 (0 : Site d) T x = 0 := by
    rw [arxivAllHigh_waveFront d hd T x]
    have hnot : ¬ mnorm x ≤ (T : ℤ) := by omega
    simp [hnot]
  have hafter :
      wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 (0 : Site d) (T + 1) x = 1 := by
    rw [arxivAllHigh_waveFront d hd (T + 1) x]
    simp [hnorm]
  have hEq := congrFun (hstable (T + 1) (by omega)) x
  rw [hbefore, hafter] at hEq
  norm_num at hEq

/-- The exact front makes the all-high wave nonstabilizable, so its first
nonstabilizable mass, `waveThreshold`, is one. -/
theorem arxivAllHigh_waveThreshold_eq_one (d : ℕ) (hd : 2 ≤ d) :
    waveThreshold (fun _ : Site d => 2 * (d : ℤ) - 1) (0 : Site d) = 1 := by
  have hnonstab := arxivAllHigh_wave_not_stabilizable d hd
  have hmem :
      1 ∈ {n : ℕ | 1 ≤ n ∧
        ¬ WaveStabilizable (fun _ : Site d => 2 * (d : ℤ) - 1) n (0 : Site d)} :=
    ⟨le_rfl, hnonstab⟩
  have hge :
      1 ≤ waveThreshold (fun _ : Site d => 2 * (d : ℤ) - 1) (0 : Site d) := by
    unfold waveThreshold
    exact (Nat.sInf_mem ⟨1, hmem⟩).1
  have hle :
      waveThreshold (fun _ : Site d => 2 * (d : ℤ) - 1) (0 : Site d) ≤ 1 := by
    unfold waveThreshold
    exact Nat.sInf_le (show 1 ∈ {n : ℕ | 1 ≤ n ∧
      ¬ WaveStabilizable (fun _ : Site d => 2 * (d : ℤ) - 1) n (0 : Site d)} from
        ⟨le_rfl, hnonstab⟩)
  omega

end Exploding
