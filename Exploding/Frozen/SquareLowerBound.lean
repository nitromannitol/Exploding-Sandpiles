/-
Lemma 3.1 of the paper: a wave of order `(2d)^{dn}` covers the box of radius `n`.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb

/-- **Lemma 3.1** (`exploding.tex:705-707`, label `lemma:square_lower_bound`).

"Let `η ≥ 0`.  For all `n ≥ 1` and `m ≥ (2d)^{dn}`, the support of the `m`-wave
contains `[-n,n]^d`."

The support of a wave is the set of sites its odometer is ever positive at.
Because the wave odometer is nondecreasing in time on a nonnegative background,
that set is the support of the terminal odometer whenever the wave stabilizes,
and is the right reading when it does not.

The proof is an induction on time: the wave is nonnegative, and a site at
distance `j ≤ t` from the origin has a neighbour at distance `j - 1`, so
`u_t(x) ≥ ⌊m (2d)^{-j}⌋`; every site of `[-n,n]^d` is within distance `dn`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.square_lower_bound (d : ℕ) (hd : 2 ≤ d) :
    ∀ η : Site d → ℤ, (∀ x, 0 ≤ η x) → ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, (2 * d) ^ (d * n) ≤ m →
      ∀ x ∈ cent d n, ∃ t : ℕ, 0 < wave η m (0 : Site d) t x
-- FROZEN-STATEMENT-END
:= by
  intro η hη n _ m hm x hx
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  -- The Manhattan norm splits off any one coordinate.
  have hsplit : ∀ (y : Site d) (i : Fin d),
      mnorm y = |y i| + ∑ j ∈ Finset.univ.erase i, |y j| := fun y i =>
    (Finset.add_sum_erase _ (fun j => |y j|) (Finset.mem_univ i)).symm
  -- A site at distance `k + 1` from the origin has a neighbour at distance `k`.
  have hstep : ∀ (y : Site d) (k : ℕ), mnorm y = ((k + 1 : ℕ) : ℤ) →
      ∃ i : Fin d, mnorm (y + unit i) = (k : ℤ) ∨ mnorm (y - unit i) = (k : ℤ) := by
    intro y k hy
    have hne : ∃ i, y i ≠ 0 := by
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      have : mnorm y = 0 := by simp [mnorm, hcon]
      rw [this] at hy
      omega
    obtain ⟨i, hi⟩ := hne
    refine ⟨i, ?_⟩
    have hrest : ∀ c : ℤ, ∑ j ∈ Finset.univ.erase i, |(y + c • unit i) j| =
        ∑ j ∈ Finset.univ.erase i, |y j| := by
      intro c
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [unit, hji]
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · left
      have h1 := hsplit (y + (1 : ℤ) • unit i) i
      rw [hrest 1, one_smul] at h1
      have hyi : (y + unit i) i = y i + 1 := by simp [unit]
      rw [h1, hyi, hsplit y i] at *
      rw [abs_of_neg hneg] at hy
      rw [abs_of_nonpos (by omega)]
      push_cast at hy
      linarith
    · right
      have h1 := hsplit (y + (-1 : ℤ) • unit i) i
      rw [hrest (-1), neg_one_smul, ← sub_eq_add_neg] at h1
      have hyi : (y - unit i) i = y i - 1 := by simp [unit]
      rw [h1, hyi]
      rw [hsplit y i, abs_of_pos hpos] at hy
      rw [abs_of_nonneg (by omega)]
      push_cast at hy
      linarith
  -- A nonnegative function's neighbour sum dominates its value at each neighbour.
  have hnbr : ∀ (u : Site d → ℤ), (∀ y, 0 ≤ u y) → ∀ (y : Site d) (i : Fin d),
      u (y + unit i) ≤ nbrSumZ u y ∧ u (y - unit i) ≤ nbrSumZ u y := by
    intro u hu y i
    have hi : u (y + unit i) + u (y - unit i) ≤ nbrSumZ u y := by
      simp only [nbrSumZ]
      exact Finset.single_le_sum (f := fun j => u (y + unit j) + u (y - unit j))
        (fun j _ => add_nonneg (hu _) (hu _)) (Finset.mem_univ i)
    exact ⟨by linarith [hu (y - unit i)], by linarith [hu (y + unit i)]⟩
  -- By induction on `t`: at distance `k ≤ t`, the wave at time `t` is at least
  -- `⌊m (2d)^{-k}⌋`.
  have key : ∀ t k : ℕ, k ≤ t → ∀ y : Site d, mnorm y = (k : ℤ) →
      (m : ℤ) / (2 * (d : ℤ)) ^ k ≤ wave η m (0 : Site d) t y := by
    intro t
    induction t with
    | zero =>
      intro k hk y hy
      have hk0 : k = 0 := by omega
      subst hk0
      have hy0 : y = 0 := by
        funext j
        have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (y j))).mp
          (by simpa [mnorm] using hy)
        simpa using hall j (Finset.mem_univ j)
      subst hy0
      simp
    | succ t ih =>
      intro k hk y hy
      by_cases hy0 : y = 0
      · subst hy0
        rw [wave_at_centre]
        exact Int.ediv_le_self _ (by positivity)
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
          rcases k with _ | k'
          · exfalso
            apply hy0
            funext j
            have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (y j))).mp
              (by simpa [mnorm] using hy)
            simpa using hall j (Finset.mem_univ j)
          · exact ⟨k', rfl⟩
        have hwnn := wave_nonneg η hη m (0 : Site d) t
        obtain ⟨i, hi⟩ := hstep y k' hy
        have hlow : (m : ℤ) / (2 * (d : ℤ)) ^ k' ≤ nbrSumZ (wave η m (0 : Site d) t) y := by
          rcases hi with hi | hi
          · exact le_trans (ih k' (by omega) _ hi) (hnbr _ hwnn y i).1
          · exact le_trans (ih k' (by omega) _ hi) (hnbr _ hwnn y i).2
        rw [wave_of_ne η m 0 y t hy0, pow_succ, ← Int.ediv_ediv_of_nonneg (by positivity)]
        exact Int.ediv_le_ediv hd0 (by linarith [hη y])
  -- Every site of the cube lies within distance `d n` of the origin.
  have hxle : mnorm x ≤ ((d * n : ℕ) : ℤ) := by
    have : ∑ j : Fin d, |x j| ≤ ∑ _j : Fin d, (n : ℤ) := Finset.sum_le_sum fun j _ => hx j
    simpa [mnorm, Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this
  have hx0 : 0 ≤ mnorm x := Finset.sum_nonneg fun j _ => abs_nonneg (x j)
  refine ⟨d * n, ?_⟩
  have hk := key (d * n) (mnorm x).toNat (by omega) x (by omega)
  have hpow : (2 * (d : ℤ)) ^ (mnorm x).toNat ≤ (m : ℤ) := by
    have h1 : (2 * d) ^ (mnorm x).toNat ≤ (2 * d) ^ (d * n) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast le_trans h1 hm
  have hone : (1 : ℤ) ≤ (m : ℤ) / (2 * (d : ℤ)) ^ (mnorm x).toNat := by
    rw [Int.le_ediv_iff_mul_le (by positivity)]
    linarith
  linarith
