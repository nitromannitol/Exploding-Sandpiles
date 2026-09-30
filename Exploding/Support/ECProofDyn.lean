/-
The toppling dynamics behind Proposition 7.1: a stabilizing odometer is finitely
supported, fills a large ball, dominates frozen odometers, and so propagates the
complete toppling of one tile to every adjacent box-crossing tile.
-/
import Exploding.Support.Hypotheses

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### Elementary facts on odometers and the Manhattan norm -/

theorem ec_podo_nonneg (s0 : Site d → ℤ) (t : ℕ) (x : Site d) : 0 ≤ podo s0 t x := by
  induction t with
  | zero => simp
  | succ t ih => rw [podo_succ]; split <;> omega

theorem ec_unit_apply (i j : Fin d) : unit i j = if j = i then (1 : ℤ) else 0 := by
  simp [unit, Pi.single_apply]

theorem ec_mnorm_zero : mnorm (0 : Site d) = 0 := by simp [mnorm]

theorem ec_mnorm_le_add_unit (x : Site d) (i : Fin d) :
    mnorm x ≤ mnorm (x + unit i) + 1 := by
  have hterm : ∀ j : Fin d,
      |x j| ≤ |(x + unit i) j| + (if j = i then (1 : ℤ) else 0) := by
    intro j
    by_cases hj : j = i
    · have hxj : (x + unit i) j = x j + 1 := by
        rw [Pi.add_apply, ec_unit_apply, if_pos hj]
      rw [hxj, if_pos hj]
      have h1 := abs_add_le (x j + 1) (-1 : ℤ)
      rw [show x j + 1 + (-1) = x j from by ring, abs_neg, abs_one] at h1
      exact h1
    · have hxj : (x + unit i) j = x j := by
        rw [Pi.add_apply, ec_unit_apply, if_neg hj, add_zero]
      rw [hxj, if_neg hj]
      simp
  have hsum : (∑ j : Fin d, (if j = i then (1 : ℤ) else 0)) = 1 := by
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (fun hi => absurd (Finset.mem_univ i) hi), if_pos rfl]
  calc mnorm x = ∑ j : Fin d, |x j| := rfl
    _ ≤ ∑ j : Fin d, (|(x + unit i) j| + (if j = i then (1 : ℤ) else 0)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = mnorm (x + unit i) + 1 := by
        rw [Finset.sum_add_distrib, hsum]
        rfl

theorem ec_mnorm_le_sub_unit (x : Site d) (i : Fin d) :
    mnorm x ≤ mnorm (x - unit i) + 1 := by
  have hterm : ∀ j : Fin d,
      |x j| ≤ |(x - unit i) j| + (if j = i then (1 : ℤ) else 0) := by
    intro j
    by_cases hj : j = i
    · have hxj : (x - unit i) j = x j - 1 := by
        rw [Pi.sub_apply, ec_unit_apply, if_pos hj]
      rw [hxj, if_pos hj]
      have h1 := abs_add_le (x j - 1) (1 : ℤ)
      rw [show x j - 1 + 1 = x j from by ring, abs_one] at h1
      exact h1
    · have hxj : (x - unit i) j = x j := by
        rw [Pi.sub_apply, ec_unit_apply, if_neg hj, sub_zero]
      rw [hxj, if_neg hj]
      simp
  have hsum : (∑ j : Fin d, (if j = i then (1 : ℤ) else 0)) = 1 := by
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (fun hi => absurd (Finset.mem_univ i) hi), if_pos rfl]
  calc mnorm x = ∑ j : Fin d, |x j| := rfl
    _ ≤ ∑ j : Fin d, (|(x - unit i) j| + (if j = i then (1 : ℤ) else 0)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = mnorm (x - unit i) + 1 := by
        rw [Finset.sum_add_distrib, hsum]
        rfl

/-- A point other than the origin has a neighbour one step closer in the Manhattan norm. -/
theorem ec_exists_nbr_closer (x : Site d) (hx : x ≠ 0) :
    ∃ y : Site d, mnorm y + 1 = mnorm x ∧
      ∃ i : Fin d, x = y + unit i ∨ x = y - unit i := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · refine ⟨x + unit i, ?_, i, Or.inr (by abel)⟩
    have hterm : ∀ j : Fin d, |(x + unit i) j| + (if j = i then (1 : ℤ) else 0) = |x j| := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Pi.add_apply, ec_unit_apply, if_pos rfl]
        rw [abs_of_neg hneg, abs_of_nonpos (by omega)]; ring
      · rw [Pi.add_apply, ec_unit_apply, if_neg hj]; simp
    have hsum : (∑ j : Fin d, (if j = i then (1 : ℤ) else 0)) = 1 := by
      rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
        (fun hi => absurd (Finset.mem_univ i) hi), if_pos rfl]
    calc mnorm (x + unit i) + 1 = ∑ j : Fin d, (|(x + unit i) j| + (if j = i then (1 : ℤ) else 0)) := by
          rw [Finset.sum_add_distrib, hsum]; rfl
      _ = mnorm x := Finset.sum_congr rfl (fun j _ => hterm j)
  · refine ⟨x - unit i, ?_, i, Or.inl (by abel)⟩
    have hterm : ∀ j : Fin d, |(x - unit i) j| + (if j = i then (1 : ℤ) else 0) = |x j| := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Pi.sub_apply, ec_unit_apply, if_pos rfl]
        rw [abs_of_pos hpos, abs_of_nonneg (by omega)]; ring
      · rw [Pi.sub_apply, ec_unit_apply, if_neg hj]; simp
    have hsum : (∑ j : Fin d, (if j = i then (1 : ℤ) else 0)) = 1 := by
      rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
        (fun hi => absurd (Finset.mem_univ i) hi), if_pos rfl]
    calc mnorm (x - unit i) + 1 = ∑ j : Fin d, (|(x - unit i) j| + (if j = i then (1 : ℤ) else 0)) := by
          rw [Finset.sum_add_distrib, hsum]; rfl
      _ = mnorm x := Finset.sum_congr rfl (fun j _ => hterm j)

/-! ### Finite speed, stable odometers -/

/-- Finite propagation speed: off the source the odometer vanishes at distance more
than the elapsed time. -/
theorem ec_podo_zero_of_far (s0 : Site d → ℤ) (hs0 : ∀ x, x ≠ 0 → s0 x ≤ 2 * (d : ℤ) - 1) :
    ∀ t : ℕ, ∀ x : Site d, (t : ℤ) < mnorm x → podo s0 t x = 0 := by
  intro t
  induction t with
  | zero => intro x _; simp
  | succ t ih =>
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h; subst h; rw [ec_mnorm_zero] at hx; omega
    have hxt : podo s0 t x = 0 := ih x (by omega)
    have hlap : lap (podo s0 t) x = 0 := by
      have hn : ∀ i : Fin d, podo s0 t (x + unit i) + podo s0 t (x - unit i) = 0 := by
        intro i
        have h1 := ec_mnorm_le_add_unit x i
        have h2 := ec_mnorm_le_sub_unit x i
        rw [ih _ (by push_cast at hx ⊢; omega), ih _ (by push_cast at hx ⊢; omega)]
        rfl
      simp only [lap, nbrSumZ, hxt, Finset.sum_eq_zero (fun i _ => hn i)]
      ring
    rw [podo_succ]
    have hnot : ¬ (2 * (d : ℤ) ≤ pconf s0 t x) := by
      simp only [pconf, hlap]
      have := hs0 x hx0
      omega
    rw [if_neg hnot, hxt]
    rfl

/-- A stabilizable initial sandpile has a time at which the odometer is stable. -/
theorem ec_stable_of_stabilizable (s0 : Site d → ℤ) (h : Stabilizable s0) :
    ∃ T : ℕ, ∀ x, s0 x + lap (podo s0 T) x ≤ 2 * (d : ℤ) - 1 := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun x => ?_⟩
  by_contra hcon
  have h1 : 2 * (d : ℤ) ≤ pconf s0 T x := by simp only [pconf]; omega
  have h2 := congrFun (hT (T + 1) (Nat.le_succ T)) x
  rw [podo_succ, if_pos h1] at h2
  omega

/-! ### The stable odometer fills a large ball -/

theorem ec_single_le_nbrSum (v : Site d → ℤ) (hv : ∀ x, 0 ≤ v x) (x y : Site d)
    (hy : ∃ i : Fin d, y = x + unit i ∨ y = x - unit i) : v y ≤ nbrSumZ v x := by
  obtain ⟨i, hi⟩ := hy
  have hterm : ∀ j : Fin d, 0 ≤ v (x + unit j) + v (x - unit j) := fun j => by
    have := hv (x + unit j); have := hv (x - unit j); omega
  have hle : v (x + unit i) + v (x - unit i) ≤ nbrSumZ v x :=
    Finset.single_le_sum (f := fun j : Fin d => v (x + unit j) + v (x - unit j))
      (fun j _ => hterm j) (Finset.mem_univ i)
  rcases hi with rfl | rfl
  · have := hv (x - unit i); omega
  · have := hv (x + unit i); omega

/-- **Ball filling.**  A nonnegative stable odometer for the background `η ≥ 0` with
`n ≥ (2d)^(ρ+2)` chips at the origin is at least one on the whole ball of radius `ρ`. -/
theorem ec_ball_fill (hd : 1 ≤ d) (η : Site d → ℤ) (hη0 : ∀ x, 0 ≤ η x) (n : ℕ)
    (v : Site d → ℤ) (hv0 : ∀ x, 0 ≤ v x)
    (hstab : ∀ x, (η x + (n : ℤ) * dirac (0 : Site d) x) + lap v x ≤ 2 * (d : ℤ) - 1)
    (ρ : ℕ) (hn : (2 * d) ^ (ρ + 2) ≤ n) :
    ∀ x : Site d, mnorm x ≤ (ρ : ℤ) → 1 ≤ v x := by
  have hd2 : (2 : ℤ) ≤ 2 * (d : ℤ) := by omega
  have hdpos : (0 : ℤ) < 2 * (d : ℤ) := by omega
  have hn' : ((2 * (d : ℤ)) ^ (ρ + 2)) ≤ (n : ℤ) := by exact_mod_cast hn
  -- the bound at distance `r`
  have key : ∀ r : ℕ, r ≤ ρ → ∀ x : Site d, mnorm x ≤ (r : ℤ) →
      (2 * (d : ℤ)) ^ (ρ - r + 1) - 1 ≤ v x := by
    intro r
    induction r with
    | zero =>
      intro _ x hx
      have hx0 : x = 0 := by
        by_contra hne
        obtain ⟨y, hy, _⟩ := ec_exists_nbr_closer x hne
        have : 0 ≤ mnorm y := Finset.sum_nonneg (fun i _ => abs_nonneg _)
        push_cast at hx; omega
      subst hx0
      have h1 := hstab 0
      have h2 : dirac (0 : Site d) 0 = 1 := dirac_self _
      rw [h2] at h1
      have h3 : lap v 0 = nbrSumZ v 0 - 2 * (d : ℤ) * v 0 := rfl
      have h4 : 0 ≤ nbrSumZ v 0 := Finset.sum_nonneg (fun i _ => add_nonneg (hv0 _) (hv0 _))
      have h5 := hη0 0
      have h6 : (2 * (d : ℤ)) ^ (ρ + 2) = 2 * (d : ℤ) * (2 * (d : ℤ)) ^ (ρ + 1) := by ring
      simp only [Nat.sub_zero]
      by_contra hlt
      push Not at hlt
      have h7 : v 0 ≤ (2 * (d : ℤ)) ^ (ρ + 1) - 2 := by omega
      nlinarith
    | succ r ih =>
      intro hr x hx
      by_cases hle : mnorm x ≤ (r : ℤ)
      · have := ih (by omega) x hle
        have hmono : (2 * (d : ℤ)) ^ (ρ - (r + 1) + 1) ≤ (2 * (d : ℤ)) ^ (ρ - r + 1) :=
          pow_le_pow_right₀ (by omega) (by omega)
        omega
      · have hx0 : x ≠ 0 := by
          intro h; subst h; rw [ec_mnorm_zero] at hle; omega
        obtain ⟨y, hy, hadj⟩ := ec_exists_nbr_closer x hx0
        have hyr : mnorm y ≤ (r : ℤ) := by push_cast at hx; omega
        have hvy := ih (by omega) y hyr
        have hnb : v y ≤ nbrSumZ v x := by
          refine ec_single_le_nbrSum v hv0 x y ?_
          obtain ⟨i, hi⟩ := hadj
          refine ⟨i, ?_⟩
          rcases hi with h | h
          · right; rw [h]; abel
          · left; rw [h]; abel
        have h1 := hstab x
        have h3 : lap v x = nbrSumZ v x - 2 * (d : ℤ) * v x := rfl
        have h5 := hη0 x
        have h6 : 0 ≤ (n : ℤ) * dirac (0 : Site d) x := by
          have : 0 ≤ dirac (0 : Site d) x := by unfold dirac; split <;> omega
          positivity
        have h7 : (2 * (d : ℤ)) ^ (ρ - r + 1) = 2 * (d : ℤ) * (2 * (d : ℤ)) ^ (ρ - (r + 1) + 1) := by
          have : ρ - r + 1 = (ρ - (r + 1) + 1) + 1 := by omega
          rw [this, pow_succ]; ring
        by_contra hlt
        push Not at hlt
        have h8 : v x ≤ (2 * (d : ℤ)) ^ (ρ - (r + 1) + 1) - 2 := by omega
        nlinarith
  intro x hx
  have := key ρ le_rfl x hx
  simp only [Nat.sub_self, zero_add, pow_one] at this
  omega

/-! ### Comparison of a frozen odometer with a stable one -/

/-- A frozen odometer is dominated by any stable odometer that dominates its seed. -/
theorem ec_fodo_le (S : Set (Site d)) (s0 s0' w0 v : Site d → ℤ) (hle : ∀ x, s0 x ≤ s0' x)
    (hw : ∀ x, w0 x ≤ v x) (hstab : ∀ x, s0' x + lap v x ≤ 2 * (d : ℤ) - 1) :
    ∀ t x, fodo S s0 w0 t x ≤ v x := by
  intro t
  induction t with
  | zero => intro x; simpa using hw x
  | succ t ih =>
    intro x
    rw [fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx]; exact hw x
    · rw [if_neg hx]
      by_cases hlt : fodo S s0 w0 t x < v x
      · split_ifs <;> omega
      · have heq : fodo S s0 w0 t x = v x := le_antisymm (ih x) (not_lt.1 hlt)
        have hl : lap (fodo S s0 w0 t) x ≤ lap v x := by
          have h1 := nbrSumZ_mono (fun y => ih y) x
          simp only [lap]
          rw [heq]
          linarith
        have hno : ¬ (2 * (d : ℤ) ≤ fconf S s0 w0 t x) := by
          simp only [fconf]
          have := hle x
          have := hstab x
          omega
        rw [if_neg hno, heq]
        omega

/-! ### Tiles -/

theorem ec_faceOut_subset (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j : Site d) (i : Fin d)
    (hi : Bool) :
    faceOut k j i hi ⊆ rboxShift k (if hi then j + unit i else j - unit i) := by
  intro x hx
  obtain ⟨hxc, hxi⟩ := hx
  have hki := hk i
  have hfaceout : ∀ y ∈ rboxShift k j, y i ≠ x i := by
    intro y hy hyx
    have := hy i
    cases hi <;> simp at hxi <;> omega
  have hrange : ∀ l, l ≠ i → 1 + (k l : ℤ) * j l ≤ x l ∧ x l ≤ (k l : ℤ) * j l + (k l : ℤ) := by
    intro l hl
    rcases hxc with hxB | ⟨hxB, y, hyB, m, hm⟩
    · exact absurd rfl (hfaceout x hxB)
    · have hunit : ∀ c : Fin d, c ≠ m → (unit m : Site d) c = 0 := by
        intro c hc; rw [ec_unit_apply, if_neg hc]
      have hmi : m = i := by
        by_contra hmi
        apply hfaceout y hyB
        rcases hm with h | h
        · rw [h, Pi.add_apply, hunit i (fun h' => hmi h'.symm)]; ring
        · rw [h, Pi.add_apply, hunit i (fun h' => hmi h'.symm)]; ring
      subst hmi
      have hyl : y l = x l := by
        rcases hm with h | h
        · rw [h, Pi.add_apply, hunit l hl]; ring
        · rw [h, Pi.add_apply, hunit l hl]; ring
      rw [← hyl]
      exact hyB l
  intro l
  by_cases hl : l = i
  · subst hl
    cases hi
    · simp only [Bool.false_eq_true, if_false, Pi.sub_apply, ec_unit_apply, if_true]
      simp only [Bool.false_eq_true, if_false] at hxi
      rw [hxi]
      constructor <;> nlinarith
    · simp only [if_true, Pi.add_apply, ec_unit_apply]
      simp only [if_true] at hxi
      rw [hxi]
      constructor <;> nlinarith
  · have := hrange l hl
    cases hi
    · simp only [Bool.false_eq_true, if_false, Pi.sub_apply, ec_unit_apply, if_neg hl]
      simpa using this
    · simp only [if_true, Pi.add_apply, ec_unit_apply, if_neg hl]
      simpa using this

/-- **Tile propagation.**  If a tile is completely toppled in a stable odometer and an
adjacent tile is box-crossing, then the adjacent tile is completely toppled. -/
theorem ec_tile_step (η : Site d → ℤ) (n : ℕ) (v : Site d → ℤ)
    (hv0 : ∀ x, 0 ≤ v x)
    (hstab : ∀ x, (η x + (n : ℤ) * dirac (0 : Site d) x) + lap v x ≤ 2 * (d : ℤ) - 1)
    (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j j' : Site d) (i : Fin d)
    (hadj : j' = j + unit i ∨ j' = j - unit i)
    (hfull : ∀ x ∈ rboxShift k j, 1 ≤ v x) (hcross : BoxCrossed η k j') :
    ∀ x ∈ rboxShift k j', 1 ≤ v x := by
  have hdir : ∀ y : Site d, 0 ≤ dirac (0 : Site d) y := by
    intro y; unfold dirac; split <;> omega
  have hle : ∀ x, η x ≤ η x + (n : ℤ) * dirac (0 : Site d) x := fun x => by
    have := hdir x
    have : 0 ≤ (n : ℤ) * dirac (0 : Site d) x := by positivity
    omega
  have key : ∀ (hi : Bool), faceOut k j' i hi ⊆ rboxShift k j →
      CrossedInDirection η k j' i hi → ∀ x ∈ rboxShift k j', 1 ≤ v x := by
    intro hi hsub hc x hx
    have h1 := hc (∏ l, k l) le_rfl x hx
    have hw : ∀ y, (Set.indicator (faceOut k j' i hi) (1 : Site d → ℤ)) y ≤ v y := by
      intro y
      by_cases hy : y ∈ faceOut k j' i hi
      · rw [Set.indicator_of_mem hy]
        exact hfull y (hsub hy)
      · rw [Set.indicator_of_notMem hy]
        exact hv0 y
    have h2 := ec_fodo_le ((rboxShift k j')ᶜ) η (fun x => η x + (n : ℤ) * dirac (0 : Site d) x)
      (Set.indicator (faceOut k j' i hi) (1 : Site d → ℤ)) v hle hw hstab (∏ l, k l) x
    omega
  rcases hadj with rfl | rfl
  · refine key false ?_ (hcross i false)
    have := ec_faceOut_subset k hk (j + unit i) i false
    simpa using this
  · refine key true ?_ (hcross i true)
    have := ec_faceOut_subset k hk (j - unit i) i true
    simpa using this

end Exploding
