/-
The base of the induction on the number of directions: a box along a single direction is a line
segment, and it is internally spanned as soon as one of its sites is occupied, because a site
topples as soon as one of its two neighbours along the line has toppled.  Hence the probability
that it is not spanned is at most `(1 - p)` to the number of its sites.
-/
import Exploding.Support.ExtSchBox
import Exploding.Support.ExtSchProof5
import Exploding.Support.ExtSchSeed

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- A segment along the direction `i` with an occupied site is internally spanned along `{i}`. -/
theorem xs1_sp_of_occ {i : Fin d} {lo hi : Site d} (hthin : ∀ j, j ≠ i → lo j = hi j)
    {η : Site d → ℤ} (h : ∃ x ∈ xsb_box lo hi, η x = 2 * (d : ℤ)) :
    xsch_Sp ({i} : Finset (Fin d)) (xsb_box lo hi) η := by
  obtain ⟨x₀, hx₀, hη⟩ := h
  have key : ∀ n : ℕ, ∀ y ∈ xsb_box lo hi, (y i - x₀ i).natAbs = n →
      xsch_Top ({i} : Finset (Fin d)) (xsb_box lo hi) η y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y hy hn
      by_cases hyx : y i = x₀ i
      · have hyeq : y = x₀ := by
          funext j
          by_cases hj : j = i
          · subst hj; exact hyx
          · have h1 := hy j
            have h2 := hx₀ j
            have h3 := hthin j hj
            omega
        subst hyeq
        exact xsch_Top.occ hy hη
      · set b : Bool := decide (y i < x₀ i) with hb
        have hstep : y + xsch_dir (i, b) ∈ xsb_box lo hi := by
          intro j
          by_cases hj : j = i
          · subst hj
            have h1 := hy j
            have h2 := hx₀ j
            by_cases hlt : y j < x₀ j
            · have hbt : b = true := by simp [hb, hlt]
              simp [xsch_dir, hbt, unit]
              omega
            · have hbf : b = false := by simp [hb, hlt]
              simp [xsch_dir, hbf, unit]
              omega
          · have h3 : (y + xsch_dir (i, b)) j = y j := by
              by_cases hbt : b = true
              · simp [xsch_dir, hbt, unit, Pi.single_eq_of_ne hj]
              · simp [xsch_dir, hbt, unit, Pi.single_eq_of_ne hj]
            rw [h3]
            exact hy j
        have hless : ((y + xsch_dir (i, b)) i - x₀ i).natAbs < n := by
          rw [← hn]
          by_cases hlt : y i < x₀ i
          · have hbt : b = true := by simp [hb, hlt]
            simp [xsch_dir, hbt, unit]
            omega
          · have hbf : b = false := by simp [hb, hlt]
            simp [xsch_dir, hbf, unit]
            omega
        refine xsch_Top.nbr ({(i, b)} : Finset (Fin d × Bool)) hy ?_ ?_ ?_
        · intro s hs
          rw [Finset.mem_singleton] at hs
          rw [hs]
          exact Finset.mem_singleton_self i
        · simp
        · intro s hs
          rw [Finset.mem_singleton] at hs
          rw [hs]
          exact ih _ hless _ hstep rfl
  exact fun y hy => key _ y hy rfl

variable {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]

/-- A segment along one direction fails to be spanned with probability at most `(1 - p)` to the
number of its sites. -/
theorem xs1_fail_le {i : Fin d} {lo hi : Site d} (hthin : ∀ j, j ≠ i → lo j = hi j) :
    (xsch_mu d p).real {η | ¬ xsch_Sp ({i} : Finset (Fin d)) (xsb_box lo hi) η}
      ≤ (1 - p) ^ (xsb_box lo hi).ncard := by
  have hd : 1 ≤ d := Fin.pos i
  have hfin := xsb_box_finite lo hi
  have hsub : {η : Site d → ℤ | ¬ xsch_Sp ({i} : Finset (Fin d)) (xsb_box lo hi) η}
      ⊆ {η : Site d → ℤ | ∀ x ∈ hfin.toFinset, η x ≠ 2 * (d : ℤ)} := by
    intro η hη x hx hocc
    exact hη (xs1_sp_of_occ hthin ⟨x, hfin.mem_toFinset.mp hx, hocc⟩)
  calc (xsch_mu d p).real {η | ¬ xsch_Sp ({i} : Finset (Fin d)) (xsb_box lo hi) η}
      ≤ (xsch_mu d p).real
          {η : Site d → ℤ | ∀ x ∈ hfin.toFinset, η x ≠ 2 * (d : ℤ)} :=
        measureReal_mono hsub
    _ = (1 - p) ^ hfin.toFinset.card := xsch5_not_occ_prob hd hfin.toFinset
    _ = (1 - p) ^ (xsb_box lo hi).ncard := by
        rw [Set.ncard_eq_toFinset_card _ hfin]

/-- A power of `1 - p` decays faster than any polynomial: `s^Q (1 - p)^s` is bounded. -/
theorem xs1_pow_le (hp : 0 < p) (Q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s → (1 - p) ^ s ≤ c / (s : ℝ) ^ Q := by
  have hp1 := (Fact.out : 0 ≤ p ∧ p ≤ 1).2
  have hr : |1 - p| < 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one Q hr
  obtain ⟨b, hb⟩ := ht.bddAbove_range
  refine ⟨max b 1, lt_max_of_lt_right one_pos, fun s hs => ?_⟩
  have hs0 : (0 : ℝ) < (s : ℝ) ^ Q := by
    have : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    positivity
  rw [le_div_iff₀ hs0]
  have h1 : (s : ℝ) ^ Q * (1 - p) ^ s ≤ b := hb ⟨s, rfl⟩
  calc (1 - p) ^ s * (s : ℝ) ^ Q = (s : ℝ) ^ Q * (1 - p) ^ s := by ring
    _ ≤ b := h1
    _ ≤ max b 1 := le_max_left _ _

/-- **Level one.**  Segments along one direction fail to be spanned with a probability decaying
faster than any polynomial in their length. -/
theorem xs1_decay (hp : 0 < p) : xsb_Decay d p 1 := by
  intro Q
  obtain ⟨c, hc, hcQ⟩ := xs1_pow_le (p := p) hp Q
  refine ⟨c, hc, fun J lo hi s hJ hs hnear => ?_⟩
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hJ
  have hthin : ∀ j, j ≠ i → lo j = hi j := fun j hj =>
    hnear.2 j (by simpa using hj)
  have hfail := xs1_fail_le (p := p) hthin
  have hp1 := (Fact.out : 0 ≤ p ∧ p ≤ 1).2
  have hs' : s ≤ (xsb_box lo hi).ncard := by
    rcases hnear.1 i (Finset.mem_singleton_self i) with h | h
    · have := xsp_box_ncard (J := {i}) (lo := lo) (hi := hi) (ℓ := s)
        (fun j hj => by rw [Finset.mem_singleton] at hj; subst hj; exact h) (fun j hj =>
          hnear.2 j hj)
      rw [this]; simp
    · have := xsp_box_ncard (J := {i}) (lo := lo) (hi := hi) (ℓ := s + 1)
        (fun j hj => by rw [Finset.mem_singleton] at hj; subst hj; exact_mod_cast h)
        (fun j hj => hnear.2 j hj)
      rw [this]; simp
  calc (xsch_mu d p).real {η | ¬ xsch_Sp ({i} : Finset (Fin d)) (xsb_box lo hi) η}
      ≤ (1 - p) ^ (xsb_box lo hi).ncard := hfail
    _ ≤ (1 - p) ^ s := pow_le_pow_of_le_one (by linarith) (by linarith) hs'
    _ ≤ c / (s : ℝ) ^ Q := hcQ s hs

end Exploding
