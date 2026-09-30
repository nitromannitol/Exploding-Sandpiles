/-
Packet AS-5: the last claim `hpodo` of
`Exploding.Frozen.approximate_subadditive`.  Sorry-free support file.

The pile `σ = explodingPile η` has `σ x = η x ≤ 2d - 1` off the origin, so no
site other than the origin is initially unstable.  A first toppling at any site
is therefore triggered by an already-toppled neighbour, so every toppling is
connected back to the origin: if the pile is not stabilizable, the origin itself
must topple.  This is the first ingredient of the `origin-max + Lipschitz`
route (the others are `assp_podo_inv` and `as3_podo_support_le_time`).
-/
import Exploding.Support.ASProof
import Exploding.Support.ASProof2
import Exploding.Support.ASSpecial

open Exploding LatticeProb MeasureTheory

set_option linter.unusedVariables false

/-- Any toppling of `podo σ` is preceded by a toppling of the origin, when the
only possibly unstable site is the origin. -/
theorem as5_topple_implies_origin {d : ℕ} (σ : Site d → ℤ)
    (hhigh : ∀ x, x ≠ 0 → σ x ≤ 2 * (d : ℤ) - 1) :
    ∀ t x, 0 < podo σ t x → ∃ s : ℕ, s ≤ t ∧ 0 < podo σ s (0 : Site d) := by
  intro t
  induction t with
  | zero => intro x h; simp [podo_zero] at h
  | succ t ih =>
    intro x hx
    by_cases hprev : 0 < podo σ t x
    · obtain ⟨s, hs, hspos⟩ := ih x hprev
      exact ⟨s, le_trans hs (Nat.le_succ t), hspos⟩
    · by_cases hx0 : x = (0 : Site d)
      · subst hx0
        exact ⟨t + 1, le_refl _, hx⟩
      · have hxzero : podo σ t x = 0 := by
          have := as_podo_nonneg σ t x; omega
        rw [podo_succ] at hx
        by_cases hc : 2 * (d : ℤ) ≤ pconf σ t x
        · have hnbr : 0 < nbrSumZ (podo σ t) x := by
            simp only [pconf, lap, hxzero, mul_zero, sub_zero] at hc
            have hs := hhigh x hx0
            omega
          obtain ⟨y, _hyx, hypos⟩ := exists_adj_pos_of_nbrSumZ_pos (podo σ t)
            (fun y => as_podo_nonneg σ t y) x hnbr
          obtain ⟨s, hs, hspos⟩ := ih y hypos
          exact ⟨s, le_trans hs (Nat.le_succ t), hspos⟩
        · rw [if_neg hc] at hx
          rw [hxzero] at hx
          simp at hx

/-- On a background bounded by `2d - 1` off the origin, a non-stabilizable pile
topples the origin. -/
theorem as5_origin_topples_of_not_stabilizable {d : ℕ} (hd : 1 ≤ d) (σ : Site d → ℤ)
    (hhigh : ∀ x, x ≠ 0 → σ x ≤ 2 * (d : ℤ) - 1) (hnstab : ¬ Stabilizable σ) :
    ∃ t : ℕ, 0 < podo σ t (0 : Site d) := by
  have hne : ({x : Site d | ∃ t : ℕ, 0 < podo σ t x}).Nonempty := by
    by_contra hcon
    have hfin : ({x : Site d | ∃ t : ℕ, 0 < podo σ t x}).Finite := by
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      rw [hcon]; exact Set.finite_empty
    exact hnstab (as2_finite_toppling_set_stabilizable hd σ hfin)
  obtain ⟨x, t, ht⟩ := hne
  obtain ⟨s, _hs, hspos⟩ := as5_topple_implies_origin σ hhigh t x ht
  exact ⟨s, hspos⟩
