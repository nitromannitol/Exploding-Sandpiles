/-
The probability that some layer of the growth schedule is not spanned is at most `|J|` times the
sum, over the sizes `a` from `L` to `s`, of the bound `g a` for the failure of a near-cube box
of size `a` in one dimension less.  Each layer is a near-cube of size `L + t / |J|` along
`J.erase (dir t)` (or empty), and each size occurs at most `|J|` times.
-/
import Exploding.Support.ExtSchSchedLayer
import Exploding.Support.ExtSchProb

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

section GrowProb
variable {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (P : xss_Plan d) {s : ℕ}

/-- Summing a nonnegative bound over the layer sizes of the schedule counts each size at most
`|J|` times. -/
theorem xsq_sum_le (hP : xss_Valid P s) {g : ℕ → ℝ} (hg0 : ∀ a, 0 ≤ g a) :
    ∑ t ∈ Finset.range (xss_steps P s), g (P.L + t / P.J.card)
      ≤ (P.J.card : ℝ) * ∑ a ∈ Finset.Icc P.L s, g a := by
  have hmaps : ∀ t ∈ Finset.range (xss_steps P s),
      P.L + t / P.J.card ∈ Finset.Icc P.L s := fun t ht =>
    Finset.mem_Icc.mpr ⟨Nat.le_add_right _ _, xss_level_le P hP (Finset.mem_range.mp ht)⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps g, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.range (xss_steps P s)).filter
      (fun t => P.L + t / P.J.card = a)).card : ℝ) ≤ P.J.card :=
    Nat.cast_le.mpr (xss_count_le P hP a)
  exact mul_le_mul_of_nonneg_right hcard (hg0 a)

omit [Fact (0 ≤ p ∧ p ≤ 1)] in
/-- The failure of a single layer is bounded by the bound for near-cube boxes of its size. -/
theorem xsq_layer_fail_le (hP : xss_Valid P s) (hL : 1 ≤ P.L) {g : ℕ → ℝ}
    (hg0 : ∀ a, 0 ≤ g a)
    (hg : ∀ (J' : Finset (Fin d)) (lo hi : Site d) (a : ℕ), J'.card = P.J.card - 1 → 1 ≤ a →
      xsb_Near J' a lo hi →
        (xsch_mu d p).real {η | ¬ xsch_Sp J' (xsb_box lo hi) η} ≤ g a)
    {t : ℕ} (ht : t < xss_steps P s) :
    (xsch_mu d p).real
        {η | ¬ xsch_Sp (P.J.erase (xss_dir P hP.1 t)) (xss_layer P t) η}
      ≤ g (P.L + t / P.J.card) := by
  rcases xss_layer_near P hP ht with h | ⟨lo, hi, hnear, h⟩
  · have hempty : {η : Site d → ℤ |
        ¬ xsch_Sp (P.J.erase (xss_dir P hP.1 t)) (xss_layer P t) η} = ∅ := by
      ext η
      simp [xsch_Sp, h]
    rw [hempty, measureReal_empty]
    exact hg0 _
  · rw [h]
    exact hg _ lo hi _ (Finset.card_erase_of_mem (xss_dir_mem P hP.1 t))
      (le_trans hL (Nat.le_add_right _ _)) hnear

omit [Fact (0 ≤ p ∧ p ≤ 1)] in
/-- **Union bound over the layers of the schedule.** -/
theorem xsr_layers_fail_le (hP : xss_Valid P s) (hL : 1 ≤ P.L) {g : ℕ → ℝ}
    (hg0 : ∀ a, 0 ≤ g a)
    (hg : ∀ (J' : Finset (Fin d)) (lo hi : Site d) (a : ℕ), J'.card = P.J.card - 1 → 1 ≤ a →
      xsb_Near J' a lo hi →
        (xsch_mu d p).real {η | ¬ xsch_Sp J' (xsb_box lo hi) η} ≤ g a) :
    (xsch_mu d p).real {η | ¬ ∀ t < xss_steps P s,
        xsch_Sp (P.J.erase (xss_dir P hP.1 t)) (xss_layer P t) η}
      ≤ (P.J.card : ℝ) * ∑ a ∈ Finset.Icc P.L s, g a := by
  have hset : {η : Site d → ℤ | ¬ ∀ t < xss_steps P s,
      xsch_Sp (P.J.erase (xss_dir P hP.1 t)) (xss_layer P t) η} =
      ⋃ t ∈ Finset.range (xss_steps P s),
        {η | ¬ xsch_Sp (P.J.erase (xss_dir P hP.1 t)) (xss_layer P t) η} := by
    ext η
    simp [Set.mem_iUnion, not_forall]
  rw [hset]
  calc (xsch_mu d p).real (⋃ t ∈ Finset.range (xss_steps P s),
        {η | ¬ xsch_Sp (P.J.erase (xss_dir P hP.1 t)) (xss_layer P t) η})
      ≤ ∑ t ∈ Finset.range (xss_steps P s), (xsch_mu d p).real
          {η | ¬ xsch_Sp (P.J.erase (xss_dir P hP.1 t)) (xss_layer P t) η} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ t ∈ Finset.range (xss_steps P s), g (P.L + t / P.J.card) :=
        Finset.sum_le_sum fun t ht =>
          xsq_layer_fail_le P hP hL hg0 hg (Finset.mem_range.mp ht)
    _ ≤ (P.J.card : ℝ) * ∑ a ∈ Finset.Icc P.L s, g a := xsq_sum_le P hP hg0
end GrowProb

end Exploding
