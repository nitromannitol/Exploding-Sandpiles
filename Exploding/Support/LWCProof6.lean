/-
Proposition 3.1's moment-free Kingman conjunct (declarations `lwc6_*`).

This file isolates the purely analytic step and the Kingman step.  The analytic step
extends a subadditive, naturally homogeneous, linearly bounded function on the
lattice `ℤ^d` to a continuous, convex, one-homogeneous function on `ℝ^d`; the Kingman
step produces the lattice function from `mk_kingman_linear` and the `lwc_*` shift
machinery.
-/
import Exploding.Support.LWCProof4
import Mathlib.Analysis.Convex.Continuous

open Exploding LatticeProb MeasureTheory Filter
open scoped BigOperators

namespace Exploding

variable {d : ℕ}

/-! ### Extending a subadditive homogeneous lattice bound -/

/-- A finite nonnegative real combination of lattice sites representing `y`, with its
`L`-cost. -/
def lwc6_Rep (L : Site d → ℝ) (y : Fin d → ℝ) (r : ℝ) : Prop :=
  ∃ (s : Finset (Site d)) (lam : Site d → ℝ),
    (∀ w ∈ s, 0 ≤ lam w) ∧
    (∑ w ∈ s, lam w • lwc2_toReal w = y) ∧
    r = ∑ w ∈ s, lam w * L w

/-- The infimum of the costs of the representations of `y`. -/
noncomputable def lwc6_infN (L : Site d → ℝ) (y : Fin d → ℝ) : ℝ :=
  sInf {r : ℝ | lwc6_Rep L y r}

/-- `unit i = unit j` exactly when `i = j`. -/
theorem lwc6_unit_eq_iff {i j : Fin d} : (unit i : Site d) = unit j ↔ i = j := by
  constructor
  · intro h
    have hc := congrFun h i
    simp only [unit, Pi.single_apply] at hc
    by_cases hij : i = j
    · exact hij
    · rw [if_neg hij] at hc
      norm_num at hc
  · rintro rfl; rfl

/-- A unit vector is never the negative of a unit vector. -/
theorem lwc6_unit_ne_neg {i j : Fin d} : (unit i : Site d) ≠ -unit j := by
  intro h
  have hc := congrFun h i
  simp only [unit, Pi.single_apply, Pi.neg_apply] at hc
  by_cases hij : i = j
  · rw [if_pos hij] at hc
    norm_num at hc
  · rw [if_neg hij] at hc
    norm_num at hc

/-- Representing by the positive and negative parts against the unit vectors. -/
theorem lwc6_rep_nonempty (L : Site d → ℝ) (y : Fin d → ℝ) :
    ∃ r, lwc6_Rep L y r := by
  classical
  let v : Fin d ⊕ Fin d → Site d := Sum.elim (fun i => unit i) (fun i => -unit i)
  let c : Fin d ⊕ Fin d → ℝ :=
    Sum.elim (fun i => max (y i) 0) (fun i => max (-(y i)) 0)
  have hv : Function.Injective v := by
    rintro (i1 | i1) (i2 | i2) h
    · exact congrArg Sum.inl (lwc6_unit_eq_iff.mp h)
    · exact absurd h lwc6_unit_ne_neg
    · exact absurd h.symm lwc6_unit_ne_neg
    · exact congrArg Sum.inr (lwc6_unit_eq_iff.mp (neg_inj.mp h))
  let s : Finset (Site d) := (Finset.univ : Finset (Fin d ⊕ Fin d)).image v
  let lam : Site d → ℝ := fun w =>
    ∑ e ∈ (Finset.univ : Finset (Fin d ⊕ Fin d)).filter (fun e => v e = w), c e
  have hlam : ∀ e, lam (v e) = c e := by
    intro e
    have hfilter : (Finset.univ.filter (fun e' => v e' = v e)) = {e} := by
      ext e'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact hv h
      · intro h; rw [h]
    simp only [lam]
    rw [hfilter, Finset.sum_singleton]
  refine ⟨∑ w ∈ s, lam w * L w, s, lam, ?_, ?_, rfl⟩
  · intro w _
    exact Finset.sum_nonneg fun e _ => by
      rcases e with i | i <;> simp only [c, Sum.elim_inl, Sum.elim_inr] <;> positivity
  · calc ∑ w ∈ s, lam w • lwc2_toReal w
        = ∑ e ∈ (Finset.univ : Finset (Fin d ⊕ Fin d)), lam (v e) • lwc2_toReal (v e) := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          exact hv hab
      _ = ∑ e ∈ (Finset.univ : Finset (Fin d ⊕ Fin d)), c e • lwc2_toReal (v e) := by
          exact Finset.sum_congr rfl fun e _ => by rw [hlam]
      _ = y := by
          funext i
          have h1 : (∑ i1 : Fin d, (c (Sum.inl i1) • lwc2_toReal (v (Sum.inl i1))) i)
              = max (y i) 0 := by
            rw [Finset.sum_eq_single i]
            · simp [c, v, Sum.elim_inl, lwc2_toReal, unit, Pi.smul_apply]
            · intro b _ hb
              simp [c, v, Sum.elim_inl, lwc2_toReal, unit, Pi.smul_apply,
                Ne.symm hb]
            · intro hi; exact absurd (Finset.mem_univ i) hi
          have h2 : (∑ i2 : Fin d, (c (Sum.inr i2) • lwc2_toReal (v (Sum.inr i2))) i)
              = -(max (-(y i)) 0) := by
            rw [Finset.sum_eq_single i]
            · simp [c, v, Sum.elim_inr, lwc2_toReal, unit, Pi.neg_apply, Pi.smul_apply]
            · intro b _ hb
              simp [c, v, Sum.elim_inr, lwc2_toReal, unit, Pi.neg_apply, Pi.smul_apply,
                Ne.symm hb]
            · intro hi; exact absurd (Finset.mem_univ i) hi
          rw [Finset.sum_apply, Fintype.sum_sum_type]
          rw [h1, h2]
          change max (y i) 0 - max (-(y i)) 0 = y i
          rw [max_zero_sub_max_neg_zero_eq_self]

/-- Representations combine: the union of the supports and the sum of the coefficients. -/
theorem lwc6_rep_add {L : Site d → ℝ} {y₁ y₂ : Fin d → ℝ} {r₁ r₂ : ℝ}
    (h₁ : lwc6_Rep L y₁ r₁) (h₂ : lwc6_Rep L y₂ r₂) :
    lwc6_Rep L (y₁ + y₂) (r₁ + r₂) := by
  obtain ⟨s₁, lam₁, hnn₁, hv₁, hr₁⟩ := h₁
  obtain ⟨s₂, lam₂, hnn₂, hv₂, hr₂⟩ := h₂
  refine ⟨s₁ ∪ s₂, fun w => (if w ∈ s₁ then lam₁ w else 0) + (if w ∈ s₂ then lam₂ w else 0),
    ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · have h1 : 0 ≤ (if w ∈ s₁ then lam₁ w else 0) := by rw [if_pos hw]; exact hnn₁ w hw
      have h2 : 0 ≤ (if w ∈ s₂ then lam₂ w else 0) := by
        by_cases h : w ∈ s₂
        · rw [if_pos h]; exact hnn₂ w h
        · rw [if_neg h]
      linarith
    · have h2 : 0 ≤ (if w ∈ s₂ then lam₂ w else 0) := by rw [if_pos hw]; exact hnn₂ w hw
      have h1 : 0 ≤ (if w ∈ s₁ then lam₁ w else 0) := by
        by_cases h : w ∈ s₁
        · rw [if_pos h]; exact hnn₁ w h
        · rw [if_neg h]
      linarith
  · have h1 : ∑ w ∈ s₁ ∪ s₂, (if w ∈ s₁ then lam₁ w else 0) • lwc2_toReal w = y₁ := by
      rw [← hv₁]
      calc ∑ w ∈ s₁ ∪ s₂, (if w ∈ s₁ then lam₁ w else 0) • lwc2_toReal w
          = ∑ w ∈ s₁, (if w ∈ s₁ then lam₁ w else 0) • lwc2_toReal w :=
            (Finset.sum_subset (Finset.subset_union_left) (fun w _ hw => by rw [if_neg hw, zero_smul])).symm
        _ = ∑ w ∈ s₁, lam₁ w • lwc2_toReal w :=
            Finset.sum_congr rfl fun w hw => by rw [if_pos hw]
    have h2 : ∑ w ∈ s₁ ∪ s₂, (if w ∈ s₂ then lam₂ w else 0) • lwc2_toReal w = y₂ := by
      rw [← hv₂]
      calc ∑ w ∈ s₁ ∪ s₂, (if w ∈ s₂ then lam₂ w else 0) • lwc2_toReal w
          = ∑ w ∈ s₂, (if w ∈ s₂ then lam₂ w else 0) • lwc2_toReal w :=
            (Finset.sum_subset (Finset.subset_union_right) (fun w _ hw => by rw [if_neg hw, zero_smul])).symm
        _ = ∑ w ∈ s₂, lam₂ w • lwc2_toReal w :=
            Finset.sum_congr rfl fun w hw => by rw [if_pos hw]
    calc ∑ w ∈ s₁ ∪ s₂,
          ((if w ∈ s₁ then lam₁ w else 0) + (if w ∈ s₂ then lam₂ w else 0)) • lwc2_toReal w
        = ∑ w ∈ s₁ ∪ s₂, ((if w ∈ s₁ then lam₁ w else 0) • lwc2_toReal w
            + (if w ∈ s₂ then lam₂ w else 0) • lwc2_toReal w) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [add_smul]
      _ = y₁ + y₂ := by rw [Finset.sum_add_distrib, h1, h2]
  · have h1 : ∑ w ∈ s₁ ∪ s₂, (if w ∈ s₁ then lam₁ w else 0) * L w
        = ∑ w ∈ s₁, lam₁ w * L w := by
      calc ∑ w ∈ s₁ ∪ s₂, (if w ∈ s₁ then lam₁ w else 0) * L w
          = ∑ w ∈ s₁, (if w ∈ s₁ then lam₁ w else 0) * L w :=
            (Finset.sum_subset (Finset.subset_union_left) (fun w _ hw => by rw [if_neg hw, zero_mul])).symm
        _ = ∑ w ∈ s₁, lam₁ w * L w :=
            Finset.sum_congr rfl fun w hw => by rw [if_pos hw]
    have h2 : ∑ w ∈ s₁ ∪ s₂, (if w ∈ s₂ then lam₂ w else 0) * L w
        = ∑ w ∈ s₂, lam₂ w * L w := by
      calc ∑ w ∈ s₁ ∪ s₂, (if w ∈ s₂ then lam₂ w else 0) * L w
          = ∑ w ∈ s₂, (if w ∈ s₂ then lam₂ w else 0) * L w :=
            (Finset.sum_subset (Finset.subset_union_right) (fun w _ hw => by rw [if_neg hw, zero_mul])).symm
        _ = ∑ w ∈ s₂, lam₂ w * L w :=
            Finset.sum_congr rfl fun w hw => by rw [if_pos hw]
    rw [hr₁, hr₂, ← h1, ← h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

/-- A representation cost is nonnegative when `L ≥ 0`. -/
theorem lwc6_rep_cost_nonneg {L : Site d → ℝ} (hnonneg : ∀ v, 0 ≤ L v) {y : Fin d → ℝ}
    {r : ℝ} (h : lwc6_Rep L y r) : 0 ≤ r := by
  obtain ⟨s, lam, hnn, _hv, rfl⟩ := h
  exact Finset.sum_nonneg fun w hw => mul_nonneg (hnn w hw) (hnonneg w)

/-- `0` is a lower bound of the representation costs when `L ≥ 0`. -/
theorem lwc6_rep_bddBelow {L : Site d → ℝ} (hnonneg : ∀ v, 0 ≤ L v) (y : Fin d → ℝ) :
    BddBelow {r : ℝ | lwc6_Rep L y r} :=
  ⟨0, fun _ hr => lwc6_rep_cost_nonneg hnonneg hr⟩

/-- `lwc6_infN` is nonnegative when `L ≥ 0`. -/
theorem lwc6_infN_nonneg {L : Site d → ℝ} (hnonneg : ∀ v, 0 ≤ L v) (y : Fin d → ℝ) :
    0 ≤ lwc6_infN L y :=
  le_csInf (lwc6_rep_nonempty L y) fun _ hr => lwc6_rep_cost_nonneg hnonneg hr

/-- The defining upper bound of `lwc6_infN`. -/
theorem lwc6_infN_le {L : Site d → ℝ} (hnonneg : ∀ v, 0 ≤ L v) {y : Fin d → ℝ} {r : ℝ}
    (h : lwc6_Rep L y r) : lwc6_infN L y ≤ r :=
  csInf_le (lwc6_rep_bddBelow hnonneg y) h

/-- `lwc6_infN` is subadditive. -/
theorem lwc6_infN_add {L : Site d → ℝ} (hnonneg : ∀ v, 0 ≤ L v) (y₁ y₂ : Fin d → ℝ) :
    lwc6_infN L (y₁ + y₂) ≤ lwc6_infN L y₁ + lwc6_infN L y₂ := by
  have hle : ∀ r₁, lwc6_Rep L y₁ r₁ →
      lwc6_infN L (y₁ + y₂) - lwc6_infN L y₂ ≤ r₁ := by
    intro r₁ h1
    have hle2 : ∀ r₂, lwc6_Rep L y₂ r₂ → lwc6_infN L (y₁ + y₂) - r₁ ≤ r₂ := by
      intro r₂ h2
      have := lwc6_infN_le hnonneg (lwc6_rep_add h1 h2)
      linarith
    have := le_csInf (lwc6_rep_nonempty L y₂) fun r₂ hr₂ => hle2 r₂ hr₂
    change lwc6_infN L (y₁ + y₂) - r₁ ≤ lwc6_infN L y₂ at this
    linarith
  have := le_csInf (lwc6_rep_nonempty L y₁) fun r₁ hr₁ => hle r₁ hr₁
  change lwc6_infN L (y₁ + y₂) - lwc6_infN L y₂ ≤ lwc6_infN L y₁ at this
  linarith

/-- `lwc6_infN` is positively homogeneous (for a nonnegative `L`). -/
theorem lwc6_infN_smul {L : Site d → ℝ} (hnonneg : ∀ v, 0 ≤ L v) (y : Fin d → ℝ)
    {c : ℝ} (hc : 0 ≤ c) : lwc6_infN L (c • y) = c * lwc6_infN L y := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · have h0 : lwc6_infN L (0 : Fin d → ℝ) = 0 := by
      refine le_antisymm ?_ (lwc6_infN_nonneg hnonneg 0)
      refine lwc6_infN_le hnonneg ⟨∅, fun _ => 0, by simp, ?_, ?_⟩
      · simp
      · simp
    simp [h0]
  · apply le_antisymm
    · have hle : ∀ r, lwc6_Rep L y r → lwc6_infN L (c • y) / c ≤ r := by
        intro r hr
        rw [div_le_iff₀ hcpos]
        obtain ⟨s, lam, hnn, hv, hr'⟩ := hr
        refine lwc6_infN_le hnonneg (show lwc6_Rep L (c • y) (r * c) from
          ⟨s, fun w => c * lam w, ?_, ?_, ?_⟩)
        · intro w hw; exact mul_nonneg hc (hnn w hw)
        · rw [← hv, Finset.smul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          change (c * lam w) • lwc2_toReal w = c • (lam w • lwc2_toReal w)
          rw [mul_smul]
        · rw [hr', Finset.sum_mul]
          refine Finset.sum_congr rfl fun w _ => ?_
          ring
      have h := le_csInf (lwc6_rep_nonempty L y) hle
      change lwc6_infN L (c • y) / c ≤ lwc6_infN L y at h
      rw [div_le_iff₀ hcpos] at h
      linarith
    · have hle : ∀ r, lwc6_Rep L (c • y) r → c * lwc6_infN L y ≤ r := by
        intro r hr
        obtain ⟨s, lam, hnn, hv, hr'⟩ := hr
        have hrep : lwc6_Rep L y (r / c) := by
          refine ⟨s, fun w => lam w / c, ?_, ?_, ?_⟩
          · intro w hw; exact div_nonneg (hnn w hw) hc
          · have hsum : ∑ w ∈ s, (lam w / c) • lwc2_toReal w = c⁻¹ • (c • y) := by
              rw [← hv, Finset.smul_sum]
              refine Finset.sum_congr rfl fun w _ => ?_
              rw [div_eq_inv_mul, mul_smul]
            rw [hsum, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
          · rw [hr', Finset.sum_div]
            refine Finset.sum_congr rfl fun w _ => ?_
            ring
        have hN := lwc6_infN_le hnonneg hrep
        rw [le_div_iff₀ hcpos] at hN
        linarith
      have h := le_csInf (lwc6_rep_nonempty L (c • y)) hle
      change c * lwc6_infN L y ≤ lwc6_infN L (c • y) at h
      exact h

/-- `lwc2_toReal` is additive. -/
theorem lwc6_toReal_add (a b : Site d) :
    lwc2_toReal (a + b) = lwc2_toReal a + lwc2_toReal b := by
  funext i; simp [lwc2_toReal]

/-- `lwc2_toReal` is `ℤ`-linear. -/
theorem lwc6_toReal_zsmul (k : ℤ) (a : Site d) :
    lwc2_toReal (k • a) = (k : ℝ) • lwc2_toReal a := by
  funext i; simp [lwc2_toReal]

/-- `lwc2_toReal` of an integer sum. -/
theorem lwc6_toReal_sum (s : Finset (Site d)) (n : Site d → ℤ) :
    lwc2_toReal (∑ w ∈ s, n w • w) = ∑ w ∈ s, (n w : ℝ) • lwc2_toReal w := by
  classical
  induction s using Finset.induction with
  | empty => funext i; simp [lwc2_toReal]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, lwc6_toReal_add, ih,
        lwc6_toReal_zsmul]

/-- Integer-coefficient subadditivity of `L`. -/
theorem lwc6_L_int_sum {L : Site d → ℝ} (hsub : ∀ u v, L (u + v) ≤ L u + L v)
    (hhom : ∀ (k : ℕ) (v : Site d), L ((k : ℤ) • v) = (k : ℝ) * L v)
    (s : Finset (Site d)) (n : Site d → ℤ) (hn : ∀ w ∈ s, 0 ≤ n w) :
    L (∑ w ∈ s, n w • w) ≤ ∑ w ∈ s, (n w : ℝ) * L w := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : L 0 = 0 := by simpa using hhom 0 0
      simp [h0]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hna : 0 ≤ n a := hn a (Finset.mem_insert_self a s)
      have hns : ∀ w ∈ s, 0 ≤ n w := fun w hw => hn w (Finset.mem_insert_of_mem hw)
      have hta : L (n a • a) = (n a : ℝ) * L a := by
        have h := hhom (n a).toNat a
        have hcast : (((n a).toNat : ℤ)) = n a := Int.toNat_of_nonneg hna
        rw [hcast] at h
        have hcastR : (((n a).toNat : ℕ) : ℝ) = (n a : ℝ) := by
          rw [← Int.cast_natCast]
          exact congrArg (fun z : ℤ => (z : ℝ)) hcast
        rwa [hcastR] at h
      calc L (n a • a + ∑ w ∈ s, n w • w)
          ≤ L (n a • a) + L (∑ w ∈ s, n w • w) := hsub _ _
        _ ≤ (n a : ℝ) * L a + ∑ w ∈ s, (n w : ℝ) * L w := by
            rw [hta]
            exact add_le_add le_rfl (ih hns)

/-- `lwc6_infN` is convex (subadditivity plus positive homogeneity). -/
theorem lwc6_infN_convex {L : Site d → ℝ} (hnonneg : ∀ v, 0 ≤ L v) :
    ConvexOn ℝ Set.univ (lwc6_infN L) :=
  ⟨convex_univ, fun x _ y _ a b ha hb _hab => by
    calc lwc6_infN L (a • x + b • y)
        ≤ lwc6_infN L (a • x) + lwc6_infN L (b • y) := lwc6_infN_add hnonneg _ _
      _ = a * lwc6_infN L x + b * lwc6_infN L y := by
          rw [lwc6_infN_smul hnonneg x ha, lwc6_infN_smul hnonneg y hb]⟩

end Exploding
