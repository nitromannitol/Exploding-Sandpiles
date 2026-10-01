/-
The Kingman conjunct of Proposition 3.1 (declarations `lwc7_*`), taking
`mk_kingman_linear` as a hypothesis.

`LWCProof6.lean` built the extension `lwc6_infN` of a lattice bound `L` and proved
that it is nonnegative, subadditive, positively homogeneous and convex.  This file
supplies the missing analytic links -- the floor comparison identifying `lwc6_infN`
with `L` on lattice points, the linear bound and continuity -- and then applies
`mk_kingman_linear` to the penultimate-cluster arrival cocycle along a fixed
lattice direction to produce the limit shape `N` of Proposition 3.1.
-/
import Exploding.Support.LWCProof6
import Exploding.Support.MKingman

open Exploding LatticeProb MeasureTheory Filter
open scoped BigOperators

namespace Exploding

variable {d : ℕ}

/-! ### The floor comparison -/

/-- `lwc2_toReal` preserves subtraction. -/
theorem lwc7_toReal_neg (a : Site d) : lwc2_toReal (-a) = -lwc2_toReal a := by
  funext i; simp [lwc2_toReal]

theorem lwc7_toReal_sub (a b : Site d) :
    lwc2_toReal (a - b) = lwc2_toReal a - lwc2_toReal b := by
  rw [sub_eq_add_neg, lwc6_toReal_add, lwc7_toReal_neg]
  rfl

/-- Manhattan norm of a real combination of lattice vectors. -/
theorem lwc7_mnorm_le_sum_abs {w : Site d} {s : Finset (Site d)} (c : Site d → ℝ)
    (hc : lwc2_toReal w = ∑ x ∈ s, c x • lwc2_toReal x) :
    (mnorm w : ℝ) ≤ ∑ x ∈ s, |c x| * (mnorm x : ℝ) := by
  have hcoord : ∀ i, (w i : ℝ) = ∑ x ∈ s, c x * (x i : ℝ) := by
    intro i
    have := congrFun hc i
    simpa [lwc2_toReal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  calc (mnorm w : ℝ) = ∑ i, |(w i : ℝ)| := by simp [mnorm]
    _ = ∑ i, |∑ x ∈ s, c x * (x i : ℝ)| := by simp only [hcoord]
    _ ≤ ∑ i, ∑ x ∈ s, |c x * (x i : ℝ)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ x ∈ s, |c x| * |(x i : ℝ)| := by simp only [abs_mul]
    _ = ∑ x ∈ s, ∑ i, |c x| * |(x i : ℝ)| := Finset.sum_comm
    _ = ∑ x ∈ s, |c x| * ∑ i, |(x i : ℝ)| := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ x ∈ s, |c x| * (mnorm x : ℝ) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        congr 1
        simp [mnorm]

/-- The Lipschitz comparison for a lattice bound. -/
theorem lwc7_L_le_add {L : Site d → ℝ} (hsub : ∀ u v, L (u + v) ≤ L u + L v)
    (C : ℝ) (hbound : ∀ v, L v ≤ C * (mnorm v : ℝ)) (a b : Site d) :
    L a ≤ L b + C * (mnorm (a - b) : ℝ) := by
  have h1 : L a ≤ L b + L (a - b) := by
    have := hsub b (a - b)
    rwa [show b + (a - b) = a by abel] at this
  linarith [hbound (a - b)]

/-- **Floor comparison.**  The `L`-cost of any nonnegative finite real
representation of a lattice point is at least the value of `L` there. -/
theorem lwc7_L_le_rep {L : Site d → ℝ}
    (hsub : ∀ u v, L (u + v) ≤ L u + L v)
    (hhom : ∀ (k : ℕ) (v : Site d), L ((k : ℤ) • v) = (k : ℝ) * L v)
    (hnonneg : ∀ v, 0 ≤ L v)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, L v ≤ C * (mnorm v : ℝ))
    {v : Site d} {r : ℝ} (h : lwc6_Rep L (lwc2_toReal v) r) : L v ≤ r := by
  obtain ⟨s, lam, hnn, hv, hr⟩ := h
  set Ms : ℝ := ∑ w ∈ s, (mnorm w : ℝ) with hMs
  have hMs_nonneg : 0 ≤ Ms := by
    rw [hMs]
    exact Finset.sum_nonneg fun w _ => by exact_mod_cast pub_mnorm_nonneg w
  have hkey : ∀ q : ℕ, 1 ≤ q → L v ≤ r + C * Ms / q := by
    intro q hq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    set n : Site d → ℤ := fun w => if w ∈ s then ⌊lam w * q⌋ else 0 with hn
    set wq : Site d := ∑ w ∈ s, n w • w with hwq
    have hn_nonneg : ∀ w ∈ s, 0 ≤ n w := by
      intro w hw
      rw [hn]
      simp only [if_pos hw]
      exact (Int.floor_nonneg).mpr (mul_nonneg (hnn w hw) (Nat.cast_nonneg q))
    have hLwq : L wq ≤ ∑ w ∈ s, (n w : ℝ) * L w := lwc6_L_int_sum hsub hhom s n hn_nonneg
    have hwq_eq : lwc2_toReal wq = ∑ w ∈ s, (n w : ℝ) • lwc2_toReal w := by
      rw [hwq]; exact lwc6_toReal_sum s n
    have hv' : lwc2_toReal v = ∑ w ∈ s, lam w • lwc2_toReal w := hv.symm
    have hc : lwc2_toReal (wq - (q : ℤ) • v)
        = ∑ w ∈ s, ((n w : ℝ) - q * lam w) • lwc2_toReal w := by
      rw [lwc7_toReal_sub, hwq_eq, lwc6_toReal_zsmul, hv', Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← mul_smul, sub_smul]
      simp
    have hmnorm : (mnorm (wq - (q : ℤ) • v) : ℝ) ≤ Ms := by
      refine le_trans (lwc7_mnorm_le_sum_abs (fun w => (n w : ℝ) - q * lam w) hc) ?_
      rw [hMs]
      refine Finset.sum_le_sum fun w hw => ?_
      have h1 : (n w : ℝ) ≤ q * lam w := by
        rw [hn]; simp only [if_pos hw]
        rw [mul_comm (q : ℝ) (lam w)]
        exact Int.floor_le (lam w * q)
      have h2 : q * lam w < (n w : ℝ) + 1 := by
        rw [hn]; simp only [if_pos hw]
        rw [mul_comm (q : ℝ) (lam w)]
        exact Int.lt_floor_add_one (lam w * q)
      have habs : |(n w : ℝ) - q * lam w| ≤ 1 := by
        rw [abs_sub_le_iff]; constructor <;> linarith
      exact mul_le_of_le_one_left (by exact_mod_cast pub_mnorm_nonneg w) habs
    have hL : L ((q : ℤ) • v) ≤ L wq + C * (mnorm (wq - (q : ℤ) • v) : ℝ) := by
      have := lwc7_L_le_add hsub C hbound ((q : ℤ) • v) wq
      rwa [pub_mnorm_sub_comm] at this
    have hcost : ∑ w ∈ s, (n w : ℝ) * L w ≤ (q : ℝ) * r := by
      rw [hr]
      calc ∑ w ∈ s, (n w : ℝ) * L w ≤ ∑ w ∈ s, (q * lam w) * L w :=
            Finset.sum_le_sum fun w hw => by
              have h1 : (n w : ℝ) ≤ q * lam w := by
                rw [hn]; simp only [if_pos hw]
                rw [mul_comm (q : ℝ) (lam w)]
                exact Int.floor_le (lam w * q)
              exact mul_le_mul_of_nonneg_right h1 (hnonneg w)
        _ = (q : ℝ) * ∑ w ∈ s, lam w * L w := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun w _ => ?_
            ring
    have hmain : (q : ℝ) * L v ≤ (q : ℝ) * r + C * Ms := by
      have hLqv : L ((q : ℤ) • v) = (q : ℝ) * L v := hhom q v
      rw [← hLqv]
      calc L ((q : ℤ) • v) ≤ L wq + C * (mnorm (wq - (q : ℤ) • v) : ℝ) := hL
        _ ≤ (∑ w ∈ s, (n w : ℝ) * L w) + C * Ms :=
              add_le_add hLwq (mul_le_mul_of_nonneg_left hmnorm hC)
        _ ≤ (q : ℝ) * r + C * Ms := by linarith
    have hdiv : L v ≤ (q * r + C * Ms) / q := by
      rw [le_div_iff₀ hqR]
      nlinarith [hmain]
    have heq : (q * r + C * Ms) / q = r + C * Ms / q := by
      field_simp
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨q, hq⟩ := exists_nat_gt (C * Ms / ε)
  have hq1 : 1 ≤ q := by
    have h0 : 0 ≤ C * Ms / ε := by positivity
    have : (0 : ℝ) < q := lt_of_le_of_lt h0 hq
    exact_mod_cast this
  have hqε : C * Ms / q ≤ ε := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < q)]
    rw [div_lt_iff₀ hε] at hq
    linarith
  linarith [hkey q hq1]

/-- `lwc6_infN` is at most `L` on lattice points (the one-term representation). -/
theorem lwc7_infN_lattice_le {L : Site d → ℝ} (hnonneg : ∀ v, 0 ≤ L v) (v : Site d) :
    lwc6_infN L (lwc2_toReal v) ≤ L v := by
  refine lwc6_infN_le hnonneg ⟨{v}, fun w => if w = v then 1 else 0, ?_, ?_, ?_⟩
  · intro w hw
    by_cases hwv : w = v
    · simp [hwv]
    · simp [hwv]
  · rw [Finset.sum_singleton]
    simp
  · rw [Finset.sum_singleton]
    simp

/-- **Lattice identification.**  The extension of `L` agrees with `L` on lattice points. -/
theorem lwc7_infN_lattice_eq {L : Site d → ℝ}
    (hsub : ∀ u v, L (u + v) ≤ L u + L v)
    (hhom : ∀ (k : ℕ) (v : Site d), L ((k : ℤ) • v) = (k : ℝ) * L v)
    (hnonneg : ∀ v, 0 ≤ L v)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, L v ≤ C * (mnorm v : ℝ)) (v : Site d) :
    lwc6_infN L (lwc2_toReal v) = L v := by
  refine le_antisymm (lwc7_infN_lattice_le hnonneg v) ?_
  refine le_csInf (lwc6_rep_nonempty L (lwc2_toReal v)) fun r hr => lwc7_L_le_rep hsub hhom hnonneg C hC hbound hr

end Exploding

namespace Exploding

variable {d : ℕ}

/-- Subadditivity over a finite sum. -/
theorem lwc7_infN_sum_le {L : Site d → ℝ} (hnonneg : ∀ v, 0 ≤ L v)
    {ι : Type*} (s : Finset ι) (f : ι → Fin d → ℝ) :
    lwc6_infN L (∑ i ∈ s, f i) ≤ ∑ i ∈ s, lwc6_infN L (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine lwc6_infN_le hnonneg ⟨∅, fun _ => 0, by simp, ?_, ?_⟩
      · simp
      · simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (lwc6_infN_add hnonneg _ _) (add_le_add le_rfl ih)

/-- Decomposition of `y` into the positive and negative parts of its coordinates along the
unit vectors. -/
theorem lwc7_split (y : Fin d → ℝ) :
    y = (∑ i : Fin d, max (y i) 0 • lwc2_toReal (unit i))
      + (∑ i : Fin d, max (-(y i)) 0 • lwc2_toReal (-unit i)) := by
  funext j
  have h1 : (∑ i : Fin d, (max (y i) 0 • lwc2_toReal (unit i)) j) = max (y j) 0 := by
    rw [Finset.sum_eq_single j]
    · simp [lwc2_toReal, unit, Pi.smul_apply]
    · intro b _ hb; simp [lwc2_toReal, unit, Pi.smul_apply, Ne.symm hb]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have h2 : (∑ i : Fin d, (max (-(y i)) 0 • lwc2_toReal (-unit i)) j)
      = -(max (-(y j)) 0) := by
    rw [Finset.sum_eq_single j]
    · simp [lwc2_toReal, unit, Pi.neg_apply, Pi.smul_apply]
    · intro b _ hb
      simp [lwc2_toReal, unit, Pi.neg_apply, Pi.smul_apply, Ne.symm hb]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  simp only [Pi.add_apply, Finset.sum_apply, h1, h2]
  change y j = max (y j) 0 - max (-(y j)) 0
  rw [max_zero_sub_max_neg_zero_eq_self]

/-- The extension is linearly bounded on `ℝ^d`. -/
theorem lwc7_infN_bound {L : Site d → ℝ}
    (hsub : ∀ u v, L (u + v) ≤ L u + L v)
    (hhom : ∀ (k : ℕ) (v : Site d), L ((k : ℤ) • v) = (k : ℝ) * L v)
    (hnonneg : ∀ v, 0 ≤ L v)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, L v ≤ C * (mnorm v : ℝ)) (y : Fin d → ℝ) :
    lwc6_infN L y ≤ C * ∑ i, |y i| := by
  conv_lhs => rw [lwc7_split y]
  have h1 : lwc6_infN L (∑ i, max (y i) 0 • lwc2_toReal (unit i))
      ≤ ∑ i, max (y i) 0 * L (unit i) := by
    calc lwc6_infN L (∑ i, max (y i) 0 • lwc2_toReal (unit i))
        ≤ ∑ i, lwc6_infN L (max (y i) 0 • lwc2_toReal (unit i)) :=
          lwc7_infN_sum_le hnonneg Finset.univ _
      _ = ∑ i, max (y i) 0 * lwc6_infN L (lwc2_toReal (unit i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lwc6_infN_smul hnonneg _ (le_max_right _ _)]
      _ = ∑ i, max (y i) 0 * L (unit i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lwc7_infN_lattice_eq hsub hhom hnonneg C hC hbound (unit i)]
  have h2 : lwc6_infN L (∑ i, max (-(y i)) 0 • lwc2_toReal (-unit i))
      ≤ ∑ i, max (-(y i)) 0 * L (-unit i) := by
    calc lwc6_infN L (∑ i, max (-(y i)) 0 • lwc2_toReal (-unit i))
        ≤ ∑ i, lwc6_infN L (max (-(y i)) 0 • lwc2_toReal (-unit i)) :=
          lwc7_infN_sum_le hnonneg Finset.univ _
      _ = ∑ i, max (-(y i)) 0 * lwc6_infN L (lwc2_toReal (-unit i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lwc6_infN_smul hnonneg _ (le_max_right _ _)]
      _ = ∑ i, max (-(y i)) 0 * L (-unit i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lwc7_infN_lattice_eq hsub hhom hnonneg C hC hbound (-unit i)]
  have hmn : ∀ i : Fin d, mnorm (unit i) = 1 := by
    intro i
    simpa using pub_mnorm_smul_unit i 1
  have hmn' : ∀ i : Fin d, mnorm (-unit i) = 1 := by
    intro i
    rw [pub_mnorm_neg, hmn i]
  calc lwc6_infN L ((∑ i, max (y i) 0 • lwc2_toReal (unit i))
        + (∑ i, max (-(y i)) 0 • lwc2_toReal (-unit i)))
      ≤ lwc6_infN L (∑ i, max (y i) 0 • lwc2_toReal (unit i))
          + lwc6_infN L (∑ i, max (-(y i)) 0 • lwc2_toReal (-unit i)) :=
        lwc6_infN_add hnonneg _ _
    _ ≤ (∑ i, max (y i) 0 * L (unit i)) + (∑ i, max (-(y i)) 0 * L (-unit i)) :=
        add_le_add h1 h2
    _ ≤ (∑ i, max (y i) 0 * C) + (∑ i, max (-(y i)) 0 * C) := by
        refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => ?_)
        · exact mul_le_mul_of_nonneg_left (le_trans (hbound (unit i)) (by rw [hmn i, Int.cast_one, mul_one])) (le_max_right _ _)
        · exact mul_le_mul_of_nonneg_left (le_trans (hbound (-unit i)) (by rw [hmn' i, Int.cast_one, mul_one])) (le_max_right _ _)
    _ = C * ∑ i, |y i| := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← add_mul, max_zero_add_max_neg_zero_eq_abs_self, mul_comm]

end Exploding

namespace Exploding

variable {d : ℕ}

/-- The extension is Lipschitz for the `L¹` norm. -/
theorem lwc7_infN_abs_sub_le {L : Site d → ℝ}
    (hsub : ∀ u v, L (u + v) ≤ L u + L v)
    (hhom : ∀ (k : ℕ) (v : Site d), L ((k : ℤ) • v) = (k : ℝ) * L v)
    (hnonneg : ∀ v, 0 ≤ L v)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, L v ≤ C * (mnorm v : ℝ))
    (y y' : Fin d → ℝ) :
    |lwc6_infN L y - lwc6_infN L y'| ≤ C * ∑ i, |y i - y' i| := by
  have hu : lwc6_infN L y ≤ lwc6_infN L y' + lwc6_infN L (y - y') := by
    have := lwc6_infN_add hnonneg y' (y - y')
    rwa [show y' + (y - y') = y by abel] at this
  have hv : lwc6_infN L y' ≤ lwc6_infN L y + lwc6_infN L (y' - y) := by
    have := lwc6_infN_add hnonneg y (y' - y)
    rwa [show y + (y' - y) = y' by abel] at this
  have hb := lwc7_infN_bound hsub hhom hnonneg C hC hbound (y - y')
  have hb' := lwc7_infN_bound hsub hhom hnonneg C hC hbound (y' - y)
  have hsym : ∑ i, |y' i - y i| = ∑ i, |y i - y' i| := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_sub_comm]
  rw [abs_sub_le_iff]
  constructor
  · have hb'' : lwc6_infN L (y - y') ≤ C * ∑ i, |y i - y' i| := by
      simpa only [Pi.sub_apply] using hb
    linarith
  · have hb'' : lwc6_infN L (y' - y) ≤ C * ∑ i, |y i - y' i| := by
      rw [← hsym]
      simpa only [Pi.sub_apply] using hb'
    linarith

/-- The extension is continuous. -/
theorem lwc7_infN_continuous {L : Site d → ℝ}
    (hsub : ∀ u v, L (u + v) ≤ L u + L v)
    (hhom : ∀ (k : ℕ) (v : Site d), L ((k : ℤ) • v) = (k : ℝ) * L v)
    (hnonneg : ∀ v, 0 ≤ L v)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, L v ≤ C * (mnorm v : ℝ)) (hd : 0 < d) :
    Continuous (lwc6_infN L) := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε / (C * (d : ℝ) + 1), by positivity, fun y' hy' => ?_⟩
  rw [Real.dist_eq]
  have h := lwc7_infN_abs_sub_le hsub hhom hnonneg C hC hbound y y'
  have hrm : ∑ i, |y i - y' i| ≤ (d : ℝ) * ‖y - y'‖ := by
    calc ∑ i, |y i - y' i| ≤ ∑ _i : Fin d, ‖y - y'‖ :=
          Finset.sum_le_sum fun i _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm (y - y') i
      _ = (d : ℝ) * ‖y - y'‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdist : ‖y - y'‖ < ε / (C * (d : ℝ) + 1) := by
    rw [norm_sub_rev]
    simpa [dist_eq_norm] using hy'
  have hCd : 0 ≤ C * (d : ℝ) := by positivity
  have hfinal : (C * (d : ℝ)) * (ε / (C * (d : ℝ) + 1)) < ε := by
    rw [← mul_div_assoc]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < C * (d : ℝ) + 1)]
    nlinarith [hCd, hε]
  rw [abs_sub_comm]
  calc |lwc6_infN L y - lwc6_infN L y'| ≤ C * ∑ i, |y i - y' i| := h
    _ ≤ C * ((d : ℝ) * ‖y - y'‖) := by gcongr
    _ = (C * (d : ℝ)) * ‖y - y'‖ := by ring
    _ ≤ (C * (d : ℝ)) * (ε / (C * (d : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hdist.le hCd
    _ < ε := hfinal

/-- The extension assembled: `lwc6_infN L` is continuous, convex, one-homogeneous and
agrees with `L` on lattice points. -/
theorem lwc7_extend_exists {L : Site d → ℝ}
    (hsub : ∀ u v, L (u + v) ≤ L u + L v)
    (hhom : ∀ (k : ℕ) (v : Site d), L ((k : ℤ) • v) = (k : ℝ) * L v)
    (hnonneg : ∀ v, 0 ≤ L v)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, L v ≤ C * (mnorm v : ℝ)) (hd : 0 < d) :
    Continuous (lwc6_infN L) ∧ ConvexOn ℝ Set.univ (lwc6_infN L) ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, lwc6_infN L (c • y) = c * lwc6_infN L y) ∧
      (∀ v : Site d, lwc6_infN L (lwc2_toReal v) = L v) :=
  ⟨lwc7_infN_continuous hsub hhom hnonneg C hC hbound hd,
    lwc6_infN_convex hnonneg,
    fun c hc y => lwc6_infN_smul (c := c) hnonneg y hc,
    fun v => lwc7_infN_lattice_eq hsub hhom hnonneg C hC hbound v⟩

end Exploding
