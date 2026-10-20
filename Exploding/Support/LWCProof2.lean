/-
Continuation of `Exploding/Support/LWCProof.lean`.

Two pieces of the last-wave convergence that need no new ergodic theory:

  (A) the far bound of `eq:lastwave_lipschitz` (stated in the frozen file, not here);
  (B) the pure real-analysis upgrade from convergence along lattice directions plus a
      Lipschitz bound to locally uniform convergence on compacts.

This file proves the half of (B) that is elementary: `lwc2_rational_convergence` upgrades
integer lattice directions to rational directions, using the Lipschitz bound and the fact that
`nearestSite (n • (v/q))` stays within `O(1)` of `(n/q) • v`.  Together with the box-membership
bounds it supplies the ingredients of the finite-subcover upgrade, whose last step remains part
of the single open conjunction in `Exploding/Frozen/LastWaveConvergence.lean`.  All
declarations are `lwc2_`-prefixed.
-/
import Exploding.Support.LWCProof

open Exploding LatticeProb MeasureTheory Filter

variable {d : ℕ}

/-- The real vector underlying a lattice site. -/
def lwc2_toReal (v : Site d) : Fin d → ℝ := fun i => (v i : ℝ)

@[simp] theorem lwc2_toReal_apply (v : Site d) (i : Fin d) :
    lwc2_toReal v i = (v i : ℝ) := rfl

theorem lwc2_toReal_smul (n : ℕ) (v : Site d) :
    (n : ℝ) • lwc2_toReal v = lwc2_toReal ((n : ℤ) • v) := by
  funext i
  simp [lwc2_toReal]

theorem lwc2_mnorm_nonneg (v : Site d) : 0 ≤ mnorm v := by
  simpa [mnorm] using Finset.sum_nonneg (fun i _ => abs_nonneg (v i))

theorem lwc2_abs_coord_le_mnorm (v : Site d) (i : Fin d) : |v i| ≤ mnorm v :=
  Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)

/-- `mnorm` of an integer multiple of a site. -/
theorem lwc2_mnorm_nat_smul (m : ℕ) (v : Site d) :
    mnorm ((m : ℤ) • v) = (m : ℤ) * mnorm v := by
  simp only [mnorm, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (Int.natCast_nonneg m),
    Finset.mul_sum]

/-- The real vector `(1/q) • v` for a lattice site `v`: its `i`-th coordinate is `v i / q`. -/
theorem lwc2_toReal_div_apply (v : Site d) (q : ℕ) (i : Fin d) :
    ((q : ℝ)⁻¹ • lwc2_toReal v) i = (v i : ℝ) * (q : ℝ)⁻¹ := by
  simp [lwc2_toReal, Pi.smul_apply, mul_comm]

theorem lwc2_nearestSite_sub_le (y : Fin d → ℝ) (i : Fin d) :
    |(nearestSite y i : ℝ) - y i| ≤ 1 := by
  simp only [nearestSite]
  rw [abs_sub_le_iff]
  constructor
  · have h := Int.ceil_lt_add_one (y i - 1 / 2)
    linarith
  · have h := Int.le_ceil (y i - 1 / 2)
    linarith

/-- Integer part of the denominator divided by the denominator converges to `1/q`. -/
theorem lwc2_div_div_tendsto (q : ℕ) (hq : 1 ≤ q) :
    Tendsto (fun n : ℕ => ((n / q : ℕ) : ℝ) / (n : ℝ)) atTop (nhds ((q : ℝ)⁻¹)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |((n / q : ℕ) : ℝ) / (n : ℝ) - (q : ℝ)⁻¹| ≤ (q : ℝ) / (n : ℝ) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : ((n / q : ℕ) : ℝ) / (n : ℝ) ≤ (q : ℝ)⁻¹ := by
      rw [div_le_iff₀ hnpos, inv_mul_eq_div, le_div_iff₀ hqpos]
      have h := Nat.mul_div_le n q
      have : (q : ℝ) * ((n / q : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      linarith
    have hge : (q : ℝ)⁻¹ - (q : ℝ) / (n : ℝ) ≤ ((n / q : ℕ) : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]
      have hsimp : ((q : ℝ)⁻¹ - (q : ℝ) / (n : ℝ)) * (n : ℝ) = (n : ℝ) / (q : ℝ) - (q : ℝ) := by
        field_simp
      rw [hsimp]
      have hlt : n < (n / q + 1) * q := by
        rw [← Nat.div_lt_iff_lt_mul (show 0 < q by omega)]
        omega
      have hcast : (n : ℝ) < (((n / q + 1 : ℕ)) : ℝ) * (q : ℝ) := by exact_mod_cast hlt
      have h1'' : (n : ℝ) / (q : ℝ) - 1 < ((n / q : ℕ) : ℝ) := by
        have heq : (n : ℝ) / (q : ℝ) - 1 = ((n : ℝ) - (q : ℝ)) / (q : ℝ) := by
          field_simp
        rw [heq, div_lt_iff₀ hqpos]
        push_cast at hcast ⊢
        linarith
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    rw [abs_le]
    constructor <;> linarith
  have hqlim : Tendsto (fun n : ℕ => (q : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have habs : Tendsto (fun n : ℕ =>
      |((n / q : ℕ) : ℝ) / (n : ℝ) - (q : ℝ)⁻¹|) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
      ((eventually_ge_atTop 1).mono fun n hn => hbound n hn) hqlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

/-- The lattice point `(n/q) • v` lies in the box `cent d ((mnorm v).toNat + 1) * n`. -/
theorem lwc2_div_smul_mem_cent (v : Site d) (q n : ℕ) (hn : 1 ≤ n) :
    ((n / q : ℕ) : ℤ) • v ∈ cent d (((mnorm v).toNat + 1) * n) := by
  intro i
  have hAnonneg : 0 ≤ mnorm v := lwc2_mnorm_nonneg v
  have hAtoNat : (((mnorm v).toNat : ℤ)) = mnorm v := Int.toNat_of_nonneg hAnonneg
  have hvi : |v i| ≤ mnorm v := lwc2_abs_coord_le_mnorm v i
  have h1 : |((n / q : ℕ) : ℤ) * v i| ≤ (n : ℤ) * mnorm v := by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    have hdiv : ((n / q : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.div_le_self n q
    nlinarith [abs_nonneg (v i)]
  have h2 : (n : ℤ) * mnorm v ≤ ((((mnorm v).toNat + 1) * n : ℕ) : ℤ) := by
    push_cast
    rw [hAtoNat]
    have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  calc |((((n / q : ℕ) : ℤ) • v) i)| = |((n / q : ℕ) : ℤ) * v i| := rfl
    _ ≤ (n : ℤ) * mnorm v := h1
    _ ≤ _ := h2


/-- The nearest lattice point to `n • (v/q)` lies in the box `cent d ((mnorm v).toNat + 1) * n`. -/
theorem lwc2_nearest_mem_cent (v : Site d) (q n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) ∈
      cent d (((mnorm v).toNat + 1) * n) := by
  intro i
  have hAnonneg : 0 ≤ mnorm v := lwc2_mnorm_nonneg v
  have hAtoNat : (((mnorm v).toNat : ℤ)) = mnorm v := Int.toNat_of_nonneg hAnonneg
  have hAtoNatR : (((mnorm v).toNat : ℝ)) = (mnorm v : ℝ) := by exact_mod_cast hAtoNat
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hnpos : (0 : ℝ) ≤ n := by positivity
  have hvi : |v i| ≤ mnorm v := lwc2_abs_coord_le_mnorm v i
  have hcoord : (((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i) =
      (n : ℝ) * (q : ℝ)⁻¹ * (v i : ℝ) := by
    simp [lwc2_toReal, Pi.smul_apply, mul_assoc]
  have hy : |(((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i)| ≤ (n : ℝ) * |v i| := by
    rw [hcoord]
    have hqinv_nonneg : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
    simp only [abs_mul, abs_of_nonneg hnpos, abs_of_nonneg hqinv_nonneg, Int.cast_abs]
    have hqinv : (q : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hqpos]; exact_mod_cast hq
    have hvi' : (0 : ℝ) ≤ |(v i : ℝ)| := abs_nonneg _
    calc (n : ℝ) * (q : ℝ)⁻¹ * |(v i : ℝ)|
        = (q : ℝ)⁻¹ * ((n : ℝ) * |(v i : ℝ)|) := by ring
      _ ≤ 1 * ((n : ℝ) * |(v i : ℝ)|) := mul_le_mul_of_nonneg_right hqinv (mul_nonneg hnpos hvi')
      _ = (n : ℝ) * |(v i : ℝ)| := by ring
  have hnear := lwc2_nearestSite_sub_le ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i
  have hz : |(nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i : ℝ)| ≤
      (n : ℝ) * (mnorm v : ℝ) + 1 := by
    calc |(nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i : ℝ)|
        = |((nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i : ℝ) -
              (((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i)) +
            (((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i)| := by ring_nf
      _ ≤ |(nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i : ℝ) -
              (((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i)| +
            |(((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i)| := abs_add_le _ _
      _ ≤ 1 + (n : ℝ) * |v i| := add_le_add hnear hy
      _ ≤ (n : ℝ) * (mnorm v : ℝ) + 1 := by
          have hviR : |v i| ≤ (mnorm v : ℝ) := by exact_mod_cast hvi
          nlinarith
  have hbound : (n : ℝ) * (mnorm v : ℝ) + 1 ≤ ((((mnorm v).toNat + 1) * n : ℕ) : ℝ) := by
    rw [← hAtoNatR]
    push_cast
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hzR : ((|nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i| : ℤ) : ℝ) ≤
      ((((mnorm v).toNat + 1) * n : ℕ) : ℝ) := by
    rw [Int.cast_abs]
    exact le_trans hz hbound
  exact_mod_cast hzR


/-- The lattice distance between `nearestSite (n • (v/q))` and `(n/q) • v` is bounded by the
constant `mnorm v + 1` per coordinate. -/
theorem lwc2_abs_coord_sub_le (v : Site d) (q n : ℕ) (hq : 1 ≤ q) (i : Fin d) :
    |(nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) - ((n / q : ℕ) : ℤ) • v) i| ≤
      mnorm v + 1 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hmle : ((n / q : ℕ) : ℝ) ≤ (n : ℝ) * (q : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hqpos]
    exact_mod_cast Nat.div_mul_le_self n q
  have hmlt : (n : ℝ) * (q : ℝ)⁻¹ < ((n / q : ℕ) : ℝ) + 1 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hqpos]
    have hlt : n < (n / q + 1) * q := by
      rw [← Nat.div_lt_iff_lt_mul (show 0 < q by omega)]
      omega
    have hcast : (n : ℝ) < (((n / q + 1 : ℕ)) : ℝ) * (q : ℝ) := by exact_mod_cast hlt
    push_cast at hcast ⊢
    linarith
  have hdiff : |(n : ℝ) * (q : ℝ)⁻¹ - ((n / q : ℕ) : ℝ)| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hvi : |v i| ≤ mnorm v := lwc2_abs_coord_le_mnorm v i
  have hviR : |(v i : ℝ)| ≤ (mnorm v : ℝ) := by exact_mod_cast hvi
  have hnearest := lwc2_nearestSite_sub_le ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i
  have hyi : (((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i) =
      (n : ℝ) * (q : ℝ)⁻¹ * (v i : ℝ) := by
    simp [lwc2_toReal, Pi.smul_apply, mul_assoc]
  have hx2i : (((((n / q : ℕ) : ℤ) • v) i) : ℝ) = ((n / q : ℕ) : ℝ) * (v i : ℝ) := by
    simp only [Pi.smul_apply, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  have hmid : |(((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i : ℝ) -
      ((((n / q : ℕ) : ℤ) • v) i : ℝ)| ≤ (mnorm v : ℝ) := by
    rw [hyi, hx2i]
    have hfac : (n : ℝ) * (q : ℝ)⁻¹ * (v i : ℝ) - ((n / q : ℕ) : ℝ) * (v i : ℝ) =
        ((n : ℝ) * (q : ℝ)⁻¹ - ((n / q : ℕ) : ℝ)) * (v i : ℝ) := (sub_mul _ _ _).symm
    rw [hfac]
    calc |((n : ℝ) * (q : ℝ)⁻¹ - ((n / q : ℕ) : ℝ)) * (v i : ℝ)|
        = |(n : ℝ) * (q : ℝ)⁻¹ - ((n / q : ℕ) : ℝ)| * |(v i : ℝ)| := abs_mul _ _
      _ ≤ 1 * |(v i : ℝ)| := mul_le_mul_of_nonneg_right hdiff (abs_nonneg _)
      _ = |(v i : ℝ)| := one_mul _
      _ ≤ (mnorm v : ℝ) := hviR
  have hreal : (|(nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) -
      ((n / q : ℕ) : ℤ) • v) i| : ℝ) ≤ (mnorm v : ℝ) + 1 := by
    simp only [Pi.sub_apply, Int.cast_sub]
    calc |(nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i : ℝ) -
          ((((n / q : ℕ) : ℤ) • v) i : ℝ)|
        ≤ |(nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i : ℝ) -
              (((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i : ℝ)| +
            |(((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) i : ℝ) -
              ((((n / q : ℕ) : ℤ) • v) i : ℝ)| := abs_sub_le _ _ _
      _ ≤ 1 + (mnorm v : ℝ) := add_le_add hnearest hmid
      _ = (mnorm v : ℝ) + 1 := by ring
  exact_mod_cast hreal

/-- The lattice distance from `nearestSite (n • (v/q))` to `(n/q) • v` is `O(1)`: at most
`d * (mnorm v + 1)`, the sum of the coordinate bounds `lwc2_abs_coord_sub_le`. -/
theorem lwc2_mnorm_sub_le (v : Site d) (q n : ℕ) (hq : 1 ≤ q) :
    (mnorm (nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) - ((n / q : ℕ) : ℤ) • v) : ℝ)
      ≤ (d : ℝ) * ((mnorm v : ℝ) + 1) := by
  have hsum : (mnorm (nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) -
      ((n / q : ℕ) : ℤ) • v) : ℝ) =
      ∑ i : Fin d, ((|(nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) -
        ((n / q : ℕ) : ℤ) • v) i| : ℤ) : ℝ) := by
    simp only [mnorm, Int.cast_sum]
  rw [hsum]
  calc ∑ i : Fin d, ((|(nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v)) -
          ((n / q : ℕ) : ℤ) • v) i| : ℤ) : ℝ)
      ≤ ∑ _i : Fin d, ((mnorm v : ℝ) + 1) :=
        Finset.sum_le_sum (fun i _ => by
          have h := lwc2_abs_coord_sub_le v q n hq i
          exact_mod_cast h)
    _ = (d : ℝ) * ((mnorm v : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `n ↦ n / q` tends to infinity for `q ≥ 1`. -/
theorem lwc2_div_atTop (q : ℕ) (hq : 1 ≤ q) :
    Tendsto (fun n : ℕ => n / q) atTop atTop := by
  refine Filter.tendsto_atTop_atTop_of_monotone (fun a b hab => Nat.div_le_div_right hab)
    (fun b => ⟨b * q, ?_⟩)
  rw [Nat.mul_div_cancel b (by omega : 0 < q)]

/-- **Rational directions.**  If `f` has a limit along every integer lattice direction with
limit shape `N`, `N` is homogeneous and `f` satisfies the Lipschitz bound, then the rescaled `f`
converges along every rational direction `v/q` to `N (v/q)`. -/
theorem lwc2_rational_convergence (f : Site d → ℝ) (N : (Fin d → ℝ) → ℝ)
    (hNhom : ∀ (c : ℝ), 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y)
    (hlat : ∀ v : Site d, Tendsto (fun n : ℕ => f ((n : ℤ) • v) / (n : ℝ)) atTop
        (nhds (N (lwc2_toReal v))))
    (C γ : ℝ) (hC : 0 < C) (_hγ : 0 < γ)
    (hlip : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x x' : Site d,
        x ∈ cent d n → x' ∈ cent d n →
        |f x - f x'| ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ)
    (v : Site d) (q : ℕ) (hq : 1 ≤ q) :
    Tendsto (fun n : ℕ => f (nearestSite ((n : ℝ) • ((q : ℝ)⁻¹ • lwc2_toReal v))) / (n : ℝ))
      atTop (nhds (N ((q : ℝ)⁻¹ • lwc2_toReal v))) := by
  obtain ⟨n0, hn0⟩ := hlip
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  set M : ℕ := (mnorm v).toNat + 1 with hM
  have hMpos : 0 < M := by omega
  set V : Fin d → ℝ := lwc2_toReal v with hV
  set r : Fin d → ℝ := (q : ℝ)⁻¹ • V with hr
  have hr_eq : r = (q : ℝ)⁻¹ • lwc2_toReal v := by rw [hr, hV]
  have hgap : Tendsto (fun n : ℕ =>
      f (nearestSite ((n : ℝ) • r)) / (n : ℝ) - f (((n / q : ℕ) : ℤ) • v) / (n : ℝ))
      atTop (nhds 0) := by
    have hb : ∀ n : ℕ, max n0 1 ≤ n →
        |f (nearestSite ((n : ℝ) • r)) / (n : ℝ) - f (((n / q : ℕ) : ℤ) • v) / (n : ℝ)|
          ≤ (C * ((d : ℝ) * ((mnorm v : ℝ) + 1)) + Real.log ((M : ℝ) * (n : ℝ)) ^ γ) / (n : ℝ) := by
      intro n hn
      have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hMn : n0 ≤ M * n := by
        have h1 : n0 ≤ n := le_trans (le_max_left _ _) hn
        exact le_trans h1 (Nat.le_mul_of_pos_left n hMpos)
      have hx1 : nearestSite ((n : ℝ) • r) ∈ cent d (M * n) := by
        rw [hr_eq]; exact lwc2_nearest_mem_cent v q n hq hn1
      have hx2 : ((n / q : ℕ) : ℤ) • v ∈ cent d (M * n) :=
        lwc2_div_smul_mem_cent v q n hn1
      have hbnd := hn0 (M * n) hMn (nearestSite ((n : ℝ) • r)) (((n / q : ℕ) : ℤ) • v) hx1 hx2
      rw [Nat.cast_mul] at hbnd
      have hm : (mnorm (nearestSite ((n : ℝ) • r) - ((n / q : ℕ) : ℤ) • v) : ℝ)
          ≤ (d : ℝ) * ((mnorm v : ℝ) + 1) := by
        rw [hr_eq]; exact lwc2_mnorm_sub_le v q n hq
      rw [div_sub_div_same, abs_div, abs_of_pos hnpos]
      apply div_le_div_of_nonneg_right _ hnpos.le
      have hCm : C * (mnorm (nearestSite ((n : ℝ) • r) - ((n / q : ℕ) : ℤ) • v) : ℝ)
          ≤ C * ((d : ℝ) * ((mnorm v : ℝ) + 1)) := mul_le_mul_of_nonneg_left hm hC.le
      linarith [hbnd, hCm]
    have hlim : Tendsto (fun n : ℕ =>
        (C * ((d : ℝ) * ((mnorm v : ℝ) + 1)) + Real.log ((M : ℝ) * (n : ℝ)) ^ γ) / (n : ℝ))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (C * ((d : ℝ) * ((mnorm v : ℝ) + 1))) / (n : ℝ))
          atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun n : ℕ => Real.log (M * n) ^ γ / (n : ℝ)) atTop (nhds 0) :=
        lwc_transfer_4 γ M hMpos
      simpa only [add_div, add_zero] using h1.add h2
    have habs : Tendsto (fun n : ℕ =>
        |f (nearestSite ((n : ℝ) • r)) / (n : ℝ) - f (((n / q : ℕ) : ℤ) • v) / (n : ℝ)|)
        atTop (nhds 0) :=
      squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
        (Eventually.mono (eventually_ge_atTop (max n0 1)) hb) hlim
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [Real.norm_eq_abs, sub_zero] using habs
  have hx2lim : Tendsto (fun n : ℕ => f (((n / q : ℕ) : ℤ) • v) / (n : ℝ)) atTop
      (nhds (N ((q : ℝ)⁻¹ • lwc2_toReal v))) := by
    have h1 : Tendsto (fun n : ℕ => f (((n / q : ℕ) : ℤ) • v) / ((n / q : ℕ) : ℝ)) atTop
        (nhds (N (lwc2_toReal v))) :=
      (hlat v).comp (lwc2_div_atTop q hq)
    have h2 : Tendsto (fun n : ℕ => ((n / q : ℕ) : ℝ) / (n : ℝ)) atTop (nhds ((q : ℝ)⁻¹)) :=
      lwc2_div_div_tendsto q hq
    have h3 := h1.mul h2
    have h4 : N (lwc2_toReal v) * (q : ℝ)⁻¹ = N ((q : ℝ)⁻¹ • lwc2_toReal v) := by
      rw [hNhom ((q : ℝ)⁻¹) (inv_nonneg.mpr hqpos.le) (lwc2_toReal v), mul_comm]
    rw [h4] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop q] with n hn
    have hm1 : 1 ≤ n / q := (Nat.one_le_div_iff (by omega : 0 < q)).mpr hn
    have hmpos : (0 : ℝ) < ((n / q : ℕ) : ℝ) := by exact_mod_cast hm1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (le_trans hq hn)
    field_simp
  have hsum := hgap.add hx2lim
  have hA : Tendsto (fun n : ℕ => f (nearestSite ((n : ℝ) • r)) / (n : ℝ)) atTop (nhds (N r)) := by
    have h := hsum
    rw [zero_add] at h
    refine h.congr' ?_
    filter_upwards with n
    ring
  simpa [hr_eq] using hA

