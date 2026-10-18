import Exploding.Support.ArxivBondFiniteHoleTail
import Exploding.Support.SubPoly

/-!
# Uniform finite-hole cutoff in growing boxes

The actual-bond finite-hole tail, followed by a finite union over each centred box and the first
Borel--Cantelli lemma, bounds every finite hole meeting the box, uniformly over all cluster roots.
The result is an intermediate actual-bond estimate and does not assert existence of an infinite
cluster or the full conclusion of Proposition 2.2.
-/

open LatticeProb MeasureTheory Filter
open scoped BigOperators

namespace Exploding

/-- A box is bad when some actual bond-cluster root has a finite hole in the box that exceeds
the logarithmic cutoff. -/
private def arxivBondFiniteHoleBoxBad (d : ℕ) (B : ℝ) (n : ℕ) :
    Set (Site d × Fin d → Bool) :=
  {ζ | ∃ z ∈ cent d (4 * n), ∃ i : Site d,
    z ∉ {y : Site d | (openBondGraph ζ).Reachable i y} ∧
    (componentIn
      ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).Finite ∧
    B * (Real.log ((n : ℝ) + 2)) ^ (2 : ℕ) <
      ((componentIn
        ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).ncard : ℝ)}

/-- The selected floor threshold has exponential tail at most the reciprocal power needed to
sum over boxes. -/
private theorem arxiv_box_tail_exp_le_inv_pow (d n : ℕ) (c B : ℝ) (hc : 0 < c)
    (hB : B = (1 + ((d : ℝ) + 3) / c) ^ 2) :
    Real.exp (-c * Real.sqrt
      ((⌊B * (Real.log ((n : ℝ) + 2)) ^ 2⌋₊ + 1 : ℕ) : ℝ)) ≤
        ((n : ℝ) + 2)⁻¹ ^ (d + 3) := by
  let x : ℝ := (n : ℝ) + 2
  let t : ℝ := B * (Real.log x) ^ 2
  let s : ℕ := ⌊t⌋₊ + 1
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hx1 : 1 < x := by
    dsimp [x]
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hs : t < (s : ℝ) := by
    dsimp [s]
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  have hsquare :
      ((1 + ((d : ℝ) + 3) / c) * Real.log x) ^ 2 = t := by
    dsimp [t]
    rw [hB]
    ring
  have hsqrt :
      (1 + ((d : ℝ) + 3) / c) * Real.log x ≤ Real.sqrt (s : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hscale : (d : ℝ) + 3 ≤ c * (1 + ((d : ℝ) + 3) / c) := by
    have hmul : c * (1 + ((d : ℝ) + 3) / c) = c + ((d : ℝ) + 3) := by
      field_simp [hc.ne']
    rw [hmul]
    linarith
  have hdecay : ((d : ℝ) + 3) * Real.log x ≤ c * Real.sqrt (s : ℝ) := by
    calc
      ((d : ℝ) + 3) * Real.log x ≤
          (c * (1 + ((d : ℝ) + 3) / c)) * Real.log x :=
            mul_le_mul_of_nonneg_right hscale hlog.le
      _ = c * ((1 + ((d : ℝ) + 3) / c) * Real.log x) := by ring
      _ ≤ c * Real.sqrt (s : ℝ) := mul_le_mul_of_nonneg_left hsqrt hc.le
  have hexp : Real.exp (-((d : ℝ) + 3) * Real.log x) =
      x⁻¹ ^ (d + 3) := by
    have harg : -((d : ℝ) + 3) * Real.log x =
        ((d + 3 : ℕ) : ℝ) * (-Real.log x) := by
      push_cast
      ring
    rw [harg, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hx]
  calc
    Real.exp (-c * Real.sqrt (s : ℝ)) ≤
        Real.exp (-((d : ℝ) + 3) * Real.log x) :=
          Real.exp_le_exp.mpr (by linarith)
    _ = x⁻¹ ^ (d + 3) := hexp

/-- For every dimension at least two, a deterministic density window and logarithmic constant
give an almost-sure eventual cutoff for every finite hole meeting each centred box, uniformly
over every actual open-bond cluster root. -/
theorem arxiv_ae_bond_finite_holes_box_cutoff (d : ℕ) (hd : 2 ≤ d) :
    ∃ q0 B : ℝ, 0 ≤ q0 ∧ q0 < 1 ∧ 1 ≤ B ∧
      ∀ q : ℝ, q0 ≤ q → q ≤ 1 →
        ∀ᵐ ζ ∂(bondPercolation d q), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
          ∀ i z : Site d, z ∈ cent d (4 * n) →
            let I := {y : Site d | (openBondGraph ζ).Reachable i y}
            z ∉ I → (componentIn Iᶜ z).Finite →
              ((componentIn Iᶜ z).ncard : ℝ) ≤
                B * (Real.log ((n : ℝ) + 2)) ^ (2 : ℕ) := by
  classical
  obtain ⟨_, q0, C, c, _, hq0, hq01, hC, hc, htail⟩ :=
    arxiv_bond_finite_hole_tail_exp d hd
  let A : ℝ := 1 + ((d : ℝ) + 3) / c
  let B : ℝ := A ^ 2
  have hA1 : 1 ≤ A := by
    dsimp [A]
    apply le_add_of_nonneg_right
    positivity
  have hB : 1 ≤ B := by
    dsimp [B]
    nlinarith
  have hB_eq : B = (1 + ((d : ℝ) + 3) / c) ^ 2 := by
    rfl
  refine ⟨q0, B, hq0, hq01, hB, ?_⟩
  intro q hq hq1
  let M : ℝ := (8 : ℝ) ^ d * C
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hbaseSeries : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 3) := by
    exact Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshiftSeries : Summable (fun n : ℕ => ((n : ℝ) + 2)⁻¹ ^ 3) := by
    have hs := (summable_nat_add_iff
      (f := fun k : ℕ => 1 / (k : ℝ) ^ 3) 2).mpr hbaseSeries
    simpa [Nat.cast_add, one_div, inv_pow] using hs
  have hrealSeries : Summable (fun n : ℕ => M * ((n : ℝ) + 2)⁻¹ ^ 3) :=
    hshiftSeries.mul_left M
  have hupperFinite :
      (∑' n : ℕ, ENNReal.ofReal (M * ((n : ℝ) + 2)⁻¹ ^ 3)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hrealSeries]
    exact ENNReal.ofReal_ne_top
  have hprob : ∀ n : ℕ,
      bondPercolation d q (arxivBondFiniteHoleBoxBad d B n) ≤
        ENNReal.ofReal (M * ((n : ℝ) + 2)⁻¹ ^ 3) := by
    intro n
    obtain ⟨hboxFinite, hboxNcard⟩ := cent_finite_ncard d (4 * n)
    let F : Finset (Site d) := hboxFinite.toFinset
    have hFcoe : (F : Set (Site d)) = cent d (4 * n) :=
      hboxFinite.coe_toFinset
    have hFcard : F.card = (8 * n + 1) ^ d := by
      calc
        F.card = (cent d (4 * n)).ncard :=
          (Set.ncard_eq_toFinset_card (cent d (4 * n)) hboxFinite).symm
        _ = (2 * (4 * n) + 1) ^ d := hboxNcard
        _ = (8 * n + 1) ^ d := by congr 1; omega
    have hFcardReal : (F.card : ℝ) = ((8 * n + 1 : ℕ) : ℝ) ^ d := by
      exact_mod_cast hFcard
    let x : ℝ := (n : ℝ) + 2
    have hx : 0 < x := by
      dsimp [x]
      positivity
    have hbase : ((8 * n + 1 : ℕ) : ℝ) ≤ 8 * x := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      dsimp [x]
      push_cast
      nlinarith [hn]
    have hcardBound :
        (F.card : ℝ) ≤ (8 : ℝ) ^ d * x ^ d := by
      rw [hFcardReal]
      calc
        ((8 * n + 1 : ℕ) : ℝ) ^ d ≤ (8 * x) ^ d :=
          pow_le_pow_left₀ (by positivity) hbase d
        _ = (8 : ℝ) ^ d * x ^ d := by rw [mul_pow]
    let s : ℕ := ⌊B * (Real.log x) ^ 2⌋₊ + 1
    let E : Site d → Set (Site d × Fin d → Bool) := fun z =>
      {ζ | ∃ i : Site d,
        z ∉ {y : Site d | (openBondGraph ζ).Reachable i y} ∧
        (componentIn
          ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).Finite ∧
        s ≤ (componentIn
          ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).ncard}
    have hsub : arxivBondFiniteHoleBoxBad d B n ⊆ ⋃ z ∈ F, E z := by
      rintro ζ ⟨z, hz, i, hzi, hfinite, hlarge⟩
      have hzF : z ∈ F := by
        exact hboxFinite.mem_toFinset.mpr hz
      have hthreshold :
          s ≤ (componentIn
            ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).ncard := by
        apply Nat.succ_le_iff.mpr
        apply (Nat.floor_lt (by positivity)).2
        simpa [s, x] using hlarge
      exact Set.mem_iUnion.mpr ⟨z,
        Set.mem_iUnion.mpr ⟨hzF, ⟨i, hzi, hfinite, hthreshold⟩⟩⟩
    have htailAt (z : Site d) :
        bondPercolation d q (E z) ≤
          ENNReal.ofReal (C * Real.exp (-c * Real.sqrt (s : ℝ))) := by
      simpa [E] using htail z s hq hq1
    have hrealBound :
        (F.card : ℝ) * (C * Real.exp (-c * Real.sqrt (s : ℝ))) ≤
          M * x⁻¹ ^ 3 := by
      have hdecay := arxiv_box_tail_exp_le_inv_pow d n c B hc hB_eq
      have hdecay' : Real.exp (-c * Real.sqrt (s : ℝ)) ≤ x⁻¹ ^ (d + 3) := by
        simpa [s, x] using hdecay
      have hsite : C * Real.exp (-c * Real.sqrt (s : ℝ)) ≤
          C * x⁻¹ ^ (d + 3) :=
        mul_le_mul_of_nonneg_left hdecay' hC.le
      have hcardmul :
          (F.card : ℝ) * (C * Real.exp (-c * Real.sqrt (s : ℝ))) ≤
            ((8 : ℝ) ^ d * x ^ d) * (C * x⁻¹ ^ (d + 3)) := by
        exact mul_le_mul hcardBound hsite (by positivity) (by positivity)
      have hpow : x ^ d * x⁻¹ ^ (d + 3) = x⁻¹ ^ 3 := by
        rw [pow_add, inv_pow]
        calc
          x ^ d * ((x ^ d)⁻¹ * x⁻¹ ^ 3) =
              (x ^ d * (x ^ d)⁻¹) * x⁻¹ ^ 3 := by ac_rfl
          _ = x⁻¹ ^ 3 := by
            rw [mul_inv_cancel₀ (pow_ne_zero d hx.ne'), one_mul]
      calc
        (F.card : ℝ) * (C * Real.exp (-c * Real.sqrt (s : ℝ))) ≤
            ((8 : ℝ) ^ d * x ^ d) * (C * x⁻¹ ^ (d + 3)) := hcardmul
        _ = M * x⁻¹ ^ 3 := by
          dsimp [M]
          rw [show ((8 : ℝ) ^ d * x ^ d) * (C * x⁻¹ ^ (d + 3)) =
            (8 : ℝ) ^ d * C * (x ^ d * x⁻¹ ^ (d + 3)) by ring, hpow]
    calc
      bondPercolation d q (arxivBondFiniteHoleBoxBad d B n) ≤
          bondPercolation d q (⋃ z ∈ F, E z) := measure_mono hsub
      _ ≤ ∑ z ∈ F, bondPercolation d q (E z) := measure_biUnion_finset_le F _
      _ ≤ ∑ z ∈ F,
          ENNReal.ofReal (C * Real.exp (-c * Real.sqrt (s : ℝ))) := by
            apply Finset.sum_le_sum
            intro z _
            exact htailAt z
      _ = (F.card : ENNReal) *
          ENNReal.ofReal (C * Real.exp (-c * Real.sqrt (s : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal ((F.card : ℝ) *
          (C * Real.exp (-c * Real.sqrt (s : ℝ)))) := by
            rw [← ENNReal.ofReal_natCast]
            exact (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (M * x⁻¹ ^ 3) := ENNReal.ofReal_le_ofReal hrealBound
  have hsum :
      (∑' n : ℕ, bondPercolation d q (arxivBondFiniteHoleBoxBad d B n)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hupperFinite
    exact ENNReal.tsum_le_tsum hprob
  have hae := MeasureTheory.ae_eventually_notMem hsum
  filter_upwards [hae] with ζ hζ
  obtain ⟨n0, hn0⟩ := (eventually_atTop.mp hζ)
  refine ⟨n0, fun n hn i z hz hzi hfinite => ?_⟩
  by_contra hbound
  have hlarge : B * (Real.log ((n : ℝ) + 2)) ^ (2 : ℕ) <
      ((componentIn
        ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).ncard : ℝ) :=
    lt_of_not_ge hbound
  exact hn0 n hn ⟨z, hz, i, hzi, hfinite, hlarge⟩

end Exploding
