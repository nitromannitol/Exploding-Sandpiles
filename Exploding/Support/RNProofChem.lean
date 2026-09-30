/-
The chemical distance estimate behind Proposition 2.2: from the large deviation bound of Antal and
Pisztora, translation invariance of Bernoulli bond percolation, a union bound over pairs of sites
and the first Borel-Cantelli lemma, almost surely all far pairs in a common open cluster are joined
by an open path of length at most a fixed multiple of their distance.
-/
import Exploding.Support.RNProofGraph
import Exploding.External.AntalPisztora


open MeasureTheory ProbabilityTheory Exploding LatticeProb Filter Topology

namespace Exploding

variable {d : ℕ}

/-- Translation of a bond configuration by `x`. -/
def rn_shiftBond (x : Site d) (ω : RnBond d → Bool) : RnBond d → Bool :=
  fun b => ω (b.1 + x, b.2)

theorem rn_shiftBond_measurable (x : Site d) : Measurable (rn_shiftBond x) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem rn_shiftBond_map {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (x : Site d) :
    (bondPercolation d q).map (rn_shiftBond x) = bondPercolation d q := by
  haveI := rn_bitLaw_isProb h0 h1
  have hinj : Function.Injective (fun b : RnBond d => (b.1 + x, b.2)) := by
    intro b b' h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (add_right_cancel h.1) h.2
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : RnBond d => bitLaw q) hinj

theorem rn_openBond_shift_adj (x : Site d) (ω : RnBond d → Bool) (u v : Site d) :
    (openBondGraph (rn_shiftBond x ω)).Adj u v ↔ (openBondGraph ω).Adj (u + x) (v + x) := by
  simp only [openBondGraph, SimpleGraph.fromRel_adj, rn_shiftBond]
  have hne : u ≠ v ↔ u + x ≠ v + x := by
    constructor
    · intro h h'; exact h (add_right_cancel h')
    · intro h h'; exact h (by rw [h'])
  have hR : ∀ a b : Site d, (∃ i, b = a + unit i ∧ ω (a + x, i) = true) ↔
      (∃ i, b + x = a + x + unit i ∧ ω (a + x, i) = true) := by
    intro a b
    constructor
    · rintro ⟨i, h1, h2⟩
      exact ⟨i, by rw [h1]; abel, h2⟩
    · rintro ⟨i, h1, h2⟩
      exact ⟨i, by
        have h3 : b + x = (a + unit i) + x := by rw [h1]; abel
        exact add_right_cancel h3, h2⟩
  rw [hne, hR u v, hR v u]

theorem rn_edist_hom_le {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (f : G →g G')
    (u v : V) : G'.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.Reachable u v
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
    calc G'.edist (f u) (f v) ≤ ((p.map f).length : ℕ∞) := SimpleGraph.edist_le _
      _ = G.edist u v := by rw [SimpleGraph.Walk.length_map, hp]
  · rw [SimpleGraph.edist_eq_top_of_not_reachable h]; exact le_top

theorem rn_edist_shift (x : Site d) (ω : RnBond d → Bool) (u v : Site d) :
    (openBondGraph (rn_shiftBond x ω)).edist u v = (openBondGraph ω).edist (u + x) (v + x) := by
  apply le_antisymm
  · let ψ : openBondGraph ω →g openBondGraph (rn_shiftBond x ω) :=
      ⟨fun a => a + -x, fun {a b} h => by
        rw [rn_openBond_shift_adj]
        simpa using h⟩
    have := rn_edist_hom_le ψ (u + x) (v + x)
    have e1 : ψ (u + x) = u := by show u + x + -x = u; abel
    have e2 : ψ (v + x) = v := by show v + x + -x = v; abel
    rw [e1, e2] at this
    exact this
  · let φ : openBondGraph (rn_shiftBond x ω) →g openBondGraph ω :=
      ⟨fun a => a + x, fun {a b} h => (rn_openBond_shift_adj x ω a b).mp h⟩
    exact rn_edist_hom_le φ u v

theorem rn_chemEvent_shift_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (ρ : ℝ) (x z : Site d) :
    bondPercolation d q {ω | ∃ m : ℕ, (openBondGraph ω).edist x (x + z) = m ∧
        ρ * (mnorm z : ℝ) < m} ≤
      bondPercolation d q {ω | ∃ m : ℕ, (openBondGraph ω).edist 0 z = m ∧
        ρ * (mnorm z : ℝ) < m} := by
  haveI := rn_infinitePi_isProb (ι := RnBond d) h0 h1
  calc bondPercolation d q {ω | ∃ m : ℕ, (openBondGraph ω).edist x (x + z) = m ∧
        ρ * (mnorm z : ℝ) < m}
      ≤ bondPercolation d q (rn_shiftBond x ⁻¹' {ω | ∃ m : ℕ, (openBondGraph ω).edist 0 z = m ∧
        ρ * (mnorm z : ℝ) < m}) := by
        refine measure_mono (fun ω hω => ?_)
        obtain ⟨m, hm, hρm⟩ := hω
        refine ⟨m, ?_, hρm⟩
        rw [rn_edist_shift, zero_add, add_comm z x]
        exact hm
    _ ≤ ((bondPercolation d q).map (rn_shiftBond x)) {ω | ∃ m : ℕ, (openBondGraph ω).edist 0 z = m ∧
        ρ * (mnorm z : ℝ) < m} := Measure.le_map_apply (rn_shiftBond_measurable x).aemeasurable _
    _ = _ := by rw [rn_shiftBond_map h0 h1]

theorem rn_poly_exp_eventually (c : ℝ) (hc : 0 < c) (d : ℕ) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → ((2 * (r : ℝ) + 1) ^ d) * Real.exp (-(c * r)) ≤ Real.exp (-(c / 2 * r)) := by
  have hlim : Tendsto (fun x : ℝ => x ^ d * Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d
  have hlim2 : Tendsto (fun r : ℝ => (6 / c) ^ d * ((c / 2 * r) ^ d * Real.exp (-(c / 2 * r))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => c / 2 * r) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    simpa using (hlim.comp h1).const_mul ((6 / c) ^ d)
  have hev : ∀ᶠ r : ℝ in atTop, (6 / c) ^ d * ((c / 2 * r) ^ d * Real.exp (-(c / 2 * r))) < 1 :=
    hlim2.eventually (gt_mem_nhds one_pos)
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp hev
  refine ⟨max (⌈R0⌉₊) 1, fun r hr => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (le_trans (le_max_right _ _) hr)
  have hrR : R0 ≤ (r : ℝ) := by
    have := (le_trans (le_max_left _ _) hr)
    exact le_trans (Nat.le_ceil R0) (by exact_mod_cast this)
  have h := hR0 r hrR
  have h2 : (2 * (r : ℝ) + 1) ^ d ≤ (3 * r) ^ d := by
    apply pow_le_pow_left₀ (by positivity); linarith
  have h3 : (3 * (r : ℝ)) ^ d = (6 / c) ^ d * (c / 2 * r) ^ d := by
    rw [← mul_pow]; congr 1; field_simp; ring
  have h4 : Real.exp (-(c * r)) = Real.exp (-(c / 2 * r)) * Real.exp (-(c / 2 * r)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (2 * (r : ℝ) + 1) ^ d * Real.exp (-(c * r))
      ≤ (3 * r) ^ d * Real.exp (-(c * r)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = ((6 / c) ^ d * ((c / 2 * r) ^ d * Real.exp (-(c / 2 * r)))) * Real.exp (-(c / 2 * r)) := by
        rw [h3, h4]; ring
    _ ≤ 1 * Real.exp (-(c / 2 * r)) :=
        mul_le_mul_of_nonneg_right h.le (Real.exp_nonneg _)
    _ = _ := one_mul _

theorem rn_tail_summable (c : ℝ) (hc : 0 < c) (d : ℕ) :
    Summable (fun n : ℕ => (2 * (n : ℝ) + 1) ^ d * Real.exp (-(c / 2 * (Real.log n) ^ 2))) := by
  have hs : Summable (fun n : ℕ => (3 : ℝ) ^ d * (1 / (n : ℝ) ^ 3)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hs ?_
  rw [eventually_atTop]
  refine ⟨max 1 ⌈Real.exp (2 * ((d : ℝ) + 3) / c)⌉₊, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_left _ _) hn)
  have hnpos : (0 : ℝ) < n := by linarith
  have hnE : Real.exp (2 * ((d : ℝ) + 3) / c) ≤ n := by
    have := le_trans (le_max_right _ _) hn
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  have hlog : 2 * ((d : ℝ) + 3) / c ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]; exact hnE
  have hlog' : ((d : ℝ) + 3) ≤ c / 2 * Real.log n := by
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ c / 2)
    calc ((d : ℝ) + 3) = c / 2 * (2 * ((d : ℝ) + 3) / c) := by field_simp
      _ ≤ _ := this
  have hlogpos : 0 ≤ Real.log n := Real.log_nonneg hn1
  have h1 : Real.exp (-(c / 2 * (Real.log n) ^ 2)) ≤ ((n : ℝ) ^ (d + 3))⁻¹ := by
    have h2 : -(c / 2 * (Real.log n) ^ 2) ≤ -(((d + 3 : ℕ) : ℝ) * Real.log n) := by
      push_cast
      nlinarith
    calc Real.exp (-(c / 2 * (Real.log n) ^ 2)) ≤ Real.exp (-(((d + 3 : ℕ) : ℝ) * Real.log n)) :=
          Real.exp_le_exp.mpr h2
      _ = ((n : ℝ) ^ (d + 3))⁻¹ := by
          rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnpos]
  have h2 : (2 * (n : ℝ) + 1) ^ d ≤ (3 * n) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (2 * (n : ℝ) + 1) ^ d * Real.exp (-(c / 2 * (Real.log n) ^ 2))
      ≤ (3 * n) ^ d * ((n : ℝ) ^ (d + 3))⁻¹ := mul_le_mul h2 h1 (Real.exp_nonneg _) (by positivity)
    _ = (3 : ℝ) ^ d * (1 / (n : ℝ) ^ 3) := by
        rw [mul_pow, pow_add]; field_simp


theorem rn_geom_tail (a : ENNReal) (k : ℕ) :
    ∑' r : ℕ, (if k ≤ r then a ^ r else 0) = a ^ k * (1 - a)⁻¹ := by
  have h := (ENNReal.summable (f := fun r : ℕ => (if k ≤ r + k then a ^ (r + k) else 0))).sum_add_tsum_nat_add' (f := fun r : ℕ => if k ≤ r then a ^ r else 0) (k := k)
  have h0 : ∑ i ∈ Finset.range k, (if k ≤ i then a ^ i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have : ¬ k ≤ i := by simpa using hi
    simp [this]
  rw [h0, zero_add] at h
  rw [← h]
  calc ∑' i : ℕ, (if k ≤ i + k then a ^ (i + k) else 0) = ∑' i : ℕ, a ^ k * a ^ i := by
        congr 1; ext i; simp [pow_add, mul_comm]
    _ = a ^ k * ∑' i : ℕ, a ^ i := ENNReal.tsum_mul_left
    _ = a ^ k * (1 - a)⁻¹ := by rw [ENNReal.tsum_geometric]


/-- The cube `[-n, n]^d` as a finset. -/
noncomputable def rn_box (d n : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) n

theorem rn_card_box (d n : ℕ) : (rn_box d n).card = (2 * n + 1) ^ d := by
  simp only [rn_box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  omega

theorem rn_abs_le_mnorm (z : Site d) (i : Fin d) : |z i| ≤ mnorm z :=
  Finset.single_le_sum (f := fun j => |z j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem rn_mem_box {n : ℕ} {z : Site d} (h : mnorm z ≤ (n : ℤ)) : z ∈ rn_box d n := by
  simp only [rn_box, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have := rn_abs_le_mnorm z i
  constructor <;> linarith [abs_le.mp (this.trans h)]

/-- The sphere `{z : |z| = r}` of the Manhattan norm, as a finset. -/
noncomputable def rn_shell (d r : ℕ) : Finset (Site d) := (rn_box d r).filter fun z => mnorm z = (r : ℤ)

theorem rn_card_shell_le (d r : ℕ) : (rn_shell d r).card ≤ (2 * r + 1) ^ d :=
  (Finset.card_filter_le _ _).trans (rn_card_box d r).le

theorem rn_mem_shell {r : ℕ} {z : Site d} (h : mnorm z = (r : ℤ)) : z ∈ rn_shell d r := by
  simp only [rn_shell, Finset.mem_filter]
  exact ⟨rn_mem_box h.le, h⟩

theorem rn_mnorm_sub_comm (x y : Site d) : mnorm (x - y) = mnorm (y - x) := by
  simp only [mnorm]
  exact Finset.sum_congr rfl fun i _ => by simp [abs_sub_comm]

/-- The bad event at scale `n`: two far sites within distance `n` of the origin in one cluster at
chemical distance exceeding `ρ` times their distance. -/
def rn_badEvent (d : ℕ) (ρ : ℝ) (n : ℕ) : Set (RnBond d → Bool) :=
  {ω | ∃ x z : Site d, mnorm x ≤ (n : ℤ) ∧ Real.log n ^ (2 : ℕ) ≤ (mnorm z : ℝ) ∧
    ∃ m : ℕ, (openBondGraph ω).edist x (x + z) = m ∧ ρ * (mnorm z : ℝ) < m}

/-- The chemical distance clause of Proposition 2.2 for a bond configuration. -/
def RnChemProp (d : ℕ) (C : ℝ) (ζ : RnBond d → Bool) : Prop :=
  ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x y : Site d, mnorm x ≤ (n : ℤ) →
    Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) → (openBondGraph ζ).Reachable x y →
      ∃ m : ℕ, (openBondGraph ζ).edist x y = (m : ℕ∞) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ)

theorem rn_badEvent_measure_le {q ρ c : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {R : ℕ}
    (hR : ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q {ω | ∃ m : ℕ, (openBondGraph ω).edist 0 y = m ∧
        ρ * (mnorm y : ℝ) < m} ≤ ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ)))))
    (n : ℕ) (hn : (R : ℝ) ≤ Real.log n ^ (2 : ℕ)) :
    bondPercolation d q (rn_badEvent d ρ n) ≤ (((2 * n + 1) ^ d : ℕ) : ENNReal) *
      ∑' r : ℕ, (if Real.log n ^ (2 : ℕ) ≤ (r : ℝ) then
        ENNReal.ofReal ((2 * (r : ℝ) + 1) ^ d * Real.exp (-(c * r))) else 0) := by
  set L : ℝ := Real.log n ^ (2 : ℕ) with hL
  set E : Site d → Site d → Set (RnBond d → Bool) := fun x z =>
    {ω | ∃ m : ℕ, (openBondGraph ω).edist x (x + z) = m ∧ ρ * (mnorm z : ℝ) < m} with hE
  set G : Site d → ℕ → Set (RnBond d → Bool) := fun x r =>
    {ω | L ≤ (r : ℝ) ∧ ∃ z ∈ rn_shell d r, ω ∈ E x z} with hG
  have hsub : rn_badEvent d ρ n ⊆ ⋃ x ∈ rn_box d n, ⋃ r : ℕ, G x r := by
    intro ω hω
    obtain ⟨x, z, hx, hz, hm⟩ := hω
    simp only [Set.mem_iUnion]
    refine ⟨x, rn_mem_box hx, (mnorm z).toNat, ?_⟩
    have hz0 : 0 ≤ mnorm z := by
      have : (0 : ℝ) ≤ (mnorm z : ℝ) := (by positivity : (0 : ℝ) ≤ L).trans hz
      exact_mod_cast this
    have hzr : mnorm z = (((mnorm z).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hz0).symm
    refine ⟨?_, z, rn_mem_shell hzr, hm⟩
    have h2 : (((mnorm z).toNat : ℕ) : ℝ) = (mnorm z : ℝ) := by
      have := Int.toNat_of_nonneg hz0
      exact_mod_cast this
    rw [h2]; exact hz
  have hG : ∀ x r, bondPercolation d q (G x r) ≤ (if L ≤ (r : ℝ) then
      ENNReal.ofReal ((2 * (r : ℝ) + 1) ^ d * Real.exp (-(c * r))) else 0) := by
    intro x r
    by_cases hr : L ≤ (r : ℝ)
    · rw [if_pos hr]
      have hRr : (R : ℤ) ≤ (r : ℤ) := by
        have : (R : ℝ) ≤ (r : ℝ) := hn.trans hr
        exact_mod_cast this
      have hsubG : G x r ⊆ ⋃ z ∈ rn_shell d r, E x z := by
        rintro ω ⟨_, z, hz, hωz⟩
        simp only [Set.mem_iUnion]
        exact ⟨z, hz, hωz⟩
      have hz : ∀ z ∈ rn_shell d r, bondPercolation d q (E x z) ≤
          ENNReal.ofReal (Real.exp (-(c * r))) := by
        intro z hz
        have hzr : mnorm z = (r : ℤ) := (Finset.mem_filter.mp hz).2
        refine (rn_chemEvent_shift_le hq0 hq1 ρ x z).trans ((hR z (by rw [hzr]; exact hRr)).trans ?_)
        have h3 : (mnorm z : ℝ) = (r : ℝ) := by rw [hzr]; simp
        rw [h3]
      calc bondPercolation d q (G x r) ≤ bondPercolation d q (⋃ z ∈ rn_shell d r, E x z) :=
            measure_mono hsubG
        _ ≤ ∑ z ∈ rn_shell d r, bondPercolation d q (E x z) := measure_biUnion_finset_le _ _
        _ ≤ ∑ z ∈ rn_shell d r, ENNReal.ofReal (Real.exp (-(c * r))) :=
            Finset.sum_le_sum hz
        _ = ((rn_shell d r).card : ENNReal) * ENNReal.ofReal (Real.exp (-(c * r))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (((2 * r + 1) ^ d : ℕ) : ENNReal) * ENNReal.ofReal (Real.exp (-(c * r))) := by
            gcongr; exact rn_card_shell_le d r
        _ = ENNReal.ofReal ((2 * (r : ℝ) + 1) ^ d * Real.exp (-(c * r))) := by
            rw [ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [← ENNReal.ofReal_natCast]
            push_cast
            rfl
    · rw [if_neg hr]
      have : G x r = ∅ := by
        ext ω; simp only [hG, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hr h.1
      rw [this]; simp
  calc bondPercolation d q (rn_badEvent d ρ n)
      ≤ bondPercolation d q (⋃ x ∈ rn_box d n, ⋃ r : ℕ, G x r) := measure_mono hsub
    _ ≤ ∑ x ∈ rn_box d n, bondPercolation d q (⋃ r : ℕ, G x r) := measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ rn_box d n, ∑' r : ℕ, bondPercolation d q (G x r) :=
        Finset.sum_le_sum fun x _ => measure_iUnion_le _
    _ ≤ ∑ x ∈ rn_box d n, ∑' r : ℕ, (if L ≤ (r : ℝ) then
        ENNReal.ofReal ((2 * (r : ℝ) + 1) ^ d * Real.exp (-(c * r))) else 0) :=
        Finset.sum_le_sum fun x _ => ENNReal.tsum_le_tsum fun r => hG x r
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, rn_card_box]

theorem rn_chem_ae (hChem : Exploding.External.AntalPisztoraChemicalDistance) (d : ℕ)
    (hd : 2 ≤ d) {q : ℝ} (hq : bondCritical d < q) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᵐ ζ ∂(bondPercolation d q), RnChemProp d C ζ := by
  obtain ⟨ρ, c, hρ, hc, R, hR⟩ := hChem d hd q hq hq1
  refine ⟨ρ, hρ, ?_⟩
  haveI := rn_infinitePi_isProb (ι := RnBond d) hq0 hq1
  obtain ⟨N₀, hN₀⟩ := rn_poly_exp_eventually c hc d
  have hev : ∀ᶠ n : ℕ in atTop, ((max R N₀ : ℕ) : ℝ) ≤ Real.log n ^ (2 : ℕ) := by
    have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ (2 : ℕ)) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp h1
    exact h2.eventually_ge_atTop _
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set a : ENNReal := ENNReal.ofReal (Real.exp (-(c / 2))) with ha
  have ha1 : a < 1 := by
    rw [ha, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (Real.exp_lt_one_iff.mpr (by linarith))
  set K : ENNReal := (1 - a)⁻¹ with hK
  have hKtop : K ≠ ⊤ := ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr ha1).ne'
  have hbound : ∀ n : ℕ, N ≤ n → bondPercolation d q (rn_badEvent d ρ n) ≤
      ENNReal.ofReal ((2 * (n : ℝ) + 1) ^ d * Real.exp (-(c / 2 * Real.log n ^ (2 : ℕ)))) * K := by
    intro n hn
    have hLR : (R : ℝ) ≤ Real.log n ^ (2 : ℕ) :=
      le_trans (by exact_mod_cast le_max_left R N₀) (hN n hn)
    have hLN : (N₀ : ℝ) ≤ Real.log n ^ (2 : ℕ) :=
      le_trans (by exact_mod_cast le_max_right R N₀) (hN n hn)
    refine (rn_badEvent_measure_le hq0 hq1 hR n hLR).trans ?_
    set L : ℝ := Real.log n ^ (2 : ℕ) with hL
    have hL0 : 0 ≤ L := by positivity
    have htail : ∑' r : ℕ, (if L ≤ (r : ℝ) then
        ENNReal.ofReal ((2 * (r : ℝ) + 1) ^ d * Real.exp (-(c * r))) else 0) ≤
        a ^ ⌈L⌉₊ * K := by
      rw [hK, ← rn_geom_tail a ⌈L⌉₊]
      refine ENNReal.tsum_le_tsum fun r => ?_
      by_cases hr : L ≤ (r : ℝ)
      · have hr' : ⌈L⌉₊ ≤ r := Nat.ceil_le.mpr hr
        have hN₀r : N₀ ≤ r := by
          have : (N₀ : ℝ) ≤ r := hLN.trans hr
          exact_mod_cast this
        rw [if_pos hr, if_pos hr', ha, ← ENNReal.ofReal_pow (Real.exp_nonneg _),
          ← Real.exp_nat_mul]
        refine ENNReal.ofReal_le_ofReal ((hN₀ r hN₀r).trans (le_of_eq ?_))
        congr 1; ring
      · simp [hr]
    have hak : a ^ ⌈L⌉₊ ≤ ENNReal.ofReal (Real.exp (-(c / 2 * L))) := by
      rw [ha, ← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have := Nat.le_ceil L
      nlinarith
    calc (((2 * n + 1) ^ d : ℕ) : ENNReal) * ∑' r : ℕ, (if L ≤ (r : ℝ) then
          ENNReal.ofReal ((2 * (r : ℝ) + 1) ^ d * Real.exp (-(c * r))) else 0)
        ≤ (((2 * n + 1) ^ d : ℕ) : ENNReal) * (a ^ ⌈L⌉₊ * K) := by gcongr
      _ ≤ (((2 * n + 1) ^ d : ℕ) : ENNReal) * (ENNReal.ofReal (Real.exp (-(c / 2 * L))) * K) := by
          gcongr
      _ = ENNReal.ofReal ((2 * (n : ℝ) + 1) ^ d * Real.exp (-(c / 2 * L))) * K := by
          rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]
          congr 2
          rw [← ENNReal.ofReal_natCast]
          push_cast
          rfl
  have hsum : ∑' n : ℕ, bondPercolation d q (rn_badEvent d ρ (n + N)) ≠ ⊤ := by
    have hg := (summable_nat_add_iff N).mpr (rn_tail_summable c hc d)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => hbound (n + N) (by omega))
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hg]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop
  have hae := ae_eventually_notMem hsum
  refine hae.mono fun ζ hζ => ?_
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp hζ
  refine ⟨n1 + N, fun n hn x y hx hy hreach => ?_⟩
  have hnb : ζ ∉ rn_badEvent d ρ n := by
    have := hn1 (n - N) (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (SimpleGraph.edist_ne_top_iff_reachable.mpr hreach)
  refine ⟨m, hm.symm, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hnb
  refine ⟨x, y - x, hx, ?_, m, ?_, ?_⟩
  · rw [rn_mnorm_sub_comm]; exact hy
  · rw [add_sub_cancel]; exact hm.symm
  · rw [rn_mnorm_sub_comm]; exact hcon

end Exploding
