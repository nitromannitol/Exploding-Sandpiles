/-
Proposition 2.2 from the percolation facts: the good cubes of a background of the toy law form an
independent field of density close to one, to which the percolation content of Proposition 2.2
applies.
-/
import Exploding.Support.ReductionShift
import Exploding.Support.RNProofCore

open MeasureTheory ProbabilityTheory Exploding LatticeProb

namespace Exploding

variable {d : ℕ}

theorem rn_goodAt_measurable (k : ℕ) (i : Site d) :
    MeasurableSet {η : Site d → ℤ | GoodAt η k i} := by
  have hf : Measurable (fun ω : Site d → ℤ => (blockO k i).restrict ω) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  exact (measurable_iff_comap_le.mp hf) _ (goodAt_measurableSet_blockO k i)

theorem rn_chipLaw_prob (a b : ℤ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (chipLaw a b p) := by
  refine ⟨?_⟩
  unfold chipLaw
  simp only [Measure.add_apply, Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  norm_num

theorem rn_toyLaw_prob (d : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (toyLaw d p) := by
  haveI := rn_chipLaw_prob (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) hp0 hp1
  unfold toyLaw productLaw
  infer_instance

theorem rn_toyLaw_shift {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) (i : Site d) :
    (toyLaw d p).map (fun η x => η (x + (k : ℤ) • i)) = toyLaw d p := by
  haveI := rn_chipLaw_prob (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) hp0 hp1
  have hinj : Function.Injective (fun x : Site d => x + (k : ℤ) • i) := fun x y h => by
    simpa using congrArg (fun z => z - (k : ℤ) • i) h
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) hinj

theorem rn_goodAt_marginal {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) (i : Site d) :
    toyLaw d p {η : Site d → ℤ | GoodAt η k i} = toyLaw d p {η : Site d → ℤ | GoodCube η k} := by
  have hmeas : MeasurableSet {η : Site d → ℤ | GoodCube η k} := by
    have := rn_goodAt_measurable k (0 : Site d)
    simpa [GoodAt] using this
  have hmf : Measurable (fun η : Site d → ℤ => fun x => η (x + (k : ℤ) • i)) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply _
  have hpre : (fun η : Site d → ℤ => fun x => η (x + (k : ℤ) • i)) ⁻¹' {η | GoodCube η k}
      = {η : Site d → ℤ | GoodAt η k i} := rfl
  rw [← hpre, ← Measure.map_apply hmf hmeas, rn_toyLaw_shift hp0 hp1 k i]

/-- The probability of a good cube is at least `1 - δ` at every scale `k ≥ 1` with
`d k^d exp(-2 ε² k) < δ`, where `ε = p/2`: the proof of Proposition 2.1 at an arbitrary such `k`. -/
theorem rn_goodCube_prob (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ)
    (hkbound : (d : ℝ) * (k : ℝ) ^ d * Real.exp (-2 * (p / 2) ^ 2 * (k : ℝ)) < δ) :
    ENNReal.ofReal (1 - δ) ≤ toyLaw d p {η | GoodCube η k} := by
  haveI hIPM' : IsProbabilityMeasure (toyLaw d p) := rn_toyLaw_prob d hp.le hp1.le
  set ε : ℝ := p / 2 with hεdef
  have hε0 : 0 < ε := by positivity
  have hεp : ε < p := by rw [hεdef]; linarith
  set Bad : Set (Site d → ℤ) := {η | ¬ ∀ (i : Fin d) (y : Site d), y ∈ cube d k →
    ∃ x ∈ line d k i y, η x = 2 * (d : ℤ) - 1} with hBaddef
  set Unbdd : Set (Site d → ℤ) :=
    {η | ¬ ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1} with hUdef
  have hfin := aux_ct_assemble_cube_finite d k
  have hcardeq : (hfin.toFinset.card : ℝ) = (k : ℝ) ^ d := by
    rw [← Set.ncard_eq_toFinset_card (cube d k) hfin, aux_ct_assemble_cube_ncard]
    push_cast; ring
  have hbad := aux_ct_all_directions d k hd p hp hp1 ε hε0 hεp hfin
  rw [hcardeq] at hbad
  have hbadlt : toyLaw d p Bad < ENNReal.ofReal δ :=
    lt_of_le_of_lt hbad (ENNReal.ofReal_lt_ofReal_iff hδ |>.mpr hkbound)
  have hUzero : toyLaw d p Unbdd = 0 := by
    have hae := aux_ct_ae_bounded d hd p hp hp1
    rwa [MeasureTheory.ae_iff] at hae
  have hsub : {η : Site d → ℤ | GoodCube η k}ᶜ ⊆ Bad ∪ Unbdd := by
    intro η hη
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    apply hη
    simp only [hBaddef, hUdef, Set.mem_setOf_eq, not_not] at hcon
    exact aux_ct_propagate d k hd η hcon.2 hcon.1
  have hcompl_le : toyLaw d p {η : Site d → ℤ | GoodCube η k}ᶜ ≤ ENNReal.ofReal δ := by
    calc toyLaw d p {η : Site d → ℤ | GoodCube η k}ᶜ
        ≤ toyLaw d p (Bad ∪ Unbdd) := measure_mono hsub
      _ ≤ toyLaw d p Bad + toyLaw d p Unbdd := measure_union_le _ _
      _ ≤ ENNReal.ofReal δ := by rw [hUzero, add_zero]; exact hbadlt.le
  have htot : (1 : ENNReal) ≤ toyLaw d p {η : Site d → ℤ | GoodCube η k}
      + toyLaw d p {η : Site d → ℤ | GoodCube η k}ᶜ := by
    have hu := measure_union_le (μ := toyLaw d p)
      {η : Site d → ℤ | GoodCube η k} {η : Site d → ℤ | GoodCube η k}ᶜ
    rw [Set.union_compl_self, measure_univ] at hu
    exact hu
  rcases le_total δ 1 with hδ1 | hδ1
  · have h1 : ENNReal.ofReal (1 - δ) + ENNReal.ofReal δ = 1 := by
      rw [← ENNReal.ofReal_add (by linarith) hδ.le]
      norm_num
    have hstep : (1 : ENNReal) ≤ toyLaw d p {η : Site d → ℤ | GoodCube η k} + ENNReal.ofReal δ := by
      calc (1 : ENNReal) ≤ toyLaw d p {η : Site d → ℤ | GoodCube η k}
            + toyLaw d p {η : Site d → ℤ | GoodCube η k}ᶜ := htot
        _ ≤ toyLaw d p {η : Site d → ℤ | GoodCube η k} + ENNReal.ofReal δ := by gcongr
    rw [← h1] at hstep
    exact (ENNReal.add_le_add_iff_right (a := ENNReal.ofReal δ)
      (by simp [ENNReal.ofReal_ne_top])).mp hstep
  · have hnonpos : (1 - δ) ≤ 0 := by linarith
    rw [ENNReal.ofReal_of_nonpos hnonpos]
    exact zero_le

/-- **The tail of Proposition 2.1.**  For every `δ > 0` the probability of a good cube is at least
`1 - δ` at every sufficiently large scale. -/
theorem rn_goodCube_tail (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k0 : ℕ, 1 ≤ k0 ∧ ∀ k : ℕ, k0 ≤ k → ENNReal.ofReal (1 - δ) ≤ toyLaw d p {η | GoodCube η k} := by
  have hε0 : 0 < p / 2 := by positivity
  obtain ⟨N, hN⟩ := aux_ct_decay_eventually d (p / 2) δ hε0 hδ
  refine ⟨max N 1, le_max_right _ _, fun k hk => ?_⟩
  have hkN : N ≤ k := le_trans (le_max_left _ _) hk
  refine rn_goodCube_prob d hd p hp hp1 δ hδ k ?_
  have hb := hN k hkN
  have hrn : (Real.exp (-2 * (p / 2) ^ 2)) ^ k = Real.exp (-2 * (p / 2) ^ 2 * (k : ℝ)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hrn] at hb
  have hdpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  calc (d : ℝ) * (k : ℝ) ^ d * Real.exp (-2 * (p / 2) ^ 2 * (k : ℝ))
      ≤ ((d : ℝ) + 1) * ((k : ℝ) ^ d * Real.exp (-2 * (p / 2) ^ 2 * (k : ℝ))) := by
        nlinarith [Real.exp_pos (-2 * (p / 2) ^ 2 * (k : ℝ)),
          pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ)) d]
    _ < ((d : ℝ) + 1) * (δ / ((d : ℝ) + 1)) := mul_lt_mul_of_pos_left hb hdpos
    _ = δ := by field_simp

open scoped Classical in
theorem rn_iIndep_good (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (k : ℕ) (hk : 1 ≤ k) :
    iIndepFun (fun (x : Site d) (η : Site d → ℤ) => decide (GoodAt η k x)) (toyLaw d p) := by
  classical
  have h := (renorm_iid_field_indep (d := d) p hp hp1 k hk).iIndepFun_indicator (β := ℕ) (m := inferInstance)
  have h2 := h.comp (fun _ (n : ℕ) => decide (n = 1)) (fun _ => measurable_of_countable _)
  refine h2.congr (fun x => Filter.Eventually.of_forall (fun η => ?_))
  simp only [Function.comp, Set.indicator]
  by_cases hη : η ∈ {η : Site d → ℤ | GoodAt η k x} <;> simp_all

open scoped Classical in
/-- **Proposition 2.2**, with the positivity of the percolation probability of bond percolation at
high density as a hypothesis. -/
theorem rn_renormalization (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hPE : ∃ qP : ℝ, 0 ≤ qP ∧ qP < 1 ∧ ∀ q : ℝ, qP ≤ q → q ≤ 1 → bondTheta d q ≠ 0) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p),
        ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k Cinf ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)),
            x ∉ Cinf →
              (componentIn Cinfᶜ x).Finite ∧
                ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
            mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
              ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ)) := by
  obtain ⟨q, hq1, C, hC1, hcore⟩ := rn_core hLSSB hHole hChem d hd hPE
  set q' : ℝ := max q 0 with hq'
  have hq'1 : q' < 1 := max_lt hq1 zero_lt_one
  obtain ⟨k0, hk01, hk0⟩ := rn_goodCube_tail d hd p hp hp1 (1 - q') (by linarith)
  refine ⟨k0, fun k hk => ⟨1, C, one_pos, by linarith, ?_⟩⟩
  have hk1 : 1 ≤ k := le_trans hk01 hk
  haveI := rn_toyLaw_prob d hp.le hp1.le
  have hgood : ∀ x : Site d, ENNReal.ofReal q ≤
      toyLaw d p {η | (fun (x : Site d) (η : Site d → ℤ) => decide (GoodAt η k x)) x η = true} := by
    intro x
    have h1 : {η : Site d → ℤ | (fun (x : Site d) (η : Site d → ℤ) => decide (GoodAt η k x)) x η = true}
        = {η : Site d → ℤ | GoodAt η k x} := by ext η; simp
    rw [h1, rn_goodAt_marginal hp.le hp1.le k x]
    have := hk0 k hk
    rw [show 1 - (1 - q') = q' by ring] at this
    exact le_trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)) this
  have hae := hcore (toyLaw d p) (fun (x : Site d) (η : Site d → ℤ) => decide (GoodAt η k x))
    (fun x => measurable_to_bool (by
      have : (fun η : Site d → ℤ => decide (GoodAt η k x)) ⁻¹' {true} = {η | GoodAt η k x} := by
        ext η; simp
      rw [this]; exact rn_goodAt_measurable k x))
    (rn_iIndep_good p hp hp1 k hk1) hgood
  refine hae.mono fun η hη => ?_
  obtain ⟨S, hSinf, hSgood, hSconn, hShole, n0, hn0⟩ := hη
  refine ⟨S, ⟨hSinf, fun x hx => ?_, hSconn⟩, hShole, n0, hn0⟩
  have := hSgood x hx
  simpa [goodSites, Set.mem_setOf_eq] using this

end Exploding
