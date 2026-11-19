import Exploding.Support.LimitShapeUnconditional

/-!
# Generalized good-cube estimates

Strongly box-crossing tiles carry an infinite cluster with controlled holes
and chemical distance, yielding the local arrival-time estimates.
-/

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory
open scoped Classical Topology

namespace Exploding

/-- Strongly box-crossing tiles have a suitable infinite cluster. -/
theorem glws_renorm_unconditional (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (h1 : FiniteRangeOfDependence d P) (h4 : StronglyBoxCrossingHyp d P) :
    ∃ k : Fin d → ℕ, (∀ i, 0 < k i) ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᵐ η ∂P, glws_Clu d k c C η := by
  have hLSSB := Exploding.lssBoundedDegree
  have hHole := Exploding.xmf_proved
  have := hP
  obtain ⟨K, hK⟩ := h1
  have hPE : ∃ qP : ℝ, 0 ≤ qP ∧ qP < 1 ∧ ∀ q : ℝ, qP ≤ q → q ≤ 1 → bondTheta d q ≠ 0 :=
    ⟨255 / 256, by norm_num, by norm_num, fun _ hq0 hq1 => pe_theta_ne_zero hd hq0 hq1⟩
  obtain ⟨ρ₁, hρ0, hρ1, C, hC1, hcore⟩ := glws_core_dom_of_high_density_chem_ae hLSSB hHole d
    (rn_chem_ae_of_high_density xap12_high_density_bound d hd) hd hPE
  obtain ⟨p, hp0, hp1, hp⟩ := rn_lssb_apply hLSSB (glws_bondGraph d K) _
    (glws_bondGraph_degree K) ρ₁ hρ0 hρ1
  obtain ⟨k, hk, hSBC⟩ := h4 ((1 - p) / 2) (by linarith)
  refine ⟨k, hk, 1, C, one_pos, by linarith, ?_⟩
  obtain ⟨hFm, hdep⟩ := glws_edge_dependence P K hK k hk
  set F : (Site d → ℤ) → RnBond d → Bool := fun η e => glws_Phi k e η with hF
  have : IsProbabilityMeasure (P.map F) := inferInstance
  have hmarg : ∀ e : RnBond d, ENNReal.ofReal p ≤ (P.map F) {ω' | ω' e = true} := by
    intro e
    have hm : MeasurableSet {ω' : RnBond d → Bool | ω' e = true} :=
      measurableSet_eq_fun (measurable_pi_apply e) measurable_const
    rw [Measure.map_apply hFm hm]
    have hA : MeasurableSet {η : Site d → ℤ | glws_X k e.1 η = true} :=
      (glws_X_meas k e.1) (measurableSet_singleton true)
    have hB : MeasurableSet {η : Site d → ℤ | glws_X k (e.1 + unit e.2) η = true} :=
      (glws_X_meas k _) (measurableSet_singleton true)
    have hset : F ⁻¹' {ω' | ω' e = true} =
        {η : Site d → ℤ | glws_X k e.1 η = true} ∩
          {η : Site d → ℤ | glws_X k (e.1 + unit e.2) η = true} := by
      ext η; simp [hF, glws_Phi]
    rw [hset]
    have hA' : ENNReal.ofReal (1 - (1 - p) / 2) < P {η : Site d → ℤ | glws_X k e.1 η = true} := by
      have : {η : Site d → ℤ | glws_X k e.1 η = true} = {η | StronglyBoxCrossed η k e.1} := by
        ext η; simp [glws_X]
      rw [this]; exact hSBC _
    have hB' : ENNReal.ofReal (1 - (1 - p) / 2) <
        P {η : Site d → ℤ | glws_X k (e.1 + unit e.2) η = true} := by
      have : {η : Site d → ℤ | glws_X k (e.1 + unit e.2) η = true} =
          {η | StronglyBoxCrossed η k (e.1 + unit e.2)} := by
        ext η; simp [glws_X]
      rw [this]; exact hSBC _
    have := glws_inter_lb P hA hB (δ := (1 - p) / 2) (by linarith) hA' hB'
    have e : 1 - 2 * ((1 - p) / 2) = p := by ring
    rwa [e] at this
  have hdom : ∀ A : Set (RnBond d → Bool), MeasurableSet A → IsIncreasingSet A →
      bernoulliProduct (RnBond d) ρ₁ A ≤
        P {ω | (fun e : RnBond d => glws_X k e.1 ω && glws_X k (e.1 + unit e.2) ω) ∈ A} := by
    intro A hA hinc
    have := hp (P.map F) inferInstance hdep hmarg A hA hinc
    rwa [Measure.map_apply hFm hA] at this
  have hae := hcore P (glws_X k) (glws_X_meas k) hdom
  refine hae.mono fun η hη => ?_
  obtain ⟨S, hSinf, hSgood, hSconn, hShole, hSchem⟩ := hη
  refine ⟨S, hSinf, fun x hx => ?_, hSconn, hShole, hSchem⟩
  have := hSgood x hx
  simpa [glws_X] using this

/-- The generalized cluster gives the local arrival-time bound. -/
theorem glws_origin_unconditional (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η) (h1 : FiniteRangeOfDependence d P)
    (h3 : PathFillingHyp d P) (h4 : StronglyBoxCrossingHyp d P) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂P, glws_Loc0 d γ C η := by
  obtain ⟨k, hk, c, C, hc, hC, hclu⟩ := glws_renorm_unconditional d hd P hP h1 h4
  obtain ⟨γp, hγp, hpf⟩ := h3
  obtain ⟨γ, C', hγ, hC', hloc⟩ := glws_loc0_of_cl hd k γp C hγp
  refine ⟨γ, C', hγ, hC', ?_⟩
  filter_upwards [hclu, hpf, hsupp] with η hη1 hη2 hη3
  have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hη3 x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hη3 x).2
  obtain ⟨Cinf, S⟩ := glws_Cl_of_Clu hd k hk c C hC γp hγp η hlow hhigh hη2 hη1
  exact hloc η Cinf S

/-- The generalized last and penultimate arrival times have polylogarithmic separation. -/
theorem s3k_close_unconditional (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η) (h1 : FiniteRangeOfDependence d P)
    (h3 : PathFillingHyp d P) (h4 : StronglyBoxCrossingHyp d P) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᵐ η ∂P, ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
      lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
        ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
          clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ := by
  obtain ⟨k, hk, c, C, hc, hC, hclu⟩ := glws_renorm_unconditional d hd P hP h1 h4
  obtain ⟨γp, hγp, hpf⟩ := h3
  have hd1 : 1 ≤ d := by omega
  refine ⟨s3k_Etop d γp + 1, by linarith [(s3k_E_ge d hd1 γp hγp).2.2.2], ?_⟩
  filter_upwards [hclu, hpf, hsupp] with η hη1 hη2 hη3
  have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hη3 x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hη3 x).2
  obtain ⟨Cinf, hinf, hgood, hconn, ⟨n0h, hhole⟩, ⟨n0c, hchem⟩⟩ := hη1
  let D : S3kData d η k Cinf γp C :=
    { hd := hd
      hlow := hlow
      hhigh := hhigh
      hk := hk
      hinf := hinf
      hgood := hgood
      hconn := hconn
      n0h := n0h
      hole := hhole
      hCch := hC.le
      n0c := n0c
      hchem := fun n hn x hx y hy hxn hlog => by
        obtain ⟨m, hm, _, hmC⟩ := hchem n hn x hx y hy hxn hlog
        exact ⟨m, hm, hmC⟩
      hγp := hγp
      hpf := hη2 }
  obtain ⟨n0, hn0⟩ := s3k_close_of_data D
  exact ⟨n0, fun n hn x hx => hn0 n hn x hx⟩

end Exploding
