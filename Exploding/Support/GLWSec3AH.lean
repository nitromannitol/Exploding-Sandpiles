/-
Proposition 5.1 of the paper (generalized last wave): the probabilistic claim `glws_Renorm`,
the generalization of Proposition 2.2 to a finite-range dependent field of strongly box-crossing
tiles.
-/
import Exploding.Support.GLWSec3AG

open MeasureTheory ProbabilityTheory Exploding LatticeProb Filter

namespace Exploding

variable {d : ℕ}

/-- The probability of an intersection of two events of probability above `1 - δ` is above
`1 - 2δ`. -/
theorem glws_inter_lb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (hA' : ENNReal.ofReal (1 - δ) < P A) (hB' : ENNReal.ofReal (1 - δ) < P B) :
    ENNReal.ofReal (1 - 2 * δ) ≤ P (A ∩ B) := by
  have h0 : (0 : ℝ) ≤ 1 - δ := by linarith
  have a1 : 1 - δ < P.real A := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal h0 (measure_ne_top P A)).mp hA'
    exact this
  have b1 : 1 - δ < P.real B := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal h0 (measure_ne_top P B)).mp hB'
    exact this
  have hc : P.real (A ∩ B)ᶜ ≤ P.real Aᶜ + P.real Bᶜ := by
    rw [Set.compl_inter]
    exact measureReal_union_le _ _
  have hAc : P.real Aᶜ = 1 - P.real A := probReal_compl_eq_one_sub hA
  have hBc : P.real Bᶜ = 1 - P.real B := probReal_compl_eq_one_sub hB
  have hABc : P.real (A ∩ B)ᶜ = 1 - P.real (A ∩ B) := probReal_compl_eq_one_sub (hA.inter hB)
  have hfin : 1 - 2 * δ ≤ P.real (A ∩ B) := by linarith
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P _)]
  exact hfin

/-- **The probabilistic claim** (the generalization of Proposition 2.2 under Hypotheses 1 and 4):
the field of strongly box-crossing tiles carries, on an event of probability one, an infinite
connected cluster of tiles with polylogarithmic holes and linear chemical distance.  The
good-edge field has dependence graph `glws_bondGraph d K` of bounded degree, so the Liggett,
Schonmann and Stacey domination makes it dominate Bernoulli bond percolation of high density, whose
cluster carries Mathieu's hole bound and the Antal and Pisztora chemical-distance bound. -/
theorem glws_renorm (d : ℕ) (P : Measure (Site d → ℤ)) : glws_Renorm d P := by
  intro hd hP h1 h4 hLSS hLSSB hHole hChem
  haveI := hP
  obtain ⟨K, hK⟩ := h1
  have hPE : ∃ qP : ℝ, 0 ≤ qP ∧ qP < 1 ∧ ∀ q : ℝ, qP ≤ q → q ≤ 1 → bondTheta d q ≠ 0 :=
    ⟨255 / 256, by norm_num, by norm_num, fun _ hq0 hq1 => pe_theta_ne_zero hd hq0 hq1⟩
  obtain ⟨ρ₁, hρ0, hρ1, C, hC1, hcore⟩ := glws_core_dom hLSSB hHole hChem d hd hPE
  obtain ⟨p, hp0, hp1, hp⟩ := rn_lssb_apply hLSSB (glws_bondGraph d K) _
    (glws_bondGraph_degree K) ρ₁ hρ0 hρ1
  obtain ⟨k, hk, hSBC⟩ := h4 ((1 - p) / 2) (by linarith)
  refine ⟨k, hk, 1, C, one_pos, by linarith, ?_⟩
  obtain ⟨hFm, hdep⟩ := glws_edge_dependence P K hK k hk
  set F : (Site d → ℤ) → RnBond d → Bool := fun η e => glws_Phi k e η with hF
  haveI : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hFm.aemeasurable
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

end Exploding
