/-
Proposition 5.1 (generalized last wave), the infinite cluster of strongly box-crossing tiles, part B:
the probabilistic claim `glws_Renorm` (the generalization of Proposition 2.2), proved from the
cited percolation results.

The tile field `X_j = 1{B_k^{(j)} is strongly box-crossing}` is `(K + 1)`-dependent, uniformly in the
side lengths `k` (`s3k_kdep`), and its one-site probabilities are at least `1 - δ` for some `k`
(Hypothesis 5.4).  Choose `ρ` close to one so that Bernoulli site percolation of density `ρ` has the
cluster of Proposition 2.2 (`rn_core`); the Liggett-Schonmann-Stacey domination (Theorem 0.0) makes
`X` dominate Bernoulli site percolation of density `ρ` once `δ` is small enough, and the Strassen
coupling puts a configuration of the cluster below `X` almost surely.
-/
import Exploding.Support.S3CloseA
import Exploding.Support.RNProofGood
import Exploding.Support.RNProofPeierls
import Exploding.Support.RNProofStrassen
import Exploding.Support.RNProofCore

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- **The probabilistic claim** (the generalization of Proposition 2.2). -/
theorem s3k_renorm (d : ℕ) (P : Measure (Site d → ℤ)) : glws_Renorm d P := by
  intro hd hP h1 h4 hLSS hLSSB hHole hChem
  have hPE : ∃ qP : ℝ, 0 ≤ qP ∧ qP < 1 ∧ ∀ q : ℝ, qP ≤ q → q ≤ 1 → bondTheta d q ≠ 0 :=
    ⟨255 / 256, by norm_num, by norm_num, fun _ hq0 hq1 => pe_theta_ne_zero hd hq0 hq1⟩
  obtain ⟨q, hq1, C, hC1, hcore⟩ := rn_core hLSSB hHole hChem d hd hPE
  set ρ : ℝ := max q 0 with hρ
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  have hρ1 : ρ < 1 := max_lt hq1 zero_lt_one
  obtain ⟨K, hK⟩ := s3k_kdep d P h1
  obtain ⟨pL, hpL1, hdom⟩ := hLSS d (K + 1) (by omega) ρ hρ0 hρ1
  have hδ : (0 : ℝ) < 1 - max pL 0 := by
    have : max pL 0 < 1 := max_lt hpL1 zero_lt_one
    linarith
  obtain ⟨k, hk, hkP⟩ := h4 (1 - max pL 0) hδ
  -- the tile field and its law
  set F : (Site d → ℤ) → (Site d → Bool) :=
    fun η j => decide (StronglyBoxCrossed η k j) with hF
  have hFm : Measurable F := glw_box_measurable d k
  set μ : Measure (Site d → Bool) := P.map F with hμ
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hFm.aemeasurable
  have hmarg : ∀ s : Site d, ENNReal.ofReal pL ≤ μ {ω | ω s = true} := by
    intro s
    have hm : MeasurableSet {ω : Site d → Bool | ω s = true} :=
      measurableSet_eq_fun (measurable_pi_apply s) measurable_const
    rw [hμ, Measure.map_apply hFm hm]
    have hset : F ⁻¹' {ω : Site d → Bool | ω s = true} = {η | StronglyBoxCrossed η k s} := by
      ext η; simp [hF]
    rw [hset]
    have h2 := hkP s
    rw [show (1 : ℝ) - (1 - max pL 0) = max pL 0 by ring] at h2
    exact le_trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)) h2.le
  have hdomA : ∀ A : Set (Site d → Bool), MeasurableSet A → IsIncreasingSet A →
      sitePercolation d ρ A ≤ μ A :=
    fun A hA hinc => hdom μ inferInstance (hK k hk) hmarg A hA hinc
  -- the cluster of Bernoulli site percolation
  haveI hνprob : IsProbabilityMeasure (sitePercolation d ρ) := rn_infinitePi_isProb hρ0 hρ1.le
  set ν : Measure (Site d → Bool) := sitePercolation d ρ with hν
  have hindep : iIndepFun (fun (x : Site d) (ω : Site d → Bool) => ω x) ν :=
    rn_bernoulli_iIndep hρ0 hρ1.le
  have hνmarg : ∀ x : Site d, ENNReal.ofReal q ≤ ν {ω | (fun (x : Site d) (ω : Site d → Bool) => ω x) x ω = true} := by
    intro x
    show ENNReal.ofReal q ≤ ν {ω | ω x = true}
    rw [hν, sitePercolation, rn_bernoulli_marg hρ0 hρ1.le x]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hae := hcore ν (fun (x : Site d) (ω : Site d → Bool) => ω x)
    (fun x => measurable_pi_apply x) hindep hνmarg
  set Bad : Set (Site d → Bool) := {ω | ¬ ∃ S : Set (Site d), S.Infinite ∧ (∀ x ∈ S, ω x = true) ∧
    (∀ x ∈ S, ∀ y ∈ S, y ∈ componentIn S x) ∧ RnHoleProp d S ∧ RnChemClause d C S} with hBad
  have hBad0 : ν Bad = 0 := ae_iff.mp hae
  set Z : Set (Site d → Bool) := (toMeasurable ν Bad)ᶜ with hZ
  have hZm : MeasurableSet Z := (measurableSet_toMeasurable ν Bad).compl
  have hZν : ν Zᶜ = 0 := by
    rw [hZ, compl_compl, measure_toMeasurable]; exact hBad0
  have hZgood : ∀ ω ∈ Z, ∃ S : Set (Site d), S.Infinite ∧ (∀ x ∈ S, ω x = true) ∧
      (∀ x ∈ S, ∀ y ∈ S, y ∈ componentIn S x) ∧ RnHoleProp d S ∧ RnChemClause d C S := by
    intro ω hω
    by_contra hcon
    exact hω (subset_toMeasurable ν Bad hcon)
  -- the coupling
  obtain ⟨B, hBm, hBμ, hBex⟩ := rn_strassen_bool ν μ hdomA Z hZm hZν
  have hBP : ∀ᵐ η ∂P, F η ∈ B := by
    rw [ae_iff]
    have := hBμ
    rw [hμ, Measure.map_apply hFm hBm.compl] at this
    exact this
  refine ⟨k, hk, 1, C, one_pos, by linarith, ?_⟩
  filter_upwards [hBP] with η hη
  obtain ⟨ζ, hζZ, hζle⟩ := hBex _ hη
  obtain ⟨S, hSinf, hSopen, hSconn, ⟨n0h, hn0h⟩, ⟨n0c, hn0c⟩⟩ := hZgood ζ hζZ
  refine ⟨S, hSinf, fun j hj => ?_, hSconn, ⟨n0h, hn0h⟩, ⟨n0c, hn0c⟩⟩
  have h2 := hζle j (hSopen j hj)
  simpa [hF] using h2

end Exploding
