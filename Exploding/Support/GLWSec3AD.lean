/-
Proposition 5.1 of the paper (generalized last wave): the percolation content of the generalization of
Proposition 2.2.  The good-edge field of an arbitrary law of bits that dominates Bernoulli bond
percolation of a prescribed density carries an infinite connected set of good sites with small holes
and linear chemical distance.  This is the body of `rn_core` after the domination, which there is
obtained for independent bits.
-/
import Exploding.Support.RNProofCore

open MeasureTheory ProbabilityTheory Exploding LatticeProb Filter

namespace Exploding

variable {d : ℕ}

/-- **The percolation content of the generalization of Proposition 2.2.**  There are a density
`ρ₁ < 1` and a constant `C` such that for every field of bits whose good-edge field dominates, on
measurable increasing events, Bernoulli bond percolation of density `ρ₁`, almost surely the open
sites contain an infinite connected set with small holes and chemical distance at most `C` times
the distance. -/
theorem glws_core_dom (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) (d : ℕ) (hd : 2 ≤ d)
    (hPE : ∃ qP : ℝ, 0 ≤ qP ∧ qP < 1 ∧ ∀ q : ℝ, qP ≤ q → q ≤ 1 → bondTheta d q ≠ 0) :
    ∃ ρ₁ : ℝ, 0 ≤ ρ₁ ∧ ρ₁ < 1 ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Site d → Ω → Bool), (∀ x, Measurable (X x)) →
        (∀ A : Set (RnBond d → Bool), MeasurableSet A → IsIncreasingSet A →
          bernoulliProduct (RnBond d) ρ₁ A ≤
            P {ω | (fun e : RnBond d => X e.1 ω && X (e.1 + unit e.2) ω) ∈ A}) →
        ∀ᵐ ω ∂P, ∃ S : Set (Site d), S.Infinite ∧ (∀ x ∈ S, X x ω = true) ∧
          (∀ x ∈ S, ∀ y ∈ S, y ∈ componentIn S x) ∧ RnHoleProp d S ∧ RnChemClause d C S := by
  obtain ⟨qP, hqP0, hqP1, hPE'⟩ := hPE
  have hθ : bondTheta d qP ≠ 0 := hPE' qP le_rfl hqP1.le
  have hcrit : bondCritical d ≤ qP := rn_bondCritical_le hqP0 hPE'
  obtain ⟨r, hr1, hhole⟩ := rn_siteField_ae hLSSB hHole d hd qP hqP0 hqP1 hθ
  set m : ℝ := max (max r qP) 0 with hm
  have hm1 : m < 1 := max_lt (max_lt hr1 hqP1) zero_lt_one
  set ρ₁ : ℝ := (1 + m) / 2 with hρ₁
  have hρ₁0 : 0 ≤ ρ₁ := by rw [hρ₁]; linarith [le_max_right (max r qP) 0]
  have hρ₁1 : ρ₁ < 1 := by rw [hρ₁]; linarith
  have hrρ : r ≤ ρ₁ := by
    rw [hρ₁]; linarith [le_max_left r qP, le_max_left (max r qP) 0]
  have hqρ : bondCritical d < ρ₁ := by
    have : qP ≤ m := (le_max_right r qP).trans (le_max_left _ _)
    rw [hρ₁]; linarith
  obtain ⟨C, hC1, hchem⟩ := rn_chem_ae hChem d hd hqρ hρ₁0 hρ₁1.le
  refine ⟨ρ₁, hρ₁0, hρ₁1, C, hC1, ?_⟩
  intro Ω _ P _ X hX hdom
  haveI : IsProbabilityMeasure (bondPercolation d ρ₁) := rn_infinitePi_isProb hρ₁0 hρ₁1.le
  set ν : Measure (RnBond d → Bool) := bondPercolation d ρ₁ with hν
  have hholeρ := hhole ρ₁ hrρ hρ₁1.le
  -- the good set of bond configurations
  set Bad : Set (RnBond d → Bool) := {ζ | ¬ ((∃ i, {y | (openBondGraph ζ).Reachable i y}.Infinite ∧
        RnHoleProp d {y | (openBondGraph ζ).Reachable i y}) ∧ RnChemProp d C ζ)} with hBad
  have hBad0 : ν Bad = 0 := by
    refine measure_mono_null (fun ζ hζ => ?_) (measure_union_null hholeρ (ae_iff.mp hchem))
    by_contra hcon
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hcon
    exact hζ ⟨hcon.1, hcon.2⟩
  set Z : Set (RnBond d → Bool) := (toMeasurable ν Bad)ᶜ with hZ
  have hZm : MeasurableSet Z := (measurableSet_toMeasurable ν Bad).compl
  have hZν : ν Zᶜ = 0 := by
    rw [hZ, compl_compl, measure_toMeasurable]; exact hBad0
  have hZgood : ∀ ζ ∈ Z, (∃ i, {y | (openBondGraph ζ).Reachable i y}.Infinite ∧
        RnHoleProp d {y | (openBondGraph ζ).Reachable i y}) ∧ RnChemProp d C ζ := by
    intro ζ hζ
    by_contra hcon
    exact hζ (subset_toMeasurable ν Bad hcon)
  -- the coupling
  set F : Ω → RnBond d → Bool := fun ω e => X e.1 ω && X (e.1 + unit e.2) ω with hF
  have hFm : Measurable F := rn_edge_measurable X hX
  haveI : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hFm.aemeasurable
  have hdomB : ∀ A : Set (RnBond d → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ (P.map F) A := by
    intro A hA hinc
    rw [Measure.map_apply hFm hA]
    exact hdom A hA hinc
  obtain ⟨B, hBm, hBμ, hBex⟩ := rn_strassen_bool ν (P.map F) hdomB Z hZm hZν
  have hae : ∀ᵐ ω ∂P, F ω ∈ B := by
    rw [ae_iff]
    have := hBμ
    rw [Measure.map_apply hFm hBm.compl] at this
    exact this
  refine hae.mono fun ω hω => ?_
  obtain ⟨ζ, hζZ, hζle⟩ := hBex _ hω
  obtain ⟨⟨i, hinf, hhol⟩, hch⟩ := hZgood ζ hζZ
  refine rn_conclude (g := fun x => X x ω) ?_ hinf hhol hch
  intro b hb
  have := hζle b hb
  simp only [hF, Bool.and_eq_true] at this
  exact this

end Exploding
