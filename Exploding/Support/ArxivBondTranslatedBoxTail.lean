import Exploding.Support.ArxivBondFiniteHoleTail
import Exploding.Support.SubPoly

/-!
# Translated centred-box tail of the finite-hole event

For `d ≥ 2`, the fixed-site actual-bond finite-hole tail `C · exp(-c √s)` from
`arxiv_bond_finite_hole_tail_exp` holds at every root. Summing it over the `(2R+1)^d` sites of a
translated box `a + cent d R` gives the bound `(2R+1)^d · C · exp(-c √s)` for the event that
some root in that translate has a finite hole of size at least `s`.

The union is finite and taken over the sites of the translate only, so no union over cluster roots
is needed. The constants `q0`, `C`, `c` are fixed before the centre `a`, the radius `R`, the
threshold `s`, and the density `q`. The case `R = 0` and the density `q = 1` need no separate
argument.

This is only the hole-event part of the source moment estimate. It does not supply the projection,
the almost-sure cutoff, or any integrability statement.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- For `d ≥ 2` there are fixed constants `q0 < 1`, `C > 0`, `c > 0` such that, for every centre
`a`, radius `R`, threshold `s`, and density `q ∈ [q0, 1]`, the probability that some root `z` of
the translate `a + cent d R` has a finite hole of size at least `s` is at most
`(2R+1)^d · C · exp(-c √s)`. -/
theorem arxiv_bond_finite_hole_translated_box_tail (d : ℕ) (hd : 2 ≤ d) :
    ∃ q0 C c : ℝ, 0 ≤ q0 ∧ q0 < 1 ∧ 0 < C ∧ 0 < c ∧
      ∀ (a : Site d) (R s : ℕ) {q : ℝ}, q0 ≤ q → q ≤ 1 →
        bondPercolation d q
          {ζ | ∃ z : Site d, z - a ∈ cent d R ∧ ∃ i : Site d,
            z ∉ {y : Site d | (openBondGraph ζ).Reachable i y} ∧
            (componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).Finite ∧
            s ≤ (componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).ncard} ≤
        ENNReal.ofReal ((((2 * R + 1 : ℕ) ^ d : ℕ) : ℝ) * C *
          Real.exp (-c * Real.sqrt (s : ℝ))) := by
  obtain ⟨_, q0, C, c, _, hq0, hq01, hC, hc, htail⟩ :=
    arxiv_bond_finite_hole_tail_exp d hd
  refine ⟨q0, C, c, hq0, hq01, hC, hc, ?_⟩
  intro a R s q hq hq1
  obtain ⟨hboxFinite, hboxNcard⟩ := cent_finite_ncard d R
  have hinj : Function.Injective (fun z : Site d => z - a) := by
    intro x y h
    simpa using h
  have hTfin : ((fun z : Site d => z - a) ⁻¹' (cent d R : Set (Site d))).Finite :=
    hboxFinite.preimage (fun _ _ _ _ h => hinj h)
  obtain ⟨F, hF⟩ : ∃ F : Finset (Site d), ∀ z : Site d, z ∈ F ↔ z - a ∈ cent d R :=
    ⟨hTfin.toFinset, fun z => hTfin.mem_toFinset⟩
  have hsubRange : (cent d R : Set (Site d)) ⊆ Set.range (fun z : Site d => z - a) :=
    fun w _ => ⟨w + a, by simp⟩
  have hFcard : F.card = (2 * R + 1) ^ d := by
    have hset :
        (F : Set (Site d)) = (fun z : Site d => z - a) ⁻¹' (cent d R : Set (Site d)) := by
      ext z
      exact hF z
    rw [← Set.ncard_coe_finset F, hset,
      Set.ncard_preimage_of_injective_subset_range hinj hsubRange]
    exact hboxNcard
  let E : Site d → Set (Site d × Fin d → Bool) := fun z =>
    {ζ | ∃ i : Site d,
      z ∉ {y : Site d | (openBondGraph ζ).Reachable i y} ∧
      (componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).Finite ∧
      s ≤ (componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).ncard}
  have hsub : {ζ | ∃ z : Site d, z - a ∈ cent d R ∧ ∃ i : Site d,
      z ∉ {y : Site d | (openBondGraph ζ).Reachable i y} ∧
      (componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).Finite ∧
      s ≤ (componentIn ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).ncard} ⊆
      ⋃ z ∈ F, E z := by
    rintro ζ ⟨z, hz, i, hzi, hfinite, hlarge⟩
    exact Set.mem_iUnion₂.mpr ⟨z, (hF z).mpr hz, ⟨i, hzi, hfinite, hlarge⟩⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le F E).trans ?_)
  have hterm : ∀ z ∈ F,
      bondPercolation d q (E z) ≤ ENNReal.ofReal (C * Real.exp (-c * Real.sqrt (s : ℝ))) :=
    fun z _ => htail z s hq hq1
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  have hN : (0 : ℝ) ≤ (((2 * R + 1) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Finset.sum_const, nsmul_eq_mul, hFcard, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul hN, mul_assoc]

end Exploding
