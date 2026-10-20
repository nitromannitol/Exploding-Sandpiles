/-
Proposition 5.1: the Kingman input of the Section 5 assembly, corrected.

`glw2_Section3Convergence` consumes `glw2_KingmanCore`, which is false
(`king_not_glw2_KingmanCore`), so the implication is vacuously true and says nothing.  The
corrected assembly consumes `king_LipKingman` (proved: `king_LipKingman_true`) together with the
local Lipschitz bound `glw2_LipschitzLocal`, which is what the paper's proof of Proposition 5.1
uses.  The hypotheses of the reduction of Proposition 5.1 are then the two true statements
`glw2_LipschitzLocal d ηmin P` and `king_Section3Convergence d hd ηmin hηmin L hL P`.
-/
import Exploding.Support.GLWProof2
import Exploding.Support.KingmanBALip
import Exploding.Support.KingmanBARefute

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory
open scoped Classical

namespace Exploding

/-- The Section-3 convergence assembly with the corrected Kingman input `king_LipKingman`.  It
consumes the two finite-range facts (A) and (B), the Lipschitz-transfer subadditive ergodic
theorem and the local Lipschitz bound, and returns the Proposition 5.1 conclusion. -/
def king_Section3Convergence (d : ℕ) (_hd : 2 ≤ d) (ηmin : ℤ) (_hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (_hL : L.index ≠ 0) (P : Measure (Site d → ℤ)) : Prop :=
  IsProbabilityMeasure P → (∀ᵐ η ∂P, InOmega d ηmin η) → StationaryOn d L P → ErgodicOn d L P →
  FiniteRangeOfDependence d P → PathFillingHyp d P → StronglyBoxCrossingHyp d P →
  Exploding.External.LiggettSchonmannStacey →
  Exploding.External.LiggettSchonmannStaceyBoundedDegree →
  Exploding.External.MathieuHoleVolume →
  Exploding.External.AntalPisztoraChemicalDistance →
  (∀ (k : Fin d → ℕ), (∀ i, 0 < k i) →
    ∃ m : ℕ, KDependent m (P.map fun η (j : Site d) => decide (StronglyBoxCrossed η k j))) →
  (∀ (y : Site d), y ∈ L → y ≠ 0 →
    ∀ (s : Finset (Site d)) (S : Set (s → ℤ)), MeasurableSet S →
      ∃ n : ℕ, P (cylinder s S ∩
        (fun η : Site d → ℤ => fun z => η (y + z))^[n] ⁻¹' cylinder s S) =
        P (cylinder s S) * P (cylinder s S)) →
  king_LipKingman → glw2_LipschitzLocal d ηmin P → glw_Conclusion d P

/-- The deterministic assembly of Proposition 5.1 with the corrected Kingman input: (A) and (B)
are supplied by `glw2_kdep`/`glw2_shift_mixing`, the Kingman input is `king_LipKingman_true`, and
the two remaining Section-3 pieces are the open conjuncts. -/
theorem king_glw_assemble (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : ErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P)
    (hLSS : Exploding.External.LiggettSchonmannStacey)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (hlips : glw2_LipschitzLocal d ηmin P)
    (hconv : king_Section3Convergence d hd ηmin hηmin L hL P) :
    glw_Conclusion d P :=
  hconv hP hsupp hstat herg h1 h3 h4 hLSS hLSSB hHole hChem
    (fun k hk => glw2_kdep d P h1 k hk)
    (fun y hy hy0 s S hS => glw2_shift_mixing d P h1 y
      (glw_shift_ergodic_meas_pres d L P hstat y hy) hy0 s S hS)
    king_LipKingman_true hlips

/-- The old assembly was vacuous: its Kingman hypothesis is false, so
`glw2_Section3Convergence` holds for every `P`, with no content.  (Recorded so that nobody
discharges the open conjunct through it.) -/
theorem king_glw2_Section3Convergence_vacuous (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ)) :
    glw2_Section3Convergence d hd ηmin hηmin L hL P :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hcore _ => (king_not_glw2_KingmanCore hcore).elim

end Exploding

namespace Exploding

variable {d : ℕ}

theorem king_abs_coord_le_mnorm (v : Site d) (i : Fin d) : |v i| ≤ mnorm v :=
  Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)

theorem king_mnorm_nat_smul (m : ℕ) (v : Site d) : mnorm ((m : ℤ) • v) = (m : ℤ) * mnorm v := by
  simp only [mnorm, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (Int.natCast_nonneg m),
    Finset.mul_sum]

/-- **From a pair Lipschitz bound to the hypothesis of `king_lipKingman`.**  Let `F x` be the
arrival time from `0` to `x` and `G x x'` the arrival time from `x` to `x'`.  If
`F x' ≤ F x + G x x'` (subadditivity in the base point) and
`G x x' ≤ C |x - x'| + (log n)^γ` on the box `cent d n` for `n ≥ n0` (the second bound of
`eq:generalized_lipschitz`, as in `glw2_LipschitzLocal`), then along the ray `n • y` the sequence
`F (n • y)` is Lipschitz upward up to a sublinear error, with constant `C |y|`. -/
theorem king_lip_of_pairs (F : Site d → ℝ) (G : Site d → Site d → ℝ) (C γ : ℝ) (n0 : ℕ)
    (htri : ∀ x x' : Site d, F x' ≤ F x + G x x')
    (hG : ∀ n : ℕ, n0 ≤ n → ∀ x x' : Site d, x ∈ cent d n → x' ∈ cent d n →
      G x x' ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ) (y : Site d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ n' : ℕ, n ≤ n' → n' ≤ 2 * n →
      F ((n' : ℤ) • y) ≤ F ((n : ℤ) • y) + (C * (mnorm y : ℝ)) * ((n' : ℝ) - n) + ε * n := by
  set M : ℕ := (mnorm y).toNat + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hMZ : mnorm y ≤ (M : ℤ) := by rw [hM]; push_cast; omega
  have hmem : ∀ N k : ℕ, k * M ≤ N → ((k : ℤ) • y) ∈ cent d N := by
    intro N k hk i
    have h1 : |((k : ℤ) • y) i| = (k : ℤ) * |y i| := by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (Int.natCast_nonneg k)]
    rw [h1]
    have h2 : |y i| ≤ (M : ℤ) := le_trans (king_abs_coord_le_mnorm y i) hMZ
    calc (k : ℤ) * |y i| ≤ (k : ℤ) * M := mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg k)
      _ = ((k * M : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (N : ℤ) := by exact_mod_cast hk
  exact king_lip_of_log (fun n : ℕ => F ((n : ℤ) • y)) (C * (mnorm y : ℝ)) γ M hM1 n0 (by
    intro N hN n₁ n₂ h12 h2M
    have hx2 := hmem N n₂ h2M
    have hx1 := hmem N n₁ (le_trans (Nat.mul_le_mul_right M h12) h2M)
    have h1 := hG N hN ((n₁ : ℤ) • y) ((n₂ : ℤ) • y) hx1 hx2
    have e : (n₁ : ℤ) • y - (n₂ : ℤ) • y = -(((n₂ - n₁ : ℕ) : ℤ) • y) := by
      rw [← neg_sub, ← sub_smul, Nat.cast_sub h12]
    have hneg : mnorm (-(((n₂ - n₁ : ℕ) : ℤ) • y)) = mnorm (((n₂ - n₁ : ℕ) : ℤ) • y) := by
      simp only [mnorm, Pi.neg_apply, abs_neg]
    rw [e, hneg, king_mnorm_nat_smul] at h1
    have h3 : (((n₂ - n₁ : ℕ) : ℤ) * mnorm y : ℤ) = (((n₂ : ℤ) - n₁) * mnorm y : ℤ) := by
      rw [Nat.cast_sub h12]
    have h4 : (((((n₂ - n₁ : ℕ) : ℤ) * mnorm y : ℤ)) : ℝ) = ((n₂ : ℝ) - n₁) * (mnorm y : ℝ) := by
      rw [h3]; push_cast; ring
    rw [h4] at h1
    have h5 := htri ((n₁ : ℤ) • y) ((n₂ : ℤ) • y)
    show F ((n₂ : ℤ) • y) ≤ F ((n₁ : ℤ) • y) + C * (mnorm y : ℝ) * ((n₂ : ℝ) - n₁)
      + Real.log N ^ γ
    nlinarith [h1, h5])

/-- **The Kingman interface for Proposition 5.1/5.2.**  Let `T` be an ergodic measure-preserving
map of `(Ω, μ)`, `y` a lattice direction, `F η x ≥ 0` the arrival time from `0` to `x`
(measurable in `η`) and `G η x x'` the arrival time from `x` to `x'`.  Assume the cocycle identity
`F η ((m+n) y) ≤ F η (m y) + F (T^m η) (n y)` for all `η`, the triangle inequality
`F η x' ≤ F η x + G η x x'` almost surely, and the pair Lipschitz bound almost surely (with
constants that may depend on `η`).  Then `F η (n y) / n` converges almost surely. -/
theorem king_dir_of_pairs {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (herg : Ergodic T μ) (y : Site d)
    (F : Ω → Site d → ℝ) (G : Ω → Site d → Site d → ℝ)
    (hF0 : ∀ η x, 0 ≤ F η x) (hFm : ∀ x, Measurable (fun η => F η x))
    (hcocycle : ∀ (m n : ℕ) η, F η (((m + n : ℕ) : ℤ) • y) ≤
      F η ((m : ℤ) • y) + F (T^[m] η) ((n : ℤ) • y))
    (htri : ∀ᵐ η ∂μ, ∀ x x' : Site d, F η x' ≤ F η x + G η x x')
    (hG : ∀ᵐ η ∂μ, ∃ (C γ : ℝ) (n0 : ℕ), ∀ n : ℕ, n0 ≤ n → ∀ x x' : Site d,
      x ∈ cent d n → x' ∈ cent d n → G η x x' ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ) :
    ∃ L : ℝ, ∀ᵐ η ∂μ,
      Tendsto (fun n : ℕ => F η ((n : ℤ) • y) / (n : ℝ)) atTop (nhds L) := by
  refine king_lipKingman μ T hT herg (fun n η => F η ((n : ℤ) • y)) hcocycle
    (fun n η => hF0 _ _) (fun n => hFm _) ?_
  filter_upwards [htri, hG] with η h1 h2
  obtain ⟨C, γ, n0, hn0⟩ := h2
  exact ⟨C * (mnorm y : ℝ), king_lip_of_pairs (F η) (G η) C γ n0 h1 hn0 y⟩

end Exploding
