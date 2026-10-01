/-
Continuation of `MKingman3.lean`, packet ds4g.

The induced-system route (R2) of `MKingman2`/`MKingman3` reduces the general
moment-free Kingman theorem `mk_kingman_linear` to two independent pieces:

* the measure-theoretic Kac package `mk3_kac` for the induced map, assembled from
  the first-return map `mk2_inducedMap`, the normalised restriction
  `mk3_normalizedRestrict` and the cumulative return sequence `mk2_returnSeq`;
* the identification of the limit: convergence of the induced cocycle
  `G k = g (r_k)` divided by `k`, together with Birkhoff's theorem for the
  cumulative return time `r_k`, gives convergence of `g (r_k) / r_k`.

This file contributes the parts of the second item that are pure limit
arithmetic, and isolates the first item as the single proposition
`mk4_boundedAboveKingman`.  Its content is exactly Kingman's theorem for a
subadditive process that is bounded above by an a.s. finite random variable (and
bounded below by a linear function): `LatticeProb.ae_tendsto_div` does not apply
there, because it needs `Integrable (h 1)`, which the a.s. upper bound does not
supply.  The equivalence below records that this bounded-above form and
`mk_kingman_linear` are the same proposition, so no strength is lost or gained by
the reformulation.  The paper's repair replaces the missing maximal ergodic
theorem for such processes by the second (Lipschitz) bound of
`eq:generalized_lipschitz`.
-/
import Exploding.Support.MKingman3
import Mathlib.Dynamics.Ergodic.Function

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory

namespace Exploding

variable {Ω : Type}

/-- The cumulative return sequence is the sum of the successive first-return
times along the induced orbit: `r k = ∑_{j<k} r_1(T_A^j x)`. -/
theorem mk4_returnSeq_eq_sum [MeasurableSpace Ω] (T : Ω → Ω) (A : Set Ω) (x : Ω) (k : ℕ) :
    mk2_returnSeq T A x k
      = ∑ j ∈ Finset.range k, mk2_returnTime T A ((mk2_inducedMap T A)^[j] x) := by
  induction k with
  | zero => simp [mk2_returnSeq]
  | succ k ih =>
      rw [mk2_returnSeq, ih, Finset.sum_range_succ]

/-- The cumulative return sequence is nondecreasing, being a sum of nonnegative
terms. -/
theorem mk4_returnSeq_mono [MeasurableSpace Ω] (T : Ω → Ω) (A : Set Ω) (x : Ω) :
    Monotone (mk2_returnSeq T A x) := by
  intro j k hjk
  rw [mk4_returnSeq_eq_sum, mk4_returnSeq_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hjk)
    (fun i _ _ => Nat.zero_le _)

/-- **Arithmetic core of the identification of the limit.**  If `G k / k → L` and
the cumulative return time satisfies `r k / k → ρ` with `ρ > 0`, then
`G k / r k → L / ρ`. -/
theorem mk4_tendsto_div_of_div (G r : ℕ → ℝ) (L ρ : ℝ) (hρ : 0 < ρ)
    (hG : Tendsto (fun k : ℕ => G k / (k : ℝ)) atTop (nhds L))
    (hr : Tendsto (fun k : ℕ => r k / (k : ℝ)) atTop (nhds ρ)) :
    Tendsto (fun k : ℕ => G k / r k) atTop (nhds (L / ρ)) := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hdiv : Tendsto (fun k : ℕ => (G k / (k : ℝ)) / (r k / (k : ℝ))) atTop (nhds (L / ρ)) :=
    hG.div hr hρne
  refine hdiv.congr' ?_
  filter_upwards [hr.eventually_ne hρne, eventually_gt_atTop 0] with k hrk hk
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrkne : r k ≠ 0 := fun h => hrk (by rw [h, zero_div])
  field_simp

/-- **Identification of the limit along the return times.**  If the induced
cocycle `G k = g (r_k)` has normalised limit `L` and the cumulative return time
has normalised limit `ρ > 0`, then `g (r_k) / r_k` converges to `L / ρ` on the
induced space.  With Birkhoff's theorem for the return time, `ρ` is the mean
return time `∫ r_1 dμ_A = 1 / μ(A)`, and the limit is `L · μ(A)`. -/
theorem mk4_return_limit [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω → Ω) (g : ℕ → Ω → ℝ) (A : Set Ω) (L ρ : ℝ) (hρ : 0 < ρ)
    (hG : ∀ᵐ x ∂(mk3_normalizedRestrict μ A),
      Tendsto (fun k : ℕ => g (mk2_returnSeq T A x k) x / (k : ℝ)) atTop (nhds L))
    (hr : ∀ᵐ x ∂(mk3_normalizedRestrict μ A),
      Tendsto (fun k : ℕ => (mk2_returnSeq T A x k : ℝ) / (k : ℝ)) atTop (nhds ρ)) :
    ∀ᵐ x ∂(mk3_normalizedRestrict μ A),
      Tendsto (fun k : ℕ => g (mk2_returnSeq T A x k) x / (mk2_returnSeq T A x k : ℝ))
        atTop (nhds (L / ρ)) := by
  filter_upwards [hG, hr] with x hGx hrx
  exact mk4_tendsto_div_of_div _ _ L ρ hρ hGx hrx

/-- **The bounded-above form of the moment-free Kingman theorem.**  A
subadditive cocycle `h` over a measure-preserving ergodic map, bounded below by a
linear function and bounded above by an a.s. finite random variable (no
integrability), converges a.s.  This is the exact missing input:
`LatticeProb.ae_tendsto_div` needs `Integrable (h 1)`, and an upper bound
`h n ≤ K ∈ L^0` does not give it. -/
def mk4_boundedAboveKingman : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω), MeasurePreserving T μ μ → Ergodic T μ →
    ∀ (h : ℕ → Ω → ℝ), (∀ m n x, h (m + n) x ≤ h m x + h n (T^[m] x)) →
    (∃ c : ℝ, ∀ n x, -c * n ≤ h n x) → (∀ n, Measurable (h n)) →
    (∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, h n x ≤ K) →
    ∃ L : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => h n x / (n : ℝ)) atTop (nhds L)

/-- `mk_kingman_linear` follows from the bounded-above form by subtracting the
linear growth rate `C n`; subadditivity is preserved by the subtraction, and the
random linear bound becomes the random uniform bound, while the lower bound
`g ≥ 0` becomes `h ≥ -C n`. -/
theorem mk4_kingman_linear_of_boundedAbove (hBA : mk4_boundedAboveKingman) :
    mk_kingman_linear := by
  intro Ω _ μ _ T hT herg g hsub hg hgm hlin
  obtain ⟨C, hC⟩ := hlin
  set h' : ℕ → Ω → ℝ := fun n x => g n x - C * n with hh'
  have hsub' : ∀ m n x, h' (m + n) x ≤ h' m x + h' n (T^[m] x) := by
    intro m n x
    have := hsub m n x
    simp only [hh']
    push_cast
    linarith
  have hlow' : ∃ c : ℝ, ∀ n x, -c * n ≤ h' n x := by
    refine ⟨max C 0, fun n x => ?_⟩
    have := hg n x
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [hh']
    nlinarith [le_max_left C 0]
  have hbdd' : ∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, h' n x ≤ K := by
    filter_upwards [hC] with x hx
    obtain ⟨K, hK⟩ := hx
    exact ⟨K, fun n => by simp only [hh']; linarith [hK n]⟩
  obtain ⟨L, hL⟩ := hBA μ T hT herg h' hsub' hlow'
    (fun n => (hgm n).sub measurable_const) hbdd'
  refine ⟨L + C, ?_⟩
  filter_upwards [hL] with x hx
  have hx' : Tendsto (fun n : ℕ => h' n x / (n : ℝ) + C) atTop (nhds (L + C)) :=
    hx.add tendsto_const_nhds
  refine hx'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [hh']
  field_simp
  ring

/-- Conversely, the bounded-above form is `mk_kingman_linear` applied to
`h n + c n`, which is nonnegative and has the linear bound `c n + K`; so the two
propositions are equivalent. -/
theorem mk4_boundedAboveKingman_of_kingman (hK : mk_kingman_linear) :
    mk4_boundedAboveKingman := by
  intro Ω _ μ _ T hT herg h hsub hlow hgm hbdd
  obtain ⟨c, hc⟩ := hlow
  set g : ℕ → Ω → ℝ := fun n x => h n x + c * n with hg'
  have hsubg : ∀ m n x, g (m + n) x ≤ g m x + g n (T^[m] x) := by
    intro m n x
    have := hsub m n x
    simp only [hg']
    push_cast
    linarith
  have hg0 : ∀ n x, 0 ≤ g n x := by
    intro n x
    have := hc n x
    simp only [hg']
    linarith
  have hbddg : ∃ C : ℝ, ∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K := by
    refine ⟨c, ?_⟩
    filter_upwards [hbdd] with x hx
    obtain ⟨K, hK⟩ := hx
    exact ⟨K, fun n => by simp only [hg']; linarith [hK n]⟩
  obtain ⟨L, hL⟩ := hK μ T hT herg g hsubg hg0
    (fun n => (hgm n).add measurable_const) hbddg
  refine ⟨L - c, ?_⟩
  filter_upwards [hL] with x hx
  have hx' : Tendsto (fun n : ℕ => g n x / (n : ℝ) - c) atTop (nhds (L - c)) :=
    hx.sub tendsto_const_nhds
  refine hx'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [hg']
  field_simp
  ring

/-- The two formulations are the same proposition. -/
theorem mk4_boundedAboveKingman_iff : mk4_boundedAboveKingman ↔ mk_kingman_linear :=
  ⟨mk4_kingman_linear_of_boundedAbove, mk4_boundedAboveKingman_of_kingman⟩

end Exploding
