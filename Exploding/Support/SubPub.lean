/-
Support for Lemma 3.6 of `paper/exploding.tex`: the probability bounds on the
toy law, the macroscopic cube index, and the wave's own mass bound.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubPen

open Exploding LatticeProb MeasureTheory

namespace Exploding

theorem aux_chipLaw_prob (a b : ℤ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (chipLaw a b p) := by
  rw [isProbabilityMeasure_iff, chipLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [Measure.dirac_apply_of_mem (Set.mem_univ a), Measure.dirac_apply_of_mem (Set.mem_univ b)]
  simp only [smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp (by linarith)]
  simp

theorem aux_chipLaw_ae (a b : ℤ) (p : ℝ) : ∀ᵐ v ∂(chipLaw a b p), v = a ∨ v = b := by
  rw [ae_iff]
  have hset : {v : ℤ | ¬(v = a ∨ v = b)} = ({a, b} : Set ℤ)ᶜ := by ext v; simp
  rw [hset, chipLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp [Set.indicator_of_notMem]

theorem aux_toyLaw_eval_ae (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (x : Site d) :
    ∀ᵐ η ∂(toyLaw d p), 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
  haveI : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
    aux_chipLaw_prob _ _ _ (le_of_lt hp) (le_of_lt hp1)
  have hmap : Measure.map (fun η : Site d → ℤ => η x) (toyLaw d p)
      = chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p := by
    rw [toyLaw, productLaw]
    exact Measure.infinitePi_map_eval _ x
  have hf : AEMeasurable (fun η : Site d → ℤ => η x) (toyLaw d p) :=
    (measurable_pi_apply x).aemeasurable
  have hmeas : MeasurableSet {v : ℤ | 2 * (d : ℤ) - 2 ≤ v ∧ v ≤ 2 * (d : ℤ) - 1} := by
    measurability
  rw [← ae_map_iff hf hmeas, hmap]
  filter_upwards [aux_chipLaw_ae (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p] with v hv
  rcases hv with h | h <;> rw [h] <;> omega

theorem aux_pub_reach_eta_bounds (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
  exact ae_all_iff.2 (fun x => aux_toyLaw_eval_ae d p hp hp1 x)


/-! ### (a) the explosion reaches a good cube of the infinite cluster -/

-- Re-examined: `Exploding.Frozen.square_lower_bound` IS fully proven in this
-- repo (`Exploding/Frozen/SquareLowerBound.lean`, 0 `sorry`), so the earlier
-- "not transcribed anywhere" assessment was wrong.  It does not, however,
-- transfer directly: it needs mass `m ≥ (2d)^(dn)` to guarantee reaching
-- `[-n,n]^d`, and `wave_mono_n` (`Exploding/Support/Toppling.lean`) shows the
-- wave is monotone INCREASING in mass, so `Exploding.Frozen.finite_exploding`'s
-- witness `N` (found by making the mass large) says nothing about whether the
-- true last wave — mass `waveThreshold η 0`, which may be far smaller than
-- `N` — also reaches a good cube.  The argument below is mass-independent: it
-- shows any wave that fails to stabilize (in particular the one at
-- `waveThreshold η 0`, which qualifies for free via `Nat.sInf_mem`) cannot
-- have its whole macroscopic footprint confined forever to one finite hole of
-- `C_∞`, since a wave confined to a fixed finite set and bounded above by its
-- own mass must eventually stabilize (elementary: nondecreasing bounded
-- integer sequences on a finite index set become simultaneously constant).

/-- The macroscopic cube index containing the microscopic site `x` at scale
`k ≥ 1`: the unique `i` with `x - k•i ∈ cube d k`. -/
noncomputable def macroIdx {d : ℕ} (k : ℕ) (x : Site d) : Site d :=
  fun i => (x i - 1) / (k : ℤ)

/-- **New.** `x` lies in the cube named by its own macro index: unfolds to
`1 ≤ (x i - 1) % k + 1 ≤ k`, from `Int.ediv_add_emod`, `Int.emod_nonneg` and
`Int.emod_lt_of_pos`. -/
theorem aux_mem_cube_of_macroIdx {d : ℕ} (k : ℕ) (hk : 1 ≤ k) (x : Site d) :
    x - (k : ℤ) • macroIdx k x ∈ cube d k := by
  have hk' : (0 : ℤ) < (k : ℤ) := Nat.cast_pos.mpr hk
  have hne : (k : ℤ) ≠ 0 := ne_of_gt hk'
  simp only [cube, Set.mem_setOf_eq]
  intro i
  have h1 : 0 ≤ (x i - 1) % (k : ℤ) := Int.emod_nonneg _ hne
  have h2 : (x i - 1) % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos _ hk'
  have hval : (x - (k : ℤ) • macroIdx k x) i = (x i - 1) % (k : ℤ) + 1 := by
    have h3 := Int.emod_add_ediv_mul (x i - 1) (k : ℤ)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, macroIdx]
    linarith
  rw [hval]
  omega

theorem mem_cube_of_macroIdx {d : ℕ} (k : ℕ) (hk : 1 ≤ k) (x : Site d) :
    x - (k : ℤ) • macroIdx k x ∈ cube d k := by
  exact aux_mem_cube_of_macroIdx k hk x


theorem aux_ediv_le_of_lt_mul (A B n : ℤ) (hB : 0 < B) (h : A < (n + 1) * B) :
    A / B ≤ n := by
  refine Int.le_of_lt_add_one ?_
  rwa [Int.ediv_lt_iff_lt_mul hB]

theorem aux_nbrSumZ_const (d : ℕ) (n : ℤ) (x : Site d) :
    nbrSumZ (fun _ : Site d => n) x = 2 * (d : ℤ) * n := by
  simp only [nbrSumZ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem aux_pub_reach_wave_le_n {d : ℕ} (η : Site d → ℤ)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (n : ℕ) (z : Site d) (t : ℕ) (x : Site d) :
    wave η n z t x ≤ (n : ℤ) := by
  induction t generalizing x with
  | zero =>
    rw [wave_zero]
    by_cases h : x = z
    · rw [if_pos h]
    · rw [if_neg h]
      exact Int.natCast_nonneg n
  | succ t ih =>
    rw [wave_succ]
    by_cases h : x = z
    · rw [if_pos h]
    · rw [if_neg h]
      by_cases hdpos : (0 : ℤ) < 2 * (d : ℤ)
      · refine aux_ediv_le_of_lt_mul (nbrSumZ (wave η n z t) x + η x) (2 * (d : ℤ)) n hdpos ?_
        have h1 := nbrSumZ_mono (fun y => ih y) x
        have h3 := aux_nbrSumZ_const d (n : ℤ) x
        have h2 := hhigh x
        nlinarith [h1, h2, h3]
      · rw [not_lt] at hdpos
        have hd0 : 2 * (d : ℤ) = 0 := le_antisymm hdpos (by positivity)
        rw [hd0, Int.ediv_zero]
        exact Int.natCast_nonneg n


end Exploding
