import Exploding.Support.FiniteExplodingUnconditional

/-!
# Last waves at all sites

Translation invariance transfers almost-sure finiteness of the last wave
from the origin to every lattice site.
-/

open Exploding LatticeProb MeasureTheory

/-- The last wave is almost surely well-defined at every site. -/
theorem Exploding.finite_exploding_at_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n x := by
  have h0 := Exploding.finite_exploding_unconditional d hd p hp hp1.le
  have hshift : ∀ x : Site d, ∀ᵐ η ∂(toyLaw d p),
      ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n x := by
    intro x
    have h1 : ∀ᵐ η ∂((toyLaw d p).map (fun η : Site d → ℤ => fun z => η (z + x))),
        ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d) := by
      rw [toyLaw_shift d p hp hp1 x]
      exact h0
    rw [MeasureTheory.ae_map_iff] at h1
    · rw [MeasureTheory.ae_iff] at h1
      rw [MeasureTheory.ae_iff]
      have h3 : {a : Site d → ℤ | ¬ ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable (fun z => a (z + x)) n (0 : Site d)} =
          {a : Site d → ℤ | ¬ ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable a n x} := by
        ext a
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro hc ⟨n, hn, hns⟩
          refine hc ⟨n, hn, fun hstab => hns ?_⟩
          obtain ⟨T, hT⟩ := hstab
          refine ⟨T, fun t ht => ?_⟩
          funext y
          have h4 := congrFun (hT t ht) (y - x)
          have h5 := wave_shift_eq a n x x t y
          have h6 := wave_shift_eq a n x x T y
          simp only [sub_self] at h5 h6
          rw [h5, h6] at h4
          simpa using h4
        · intro hc ⟨n, hn, hns⟩
          refine hc ⟨n, hn, fun hstab => hns ?_⟩
          obtain ⟨T, hT⟩ := hstab
          refine ⟨T, fun t ht => ?_⟩
          funext y
          have h4 := congrFun (hT t ht) (y + x)
          rw [← wave_shift_eq a n x x t (y + x), ← wave_shift_eq a n x x T (y + x)] at h4
          simpa using h4
      rw [h3] at h1
      exact h1
    · exact (Measurable.of_eval fun z => measurable_pi_apply (z + x)).aemeasurable
    · have h : MeasurableSet (⋃ n : ℕ, {a : Site d → ℤ |
          (1 ≤ n ∧ ¬ WaveStabilizable a n (0 : Site d))}) :=
        MeasurableSet.iUnion fun n =>
          (measurableSet_le (f := fun _ : Site d → ℤ => (1 : ℕ)) measurable_const
            measurable_const).inter (measurableSet_not_stabilizable n (0 : Site d))
      rw [show {a : Site d → ℤ | ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable a n (0 : Site d)} =
          ⋃ n : ℕ, {a : Site d → ℤ | (1 ≤ n ∧ ¬ WaveStabilizable a n (0 : Site d))} from by
        ext a
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]]
      exact h
  exact (MeasureTheory.ae_all_iff).mpr hshift
