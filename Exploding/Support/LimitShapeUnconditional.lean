import Exploding.Support.TimeConstantUnconditional

/-!
# Limit shape of the exploding sandpile

The rescaled toppled region converges in measure to an open convex set.
-/

open Exploding Exploding.LSProof LatticeProb MeasureTheory Filter

/-- The rescaled toppled region converges in measure to a limit shape. -/
theorem Exploding.limit_shape_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ B : Set (Fin d → ℝ),
      Convex ℝ B ∧ IsOpen B ∧ B.Nonempty ∧
      ∀ᵐ η ∂(toyLaw d p),
        Tendsto
          (fun t : ℕ =>
            volume (symmDiff
              {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} B))
          atTop (nhds 0) := by
  obtain ⟨N, hcont, hconv, hhom, hae⟩ :=
    Exploding.convergence_of_time_constant_unconditional d hd p hp hp1
  by_cases hμ : toyLaw d p = 0
  · exact ⟨Set.univ, convex_univ, isOpen_univ, Set.univ_nonempty, by simp [hμ]⟩
  · have : NeBot (ae (toyLaw d p)) := ae_neBot.mpr hμ
    obtain ⟨η₀, hη₀, hη₀ub⟩ := (hae.and (ls_toyLaw_upper_ae d hd p hp hp1)).exists
    have hlb : ∀ y : Fin d → ℝ, ∑ i, |y i| ≤ N y :=
      fun y => ls_N_lower_bound η₀ N hη₀ub hη₀.2.1 hη₀.2.2 y
    obtain ⟨hBconv, hBopen, hBne, hBfront⟩ := ls_B_domain N hcont hconv hhom hlb
    refine ⟨{y : Fin d → ℝ | N y < 1}, hBconv, hBopen, hBne, ?_⟩
    filter_upwards [hae, ls_toyLaw_upper_ae d hd p hp hp1] with η hη hηub
    exact ls_measure_convergence η N hη.2.1 hlb
      (fun K hK ε hε => ls_shell_inclusion η N hη.2.1 hη.2.2 K hK ε hε) hBfront
      hBopen hhom hηub
