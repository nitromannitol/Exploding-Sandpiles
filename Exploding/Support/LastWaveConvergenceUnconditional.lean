import Exploding.Support.LastWaveInputsUnconditional

/-!
# Convergence of last-wave arrival times

The rescaled last-wave arrival times converge locally uniformly to a
continuous convex homogeneous function.
-/

open Exploding LatticeProb MeasureTheory Filter

/-- Last-wave arrival times converge locally uniformly. -/
theorem Exploding.convergence_of_the_last_wave_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε
:= by
  rcases lt_or_eq_of_le hp1 with hp_lt | hp_eq
  ·
    obtain ⟨hking, hlip⟩ :
        (∃ N : (Fin d → ℝ) → ℝ,
          Continuous N ∧ ConvexOn ℝ Set.univ N ∧
          (∀ (c : ℝ), 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
          ∀ᵐ η ∂(toyLaw d p),
            (∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤) ∧
            ∀ v : Site d,
              Tendsto (fun n : ℕ =>
                  ((clusterArrival η (0 : Site d) ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
                atTop (nhds (N (lwc2_toReal v))))
        ∧
        (∀ᵐ η ∂(toyLaw d p), ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
          ∀ x x' : Site d, x ∈ cent d n → x' ∈ cent d n →
            |((clusterArrival η (0 : Site d) x).toNat : ℝ) -
              ((clusterArrival η (0 : Site d) x').toNat : ℝ)|
                ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ) :=
      ⟨Exploding.king_hking_unconditional d hd p hp hp_lt,
        Exploding.lwcl_far_lipschitz_unconditional d hd p hp hp_lt⟩
    obtain ⟨N, hcont, hconvex, hhom, hking_ae⟩ := hking
    refine ⟨N, hcont, hconvex, hhom, ?_⟩
    apply lwc_transfer_unconditional d hd p hp hp_lt N
    filter_upwards [hking_ae, hlip] with η hk hl
    obtain ⟨C, γ, hC, hγ, hrest⟩ := hl
    obtain ⟨n0, hn0⟩ := hrest
    exact ⟨hk.1, fun K hK ε hε =>
      lwc3_lattice_upgrade (fun x => ((clusterArrival η (0 : Site d) x).toNat : ℝ)) N (by omega)
        hcont hhom hk.2 C γ hC hγ ⟨n0, hn0⟩ K hK ε hε⟩
  ·
    subst p
    exact Exploding.convergence_of_the_last_wave_p1 d hd
