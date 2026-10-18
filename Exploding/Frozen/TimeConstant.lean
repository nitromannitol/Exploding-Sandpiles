/-
Theorem 1.3 of the paper: the rescaled arrival times of the exploding sandpile
converge locally uniformly to a continuous, convex, one-homogeneous function.
-/
import Exploding.Support.Vocab
import Exploding.External.FeyLevinePeres
import Exploding.Frozen.LastWaveConvergence
import Exploding.Frozen.ApproximateSubadditive
import Exploding.Support.Gen
import Exploding.Support.TimeConstantP1
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory Filter

/-- **Theorem 1.3** (`exploding-corrected-arxiv.tex:117-120`, label `theorem:convergence_of_time_constant`).

"Let `η` be as in (1.2) and let `T_η(x) := min{t ≥ 1 : v_t(x) > 0}`.  On an event
of probability 1, the rescaled arrival times `T̄_η(x) := n^{-1} T_η([n x])`
converge locally uniformly to `N_p`, a continuous, convex, one-homogeneous
function on `ℝ^d`."

`T_η` is `Exploding.arrival`, the arrival time of the parallel toppling odometer
for `η + M_η δ₀`, taken in `ℕ∞`; the almost-sure event asserts that it is finite
at every site, so that reading it as a natural number is not a junk value.
Locally uniform convergence is written in its `ε`-form for the same reason: a
supremum over a compact set would be read through `sSup ∅ = 0`.  `N_p` is
deterministic: it is bound before `η`.

Theorem 1.1 (`hFLP`) and the results the paper cites for Proposition 2.2
(`hLSSB`, `hHole`, `hChem`) enter as explicit hypotheses for the strict branch.
The corrected source specifies the homogeneous law for `0 < p ≤ 1`; at `p = 1`
the ordinary all-high Support theorem supplies the complete conclusion. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.convergence_of_time_constant (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hFLP : Exploding.External.FeyLevinePeresExplosive)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        Explosive η ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) - N y| ≤ ε
-- FROZEN-STATEMENT-END
:= by
  rcases lt_or_eq_of_le hp1 with hp_lt | hp_eq
  ·
    obtain ⟨N, hcont, hconv, hhom, hlast⟩ :=
      Exploding.Frozen.convergence_of_the_last_wave d hd p hp hp_lt.le hLSSB hHole hChem
    have hexp : ∀ᵐ η ∂(toyLaw d p), Explosive η := hFLP d hd p hp hp_lt
    refine ⟨N, hcont, hconv, hhom, ?_⟩
    filter_upwards [hlast, Exploding.Frozen.approximate_subadditive d hd p hp hp_lt.le hLSSB hHole hChem, hexp]
      with η hlastη hsub hηexp
    obtain ⟨hfinL, hloc⟩ := hlastη
    obtain ⟨C1, C2, hC⟩ := hsub
    refine ⟨hηexp, ?_, ?_⟩
    · intro x
      exact ne_top_of_le_ne_top (Gen.add_nat_ne_top (hfinL x) C1) (hC x).1
    · intro K hK ε hε
      obtain ⟨C, hCb⟩ := Gen.exists_nat_bound_of_isCompact hK
      have hε2 : 0 < ε / 2 := by linarith
      have hloc' := hloc K hK (ε / 2) hε2
      rw [Filter.eventually_atTop] at hloc'
      obtain ⟨n1, hn1⟩ := hloc'
      rw [Filter.eventually_atTop]
      refine ⟨max n1 (max (C2 + 1) (max 1 (max (Nat.ceil (2 * (C1 : ℝ) / ε) + 1) (Nat.ceil (2 * (C2 : ℝ) / ε) + 1)))), ?_⟩
      intro n hn y hy
      have hn1' : n1 ≤ n := by omega
      have hn2' : C2 + 1 ≤ n := by omega
      have hn1'' : 1 ≤ n := by omega
      have hnC : 2 * (C1 : ℝ) / ε ≤ (n : ℝ) := by
        have h1 : Nat.ceil (2 * (C1 : ℝ) / ε) ≤ n := by omega
        have h2 : (Nat.ceil (2 * (C1 : ℝ) / ε) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
        have h3 : 2 * (C1 : ℝ) / ε ≤ (Nat.ceil (2 * (C1 : ℝ) / ε) : ℝ) := Nat.le_ceil _
        linarith
      have hnC2 : 2 * (C2 : ℝ) / ε ≤ (n : ℝ) := by
        have h1 : Nat.ceil (2 * (C2 : ℝ) / ε) ≤ n := by omega
        have h2 : (Nat.ceil (2 * (C2 : ℝ) / ε) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
        have h3 : 2 * (C2 : ℝ) / ε ≤ (Nat.ceil (2 * (C2 : ℝ) / ε) : ℝ) := Nat.le_ceil _
        linarith
      have hnpos : 0 < n := hn1''
      have hx : nearestSite ((n : ℝ) • y) ∈ cent d (n * (C + 2)) := by
        intro i
        have h1' := Gen.nearestSite_smul_mem_cent y C n (hCb y hy) i
        have h2' : ((n * (C + 1) + 1 : ℕ) : ℤ) ≤ ((n * (C + 2) : ℕ) : ℤ) := by
          push_cast
          nlinarith [hn1'']
        exact le_trans h1' h2'
      have hA := hn1 n hn1' y hy
      have hB : ((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ)
          ≤ ((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) + (C1 : ℝ) := by
        have h1 := Gen.toNat_le_add (hC (nearestSite ((n : ℝ) • y))).1 (hfinL _)
        exact_mod_cast h1
      have hB2 : ((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ)
          ≤ ((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) + (C2 : ℝ) := by
        have hfinA : arrival η (nearestSite ((n : ℝ) • y)) ≠ ⊤ :=
          ne_top_of_le_ne_top (Gen.add_nat_ne_top (hfinL _) C1) (hC (nearestSite ((n : ℝ) • y))).1
        have h1 := Gen.toNat_le_add (hC (nearestSite ((n : ℝ) • y))).2 hfinA
        exact_mod_cast h1
      have hC' : |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
          - ((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)|
          ≤ ε / 2 := by
        have hfin1 : (C1 : ℝ) ≤ ε / 2 * (n : ℝ) := by
          have h4 : ε * (2 * (C1 : ℝ) / ε) ≤ ε * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hnC (le_of_lt hε)
          rw [mul_div_cancel₀ _ (ne_of_gt hε)] at h4
          linarith
        have hfin2 : (C2 : ℝ) ≤ ε / 2 * (n : ℝ) := by
          have h4 : ε * (2 * (C2 : ℝ) / ε) ≤ ε * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hnC2 (le_of_lt hε)
          rw [mul_div_cancel₀ _ (ne_of_gt hε)] at h4
          linarith
        have h1 : ((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
            - ((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) ≤ ε / 2 := by
          rw [div_sub_div_same]
          rw [div_le_iff₀ (by exact_mod_cast hnpos)]
          nlinarith [hB, hfin1]
        have h2 : ((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
            - ((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) ≤ ε / 2 := by
          rw [div_sub_div_same]
          rw [div_le_iff₀ (by exact_mod_cast hnpos)]
          nlinarith [hB2, hfin2]
        rw [abs_sub_le_iff]
        exact ⟨h1, h2⟩
      have hD : |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
          - ((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)| ≤ ε / 2 := by
        rw [abs_sub_comm]
        exact hC'
      have hD' : |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
          - ((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)| ≤ ε / 2 := by
        rw [abs_sub_comm]; exact hD
      have := Gen.abs_sub_le_of_le _ _ _ _ _ hD' hA
      linarith

  · subst p
    exact Exploding.convergence_of_time_constant_p1 d hd
