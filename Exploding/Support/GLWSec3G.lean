/-
Proposition 5.1 of the paper (generalized last wave), the Section-3 assembly, part G:
explosion from the last wave, the transfer from the penultimate-cluster arrival times to the
last-wave arrival times, and the assembly of `glw2_Section3Convergence`.
-/
import Exploding.Support.GLWSec3F
import Exploding.Support.ASProof4

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- **Robustness forbids a non-stabilizable centred wave**, for a background with
`0 ≤ η ≤ 2d - 1` (the proof of `as4_hrobust`, which only uses `η ≥ 0`). -/
theorem glws_hrobust (hd : 2 ≤ d) (η : Site d → ℤ)
    (hη0 : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hrob : Robust η) : ∀ n : ℕ, 1 ≤ n → WaveStabilizable η n (0 : Site d) := by
  intro n _hn
  have hdpos : 0 < d := by omega
  -- the finite pile `η + (2dn+1) δ_0` stabilizes by robustness
  obtain ⟨T, hT⟩ := hrob (2 * d * n + 1) (by omega)
  set s0 : Site d → ℤ := fun x => η x + ((2 * d * n + 1 : ℕ) : ℤ) * dirac (0 : Site d) x with hs0
  have hs0eq : s0 = fun x => η x + ((2 * d * n + 1 : ℕ) : ℤ) * dirac (0 : Site d) x := hs0
  set v : Site d → ℤ := podo s0 T with hv
  have hv0nn : ∀ x, 0 ≤ v x := fun x => as_podo_nonneg s0 T x
  have hstable0 : η (0 : Site d) + ((2 * d * n + 1 : ℕ) : ℤ) + lap v (0 : Site d)
      ≤ 2 * (d : ℤ) - 1 := by
    have := glw_wave_to_explosive_pstable s0 T hT 0
    rw [hv]
    simpa [hs0eq] using this
  have hvn : (n : ℤ) ≤ v (0 : Site d) :=
    glw_wave_to_explosive_of_origin_bound η hη0 hdpos n v hv0nn hstable0
  have hstable : ∀ x, x ≠ (0 : Site d) → η x + lap v x ≤ 2 * (d : ℤ) - 1 := by
    intro x hx
    rw [hv]
    have := glw_wave_to_explosive_pstable s0 T hT x
    rwa [show s0 x = η x by simp [hs0eq, dirac_of_ne hx]] at this
  have hdom : ∀ t x, wave η n (0 : Site d) t x ≤ v x :=
    glw_wave_to_explosive_dom η n v hv0nn hvn hstable
  -- the support of `v` is finite (finite speed of toppling)
  have hvsupp : ({x : Site d | 0 < v x}).Finite := by
    have hhigh' : ∀ x, x ≠ 0 → s0 x ≤ 2 * (d : ℤ) - 1 := by
      intro x hx
      rw [hs0eq]
      simp only [dirac_of_ne hx, mul_zero, add_zero]
      exact hhigh x
    have hsub : {x : Site d | 0 < v x} ⊆ {x : Site d | mnorm x ≤ (T : ℤ)} := by
      intro x hx
      rw [hv] at hx
      exact as3_podo_support_le_time s0 hhigh' T x hx
    refine (as_coord_bdd_finite (0 : Site d) (T : ℝ) _ ?_).subset hsub
    intro x hx i
    have h1 : |x i| ≤ mnorm x := abs_coord_le_mnorm x i
    have h2 : mnorm x ≤ (T : ℤ) := hx
    simp only [Pi.zero_apply, sub_zero]
    exact_mod_cast le_trans h1 h2
  -- on the finite support each coordinate stabilizes
  have hstab_each : ∀ x : Site d,
      ∃ Tx : ℕ, ∀ t : ℕ, Tx ≤ t → wave η n (0 : Site d) t x = wave η n (0 : Site d) Tx x := by
    intro x
    by_cases hx : 0 < v x
    · exact as4_mono_bdd_eventually_constant (fun t => wave η n (0 : Site d) t x)
        (fun s t hst => wave_mono_time η hη0 (by
          have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
          linarith) n 0 hst x)
        ⟨v x, fun t => hdom t x⟩
    · have hvx : v x ≤ 0 := le_of_not_gt hx
      have hzero : ∀ t : ℕ, wave η n (0 : Site d) t x = 0 := by
        intro t
        have h1 := hdom t x
        have h2 := wave_nonneg η hη0 n (0 : Site d) t x
        omega
      exact ⟨0, fun t _ => by rw [hzero t, hzero 0]⟩
  choose Tx hTx using hstab_each
  refine ⟨hvsupp.toFinset.sup Tx, fun t ht => ?_⟩
  funext x
  by_cases hx : x ∈ hvsupp.toFinset
  · have h1 : Tx x ≤ t := le_trans (Finset.le_sup (f := Tx) hx) ht
    have h2 : Tx x ≤ hvsupp.toFinset.sup Tx := Finset.le_sup (f := Tx) hx
    rw [hTx x t h1, hTx x (hvsupp.toFinset.sup Tx) h2]
  · have hxsupp : ¬ 0 < v x := fun h => hx (hvsupp.mem_toFinset.mpr h)
    have hvx : v x ≤ 0 := le_of_not_gt hxsupp
    have hzero : ∀ s : ℕ, wave η n (0 : Site d) s x = 0 := by
      intro s
      have h1 := hdom s x
      have h2 := wave_nonneg η hη0 n (0 : Site d) s x
      omega
    rw [hzero t, hzero (hvsupp.toFinset.sup Tx)]


/-- Explosion from a non-stabilizable wave at the origin. -/
theorem glws_explosive (hd : 2 ≤ d) (η : Site d → ℤ) (hη0 : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)) : Explosive η := by
  intro hrob
  obtain ⟨n, hn, hns⟩ := hlast
  exact hns (glws_hrobust hd η hη0 hhigh hrob n hn)

/-- **The closeness of the two arrival times** (Lemma 3.7 in the generalized setting): the
penultimate-cluster arrival time exceeds the last-wave arrival time by at most a power of the
logarithm.  This is the single piece of the Section-3 re-run that the local bound of
`glw2_LipschitzLocal` does not contain. -/
def glws_Close (d : ℕ) (ηmin : ℤ) (P : Measure (Site d → ℤ)) : Prop :=
  IsProbabilityMeasure P → (∀ᵐ η ∂P, InOmega d ηmin η) →
  FiniteRangeOfDependence d P → PathFillingHyp d P → StronglyBoxCrossingHyp d P →
  Exploding.External.LiggettSchonmannStacey →
  Exploding.External.LiggettSchonmannStaceyBoundedDegree →
  Exploding.External.MathieuHoleVolume →
  Exploding.External.AntalPisztoraChemicalDistance →
  ∃ γ : ℝ, 0 < γ ∧ ∀ᵐ η ∂P, ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
    lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
      ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
        clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ

/-- The transfer from `clusterArrival` to `lastArrival`: the proof of `lwc_transfer`, for any
measure on which the closeness holds almost surely. -/
theorem glws_transfer (P : Measure (Site d → ℤ)) (N : (Fin d → ℝ) → ℝ) (γ : ℝ)
    (hclose : ∀ᵐ η ∂P, ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
      lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
        ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
          clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ)
    (hunif : ∀ᵐ η ∂P,
      (∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤) ∧
        ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
            |((clusterArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
              - N y| ≤ ε) :
    ∀ᵐ η ∂P,
      (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
        ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
            |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
              - N y| ≤ ε := by
  filter_upwards [hclose, hunif] with η hηclose hηunif
  refine ⟨lwc_transfer_5 η γ hηclose, fun K hK ε hε => ?_⟩
  obtain ⟨C, hCbd⟩ := lwc_transfer_3 d K hK
  obtain ⟨n0, hn0⟩ := hηclose
  have hCpos : (0 : ℕ) < C + 1 := Nat.succ_pos C
  have htail : ∀ᶠ n : ℕ in atTop, Real.log (((C + 1 : ℕ) : ℝ) * n) ^ γ / (n : ℝ) ≤ ε / 2 :=
    (lwc_transfer_4 γ (C + 1) hCpos).eventually_le_const (by linarith)
  have hev2 : ∀ᶠ n : ℕ in atTop, n0 ≤ (C + 1) * n := by
    have hm : Filter.Tendsto (fun n : ℕ => (C + 1) * n) atTop atTop :=
      Filter.tendsto_atTop_atTop_of_monotone (fun a b hab => Nat.mul_le_mul_left (C+1) hab)
        (fun b => ⟨b, Nat.le_mul_of_pos_left b hCpos⟩)
    exact hm.eventually_ge_atTop n0
  have hev3 := hηunif.2 K hK (ε / 2) (by linarith)
  filter_upwards [htail, hev2, hev3, eventually_ge_atTop 1] with n h1 h2 h3 h4
  intro y hy
  set x : Site d := nearestSite ((n : ℝ) • y) with hxdef
  have hmnorm : mnorm x ≤ ((C + 1 : ℕ) : ℤ) * n := by
    have hcx := hCbd y hy n h4
    have : (C : ℤ) * n ≤ ((C + 1 : ℕ) : ℤ) * n := by push_cast; nlinarith [Int.natCast_nonneg n]
    linarith
  have hbound := lwc_transfer_6 η γ n0 hn0 ((C + 1) * n) h2 x
    (by rw [hxdef]; push_cast; push_cast at hmnorm; linarith)
  have hcast : (((C + 1) * n : ℕ) : ℝ) = ((C + 1 : ℕ) : ℝ) * n := by push_cast; ring
  rw [hcast] at hbound
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h4
  have hstep1 : |((lastArrival η 0 x).toNat : ℝ) / n - ((clusterArrival η 0 x).toNat : ℝ) / n|
      ≤ ε / 2 := by
    rw [div_sub_div_same, abs_div, abs_of_pos hnpos]
    calc |((lastArrival η 0 x).toNat : ℝ) - ((clusterArrival η 0 x).toNat : ℝ)| / n
        ≤ Real.log (((C + 1 : ℕ) : ℝ) * n) ^ γ / n := by gcongr
      _ ≤ ε / 2 := h1
  calc |((lastArrival η 0 x).toNat : ℝ) / n - N y|
      ≤ |((lastArrival η 0 x).toNat : ℝ) / n - ((clusterArrival η 0 x).toNat : ℝ) / n|
          + |((clusterArrival η 0 x).toNat : ℝ) / n - N y| := abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hstep1 (h3 y hy)
    _ = ε := by ring

end Exploding
