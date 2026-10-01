/-
Proposition 3.1's Kingman conjunct, from the Lipschitz-transfer Kingman theorem.

`LWCProof8.lean` derives the lattice limit shape from `mk_kingman_linear`, which is false
(`KingmanBARefute.lean`).  The per-direction cocycle `lwc8_gv` is subadditive along the shift,
nonnegative and measurable, and the far Lipschitz bound `lwcl_far_lipschitz` of the paper
(`eq:lastwave_lipschitz`) is exactly the upward Lipschitz hypothesis of `king_lipKingman`.  So
the per-direction limit exists, and the rest of `LWCProof8` (the lattice data, subadditivity of
the limit by convergence in probability, the extension to a continuous convex one-homogeneous
function) goes through unchanged.  This file reruns the two `LWCProof8` declarations that
consumed `mk_kingman_linear`, with the corrected input, and states the Proposition 3.1 Kingman
conjunct with only the frozen hypotheses.
-/
import Exploding.Support.LWCProof8
import Exploding.Support.LWCLipE
import Exploding.Support.KingmanBALip

open Exploding LatticeProb MeasureTheory Filter
open scoped BigOperators
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- **The Lipschitz hypothesis of `king_lipKingman` for the per-direction cocycle**, from the far
Lipschitz bound of Proposition 3.1 along the ray `n • v` (the box `cent d N` contains `n • v`
as soon as `n * M ≤ N`, with `M = |v| + 1`). -/
theorem king_wire_lip (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (E : Set (Site d → ℤ)) (hEfull : toyLaw d p Eᶜ = 0) (v : Site d) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ n' : ℕ, n ≤ n' →
      n' ≤ 2 * n → lwc8_gv E v η n' ≤ lwc8_gv E v η n + C * ((n' : ℝ) - n) + ε * n := by
  have hEae : ∀ᵐ η ∂(toyLaw d p), η ∈ E := ae_iff.mpr hEfull
  have hfar := lwcl_far_lipschitz d hd p hp hp1 hLSSB hHole hChem
  set M : ℕ := (mnorm v).toNat + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hMZ : mnorm v ≤ (M : ℤ) := by rw [hM]; push_cast; omega
  filter_upwards [hEae, hfar] with η hηE hη
  obtain ⟨C, γ, hC, hγ, n0, hn0⟩ := hη
  refine ⟨C * (mnorm v : ℝ), fun ε hε => ?_⟩
  have hmem : ∀ N k : ℕ, k * M ≤ N → ((k : ℤ) • v) ∈ cent d N := by
    intro N k hk i
    have h1 : |((k : ℤ) • v) i| = (k : ℤ) * |v i| := by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (Int.natCast_nonneg k)]
    rw [h1]
    have h2 : |v i| ≤ (M : ℤ) := le_trans (lwc2_abs_coord_le_mnorm v i) hMZ
    calc (k : ℤ) * |v i| ≤ (k : ℤ) * M := mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg k)
      _ = ((k * M : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (N : ℤ) := by exact_mod_cast hk
  have key := king_lip_of_log (fun n : ℕ => ((clusterArrival η 0 ((n : ℤ) • v)).toNat : ℝ))
    (C * (mnorm v : ℝ)) γ M hM1 n0 (by
      intro N hN n₁ n₂ h12 h2M
      have hx2 := hmem N n₂ h2M
      have hx1 := hmem N n₁ (le_trans (Nat.mul_le_mul_right M h12) h2M)
      have h1 := hn0 N hN ((n₂ : ℤ) • v) ((n₁ : ℤ) • v) hx2 hx1
      have e : (n₂ : ℤ) • v - (n₁ : ℤ) • v = (((n₂ - n₁ : ℕ)) : ℤ) • v := by
        rw [← sub_smul, Nat.cast_sub h12]
      rw [e, lwc2_mnorm_nat_smul] at h1
      have h3 : (((n₂ - n₁ : ℕ) : ℤ) * mnorm v : ℤ) = (((n₂ : ℤ) - n₁) * mnorm v : ℤ) := by
        rw [Nat.cast_sub h12]
      have h4 : (((((n₂ - n₁ : ℕ) : ℤ) * mnorm v : ℤ)) : ℝ)
          = ((n₂ : ℝ) - n₁) * (mnorm v : ℝ) := by
        rw [h3]; push_cast; ring
      rw [h4] at h1
      have := (abs_le.1 h1).2
      nlinarith [this]) ε hε
  filter_upwards [key] with n hn n' hnn' hn'2
  rw [lwc8_gv_of_mem hηE, lwc8_gv_of_mem hηE]
  exact hn n' hnn' hn'2

end Exploding

namespace Exploding

variable {d : ℕ}

/-- The per-direction limit of the cocycle, from the Lipschitz-transfer Kingman theorem and the
far Lipschitz bound. -/
theorem king_dir_limit (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (E : Set (Site d → ℤ)) (hEmeas : MeasurableSet E) (hEfull : toyLaw d p Eᶜ = 0)
    (hEshift : ∀ v, ∀ η ∈ E, (fun z => η (v + z)) ∈ E)
    (hEmem : ∀ η ∈ E, (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) ∧
      (∀ y, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y) ∧
      ∀ a b : Site d, clusterArrival η a b ≠ ⊤)
    (v : Site d) :
    ∃ Lv : ℝ, ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun n : ℕ => lwc8_gv E v η n / (n : ℝ)) atTop (nhds Lv) := by
  classical
  haveI : IsProbabilityMeasure (toyLaw d p) := by
    haveI : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
      lwc_isProbabilityMeasure_chipLaw _ _ p hp.le hp1.le
    change IsProbabilityMeasure
      (Measure.infinitePi (fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p))
    infer_instance
  rcases eq_or_ne v 0 with rfl | hv
  · refine ⟨0, ?_⟩
    filter_upwards with η
    have hz : ∀ n, lwc8_gv E 0 η n = lwc8_gv E 0 η 0 := by
      intro n
      by_cases h : η ∈ E <;> simp [lwc8_gv, h]
    have htend : Tendsto (fun n : ℕ => lwc8_gv E 0 η 0 / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine htend.congr' ?_
    filter_upwards with n
    rw [hz n]
  · have hT : MeasurePreserving (fun η : Site d → ℤ => fun z => η (v + z))
        (toyLaw d p) (toyLaw d p) :=
      (lwc_shift_ergodic d p hp hp1 v hv).toMeasurePreserving
    have herg : Ergodic (fun η : Site d → ℤ => fun z => η (v + z)) (toyLaw d p) :=
      lwc_shift_ergodic d p hp hp1 v hv
    have hmeas : ∀ n, Measurable (fun η : Site d → ℤ => lwc8_gv E v η n) := by
      intro n
      unfold lwc8_gv
      exact Measurable.ite hEmeas (lwc_measurable d 0 ((n : ℤ) • v)) measurable_const
    have hnonneg : ∀ n η, 0 ≤ lwc8_gv E v η n := by
      intro n η
      by_cases h : η ∈ E <;> simp only [lwc8_gv, h, if_true, if_false]
      · positivity
      · linarith
    have hsub : ∀ m n η, lwc8_gv E v η (m + n)
        ≤ lwc8_gv E v η m
          + lwc8_gv E v ((fun η : Site d → ℤ => fun z => η (v + z))^[m] η) n :=
      lwc8_gv_sub d hd E hEshift hEmem v
    have hlipg := king_wire_lip d hd p hp hp1 hLSSB hHole hChem E hEfull v
    exact king_lipKingman (toyLaw d p) (fun η : Site d → ℤ => fun z => η (v + z)) hT herg
      (fun n η => lwc8_gv E v η n) hsub hnonneg hmeas hlipg


end Exploding

namespace Exploding

variable {d : ℕ}

/-- The lattice limit `L` produced by the Lipschitz-transfer Kingman theorem, with nonnegativity, the linear
bound, homogeneity and (below) subadditivity. -/
theorem king_L_data (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ L : Site d → ℝ,
      (∀ v : Site d, ∀ᵐ η ∂(toyLaw d p),
        Tendsto (fun n : ℕ => ((clusterArrival η 0 ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
          atTop (nhds (L v))) ∧
      (∀ v : Site d, 0 ≤ L v) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ v : Site d, L v ≤ C * (mnorm v : ℝ)) ∧
      (∀ (k : ℕ) (v : Site d), L ((k : ℤ) • v) = (k : ℝ) * L v) := by
  classical
  haveI : IsProbabilityMeasure (toyLaw d p) := by
    haveI : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
      lwc_isProbabilityMeasure_chipLaw _ _ p hp.le hp1.le
    change IsProbabilityMeasure
      (Measure.infinitePi (fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p))
    infer_instance
  obtain ⟨E, hEmeas, hEfull, hEshift, hEmem⟩ := lwc_good_event d hd p hp hp1 hLSSB hHole hChem
  have hEae : ∀ᵐ η ∂(toyLaw d p), η ∈ E := ae_iff.mpr hEfull
  have hdir : ∀ v : Site d, ∃ Lv : ℝ, ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun n : ℕ => lwc8_gv E v η n / (n : ℝ)) atTop (nhds Lv) :=
    fun v => king_dir_limit d hd p hp hp1 hLSSB hHole hChem E hEmeas hEfull hEshift hEmem v
  let L : Site d → ℝ := fun v => Classical.choose (hdir v)
  have hL : ∀ v : Site d, ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun n : ℕ => lwc8_gv E v η n / (n : ℝ)) atTop (nhds (L v)) :=
    fun v => Classical.choose_spec (hdir v)
  have hLc : ∀ v : Site d, ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun n : ℕ => ((clusterArrival η 0 ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
        atTop (nhds (L v)) := by
    intro v
    filter_upwards [hL v, hEae] with η hηlim hηE
    refine hηlim.congr' ?_
    filter_upwards with n
    rw [lwc8_gv_of_mem hηE]
  have hL0 : L 0 = 0 := by
    obtain ⟨η, h₁, h₂, hηE⟩ := ((hL 0).and ((lwc_kingman_zero_case d p).and hEae)).exists
    have h₁' : Tendsto (fun n : ℕ =>
        ((clusterArrival η 0 ((n : ℤ) • (0 : Site d))).toNat : ℝ) / (n : ℝ)) atTop (nhds (L 0)) := by
      refine h₁.congr' ?_
      filter_upwards with n
      rw [lwc8_gv_of_mem hηE]
    exact tendsto_nhds_unique h₁' h₂
  have hnonneg : ∀ v : Site d, 0 ≤ L v := by
    intro v
    obtain ⟨η, hηlim⟩ := (hL v).exists
    refine ge_of_tendsto hηlim ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [lwc8_gv]
    split
    · exact div_nonneg (by positivity) (by positivity)
    · simp
  obtain ⟨γ, C0, hγ, hC0, hbase⟩ := lwc_cluster_lipschitz_1_2 d hd p hp hp1 hLSSB hHole hChem
  have hboundone : ∀ v : Site d, L v ≤ C0 * (mnorm v : ℝ) + 1 := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · rw [hL0]; simp [mnorm]
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      have hMpos : 0 < (mnorm v).toNat + 1 := by omega
      have hlog : ∀ᶠ n : ℕ in atTop,
          Real.log ((((mnorm v).toNat + 1 : ℕ) : ℝ) * n) ^ γ / (n : ℝ) ≤ ε :=
        (lwc_transfer_4 γ ((mnorm v).toNat + 1) hMpos).eventually_le_const hε
      obtain ⟨η, hηlim, hηbase, hηE⟩ := ((hL v).and (hbase.and hEae)).exists
      obtain ⟨n0, hn0⟩ := hηbase
      have hev : ∀ᶠ n : ℕ in atTop,
          lwc8_gv E v η n / (n : ℝ) ≤ C0 * (mnorm v : ℝ) + ε := by
        filter_upwards [hlog, eventually_ge_atTop n0, eventually_ge_atTop 1] with n hlog' hn0' hn1
        have hx : mnorm ((n : ℤ) • v) ≤ ((n * ((mnorm v).toNat + 1) : ℕ) : ℤ) := by
          rw [lwc2_mnorm_nat_smul]
          have hMZ : mnorm v ≤ (((mnorm v).toNat + 1 : ℕ) : ℤ) := by
            have h1 : (mnorm v).toNat ≤ (mnorm v).toNat + 1 := Nat.le_succ _
            rw [← Int.toNat_of_nonneg (pub_mnorm_nonneg v)]
            exact_mod_cast h1
          calc (n : ℤ) * mnorm v ≤ (n : ℤ) * (((mnorm v).toNat + 1 : ℕ) : ℤ) :=
                mul_le_mul_of_nonneg_left hMZ (Int.natCast_nonneg n)
            _ = ((n * ((mnorm v).toNat + 1) : ℕ) : ℤ) := by push_cast; ring
        have hNn0 : n0 ≤ n * ((mnorm v).toNat + 1) := by
          have h2 : n ≤ n * ((mnorm v).toNat + 1) := by
            rw [mul_comm n ((mnorm v).toNat + 1)]
            exact Nat.le_mul_of_pos_left n hMpos
          exact le_trans hn0' h2
        obtain ⟨a, ha, hb⟩ := hn0 (n * ((mnorm v).toNat + 1)) hNn0 ((n : ℤ) • v) hx
        rw [lwc8_gv_of_mem hηE, ha]
        simp only [ENat.toNat_coe]
        have hmnorm : (mnorm ((n : ℤ) • v) : ℝ) = (mnorm v : ℝ) * n := by
          rw [lwc2_mnorm_nat_smul]; push_cast; ring
        rw [hmnorm] at hb
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < n)]
        have hlog'' : Real.log (((n * ((mnorm v).toNat + 1) : ℕ) : ℝ)) ^ γ ≤ ε * n := by
          have h := hlog'
          rw [show ((((mnorm v).toNat + 1 : ℕ) : ℝ) * (n : ℝ))
              = (((n * ((mnorm v).toNat + 1) : ℕ) : ℝ)) by push_cast; ring] at h
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < n)] at h
          linarith
        calc (a : ℝ) ≤ C0 * ((mnorm v : ℝ) * n)
              + Real.log (((n * ((mnorm v).toNat + 1) : ℕ) : ℝ)) ^ γ := hb
          _ ≤ C0 * ((mnorm v : ℝ) * n) + ε * n := by linarith [hlog'']
          _ = (C0 * (mnorm v : ℝ) + ε) * n := by ring
      have hconst : Tendsto (fun _ : ℕ => C0 * (mnorm v : ℝ) + ε) atTop
          (nhds (C0 * (mnorm v : ℝ) + ε)) := tendsto_const_nhds
      have := le_of_tendsto_of_tendsto hηlim hconst hev
      linarith
  have hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Site d, L v ≤ C * (mnorm v : ℝ) := by
    refine ⟨C0 + 1, by positivity, fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · rw [hL0]; simp [mnorm]
    · have hmv : (1 : ℝ) ≤ (mnorm v : ℝ) := by
        obtain ⟨i, hi⟩ : ∃ i : Fin d, v i ≠ 0 := by
          by_contra h
          push Not at h
          exact hv (funext h)
        have h1 : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
        have h2 : |v i| ≤ mnorm v := lwc2_abs_coord_le_mnorm v i
        exact_mod_cast le_trans h1 h2
      calc L v ≤ C0 * (mnorm v : ℝ) + 1 := hboundone v
        _ ≤ (C0 + 1) * (mnorm v : ℝ) := by nlinarith [hC0.le, hmv]
  have hhom : ∀ (k : ℕ) (v : Site d), L ((k : ℤ) • v) = (k : ℝ) * L v := by
    intro k v
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [show (((0 : ℕ) : ℤ)) • v = (0 : Site d) by simp, hL0]
      ring
    · exact lwc_homog d p L hLc v k hk
  exact ⟨L, hLc, hnonneg, hbound, hhom⟩

end Exploding

namespace Exploding

variable {d : ℕ}

/-- **Proposition 3.1's Kingman conjunct.**  There is a continuous, convex, one-homogeneous `N`
with almost-sure finiteness of `clusterArrival` and lattice-direction convergence of the rescaled
penultimate-cluster arrival times to `N`.  It uses only the frozen hypotheses of Proposition 3.1,
and (through `king_lipKingman`) not the false `mk_kingman_linear`. -/
theorem king_hking (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧ ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        (∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤) ∧
        ∀ v : Site d,
          Tendsto (fun n : ℕ =>
              ((clusterArrival η (0 : Site d) ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
            atTop (nhds (N (lwc2_toReal v))) := by
  obtain ⟨L, hLc, hnonneg, ⟨C, hC, hbound⟩, hhom⟩ :=
    king_L_data d hd p hp hp1 hLSSB hHole hChem
  exact lwc8_assemble d hd p hp hp1 hLSSB hHole hChem L hLc hnonneg C hC hbound hhom
    (fun u v => lwc8_L_subadditive d hd p hp hp1 hLSSB hHole hChem L hLc u v)

end Exploding
