/-
Packet LWC-8 (`lwc8_`) — the Kingman conjunct of Proposition 3.1, taking
`mk_kingman_linear` as a hypothesis.

`LWCProof6/7` built the extension `lwc6_infN L` of a subadditive, homogeneous,
linearly bounded lattice bound `L`, and identified it with `L` on lattice points.
This file applies `mk_kingman_linear` to the per-direction penultimate-cluster
arrival cocycle over the shift by a lattice vector, produces the limit `L`, proves
its subadditivity/nonnegativity/bound, and assembles the conclusion.
-/
import Exploding.Support.LWCProof7
import Exploding.Support.MKingman

open Exploding LatticeProb MeasureTheory Filter
open scoped BigOperators
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- The per-direction cocycle, zero off the good event. -/
noncomputable def lwc8_gv (E : Set (Site d → ℤ)) (v : Site d) (η : Site d → ℤ) (n : ℕ) : ℝ :=
  if η ∈ E then ((clusterArrival η 0 ((n : ℤ) • v)).toNat : ℝ) else 0

/-- `(m • v) + v = (m+1) • v`. -/
theorem lwc8_smul_add_one (v : Site d) (m : ℕ) :
    (m : ℤ) • v + v = (((m + 1 : ℕ) : ℤ)) • v := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The `m`-fold shift by `v` is the shift by `m • v`. -/
theorem lwc8_shift_iterate (v : Site d) (m : ℕ) (η : Site d → ℤ) :
    (fun η : Site d → ℤ => fun z => η (v + z))^[m] η = fun z => η ((m : ℤ) • v + z) := by
  induction m with
  | zero => funext z; simp
  | succ m ih =>
      funext z
      rw [Function.iterate_succ_apply', ih]
      show η ((m : ℤ) • v + (v + z)) = η (((m + 1 : ℕ) : ℤ) • v + z)
      congr 1
      calc (m : ℤ) • v + (v + z) = ((m : ℤ) • v + v) + z := by abel
        _ = (((m + 1 : ℕ) : ℤ)) • v + z := by rw [lwc8_smul_add_one]

/-- On the good event the cocycle reads off the penultimate-cluster arrival. -/
theorem lwc8_gv_of_mem {E : Set (Site d → ℤ)} {v : Site d} {η : Site d → ℤ} (hη : η ∈ E)
    (n : ℕ) : lwc8_gv E v η n = ((clusterArrival η 0 ((n : ℤ) • v)).toNat : ℝ) := by
  simp [lwc8_gv, hη]

end Exploding

namespace Exploding

variable {d : ℕ}

/-- The per-direction cocycle is linearly bounded. -/
theorem lwc8_gv_linear (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (E : Set (Site d → ℤ)) (hEfull : toyLaw d p Eᶜ = 0)
    (v : Site d) :
    ∃ C : ℝ, ∀ᵐ η ∂(toyLaw d p), ∃ K : ℝ, ∀ n : ℕ,
      lwc8_gv E v η n ≤ C * n + K := by
  classical
  have hEae : ∀ᵐ η ∂(toyLaw d p), η ∈ E := ae_iff.mpr hEfull
  by_cases hv : v = 0
  · subst hv
    refine ⟨1, ?_⟩
    filter_upwards [hEae] with η hη
    refine ⟨(lwc8_gv E 0 η 0 : ℝ) + 1, fun n => ?_⟩
    have hz : lwc8_gv E 0 η n = lwc8_gv E 0 η 0 := by
      by_cases h : η ∈ E <;> simp [lwc8_gv, h]
    rw [hz]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · obtain ⟨γ, C0, hγ, hC0, hbase⟩ :=
      lwc_cluster_lipschitz_1_2 d hd p hp hp1 hLSSB hHole hChem
    set M : ℕ := (mnorm v).toNat + 1 with hM
    have hMpos : 0 < M := by omega
    have hlog : ∀ᶠ n : ℕ in atTop, Real.log ((M : ℝ) * n) ^ γ ≤ n := by
      have h0 : ∀ᶠ n : ℕ in atTop, Real.log ((M : ℝ) * n) ^ γ / (n : ℝ) ≤ 1 :=
        (lwc_transfer_4 γ M hMpos).eventually_le_const (by norm_num : (0 : ℝ) < 1)
      filter_upwards [h0, eventually_gt_atTop 0] with n hn hnpos
      rw [div_le_iff₀ (by exact_mod_cast hnpos)] at hn
      linarith
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hlog
    refine ⟨C0 * (mnorm v : ℝ) + 1, ?_⟩
    filter_upwards [hEae, hbase] with η hηE hbaseη
    obtain ⟨n0, hn0⟩ := hbaseη
    set B : ℕ := max (max n0 N2) 1 with hB
    set gfun : ℕ → ℝ := fun i => lwc8_gv E v η i + Real.log ((M : ℝ) * ((i : ℝ) + 1)) ^ γ
      with hgfun
    have hlogM : ∀ i : ℕ, 0 ≤ Real.log ((M : ℝ) * ((i : ℝ) + 1)) ^ γ := by
      intro i
      apply Real.rpow_nonneg
      apply Real.log_nonneg
      have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
      have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      nlinarith [hM1, hi]
    have hgnonneg : ∀ i, 0 ≤ gfun i := by
      intro i
      rw [hgfun]
      refine add_nonneg ?_ (hlogM i)
      rw [lwc8_gv]
      split <;> positivity
    refine ⟨∑ i ∈ Finset.range B, gfun i + 1, fun n => ?_⟩
    by_cases hnB : n < B
    · have hle : lwc8_gv E v η n ≤ ∑ i ∈ Finset.range B, gfun i + 1 := by
        have hmem : n ∈ Finset.range B := Finset.mem_range.mpr hnB
        have h1 : lwc8_gv E v η n ≤ gfun n := by
          rw [hgfun]; exact le_add_of_nonneg_right (hlogM n)
        have h2 : gfun n ≤ ∑ i ∈ Finset.range B, gfun i :=
          Finset.single_le_sum (fun i _ => hgnonneg i) hmem
        linarith
      have hCnn : 0 ≤ (C0 * (mnorm v : ℝ) + 1) * n :=
        mul_nonneg (by
          have hmv : (0 : ℝ) ≤ (mnorm v : ℝ) := by exact_mod_cast pub_mnorm_nonneg v
          nlinarith [hC0.le, hmv]) (Nat.cast_nonneg n)
      linarith
    · have hB_le : B ≤ n := le_of_not_gt hnB
      have hn0' : n0 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB_le
      have hN2' : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB_le
      have hx : mnorm ((n : ℤ) • v) ≤ ((n * M : ℕ) : ℤ) := by
        rw [lwc2_mnorm_nat_smul]
        have hMZ : mnorm v ≤ (M : ℤ) := by
          rw [hM]; push_cast; omega
        calc (n : ℤ) * mnorm v ≤ (n : ℤ) * M :=
              mul_le_mul_of_nonneg_left hMZ (Int.natCast_nonneg n)
          _ = ((n * M : ℕ) : ℤ) := by push_cast; ring
      have hNn0 : n0 ≤ n * M := by
        have h2 : n ≤ n * M := by
          rw [mul_comm n M]
          exact Nat.le_mul_of_pos_left n hMpos
        exact le_trans hn0' h2
      obtain ⟨a, ha, hbound⟩ := hn0 (n * M) hNn0 ((n : ℤ) • v) hx
      have hlog' : Real.log ((n : ℝ) * M) ^ γ ≤ n := by
        rw [mul_comm (n : ℝ) (M : ℝ)]
        exact hN2 n hN2'
      have hmnorm : (mnorm ((n : ℤ) • v) : ℝ) = (mnorm v : ℝ) * n := by
        rw [lwc2_mnorm_nat_smul]; push_cast; ring
      have hKnonneg : 0 ≤ ∑ i ∈ Finset.range B, gfun i + 1 := by
        have : 0 ≤ ∑ i ∈ Finset.range B, gfun i := Finset.sum_nonneg fun i _ => hgnonneg i
        linarith
      rw [lwc8_gv_of_mem hηE]
      rw [ha]
      simp only [ENat.toNat_coe]
      rw [hmnorm] at hbound
      push_cast at hbound
      nlinarith [hbound, hlog', hKnonneg]

end Exploding

namespace Exploding

variable {d : ℕ}

/-- On the good event the `m`-fold shift stays in the good event. -/
theorem lwc8_shift_mem {E : Set (Site d → ℤ)} (hEshift : ∀ v, ∀ η ∈ E, (fun z => η (v + z)) ∈ E)
    (v : Site d) (m : ℕ) {η : Site d → ℤ} (hη : η ∈ E) :
    (fun η : Site d → ℤ => fun z => η (v + z))^[m] η ∈ E := by
  rw [lwc8_shift_iterate]
  exact hEshift ((m : ℤ) • v) η hη

/-- Off the good event the `m`-fold shift stays off it. -/
theorem lwc8_shift_notMem {E : Set (Site d → ℤ)} (hEshift : ∀ v, ∀ η ∈ E, (fun z => η (v + z)) ∈ E)
    (v : Site d) (m : ℕ) {η : Site d → ℤ} (hη : η ∉ E) :
    (fun η : Site d → ℤ => fun z => η (v + z))^[m] η ∉ E := by
  intro h
  apply hη
  rw [lwc8_shift_iterate] at h
  have h2 := hEshift (-((m : ℤ) • v)) (fun z => η ((m : ℤ) • v + z)) h
  simpa [Function.comp_def, add_assoc] using h2

/-- The per-direction cocycle is subadditive along the shift. -/
theorem lwc8_gv_sub (d : ℕ) (hd : 2 ≤ d) (E : Set (Site d → ℤ))
    (hEshift : ∀ v, ∀ η ∈ E, (fun z => η (v + z)) ∈ E)
    (hEmem : ∀ η ∈ E, (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) ∧
      (∀ y, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y) ∧
      ∀ a b : Site d, clusterArrival η a b ≠ ⊤)
    (v : Site d) (m n : ℕ) (η : Site d → ℤ) :
    lwc8_gv E v η (m + n)
      ≤ lwc8_gv E v η m
        + lwc8_gv E v ((fun η : Site d → ℤ => fun z => η (v + z))^[m] η) n := by
  classical
  by_cases hη : η ∈ E
  · have hηm : (fun η : Site d → ℤ => fun z => η (v + z))^[m] η ∈ E :=
      lwc8_shift_mem hEshift v m hη
    have hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x := fun x => ((hEmem η hη).1 x).1
    have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => ((hEmem η hη).1 x).2
    have hlast : ∀ y, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y := (hEmem η hη).2.1
    have hfin : ∀ a b : Site d, clusterArrival η a b ≠ ⊤ := (hEmem η hη).2.2
    have hfinm : ∀ a b : Site d,
        clusterArrival ((fun η : Site d → ℤ => fun z => η (v + z))^[m] η) a b ≠ ⊤ :=
      (hEmem _ hηm).2.2
    have hineq := Exploding.Frozen.approx_subadditivity d hd η hlow hhigh hlast (0 : Site d)
      ((m : ℤ) • v) ((((m + n : ℕ) : ℤ)) • v)
    have hvadd : ((m : ℤ) • v + (n : ℤ) • v) = (((m + n : ℕ) : ℤ)) • v := by
      rw [← add_smul]; norm_num
    have hshift := lwc_cluster_shift d η ((m : ℤ) • v) 0 ((n : ℤ) • v)
    have hshift' : clusterArrival ((fun η : Site d → ℤ => fun z => η (v + z))^[m] η) 0
          ((n : ℤ) • v)
        = clusterArrival η ((m : ℤ) • v) ((((m + n : ℕ) : ℤ)) • v) := by
      rw [lwc8_shift_iterate, ← hvadd]
      simpa using hshift
    rw [← hshift'] at hineq
    have hfin2 : clusterArrival η 0 ((m : ℤ) • v) ≠ ⊤ := hfin 0 _
    have hfin3 : clusterArrival ((fun η : Site d → ℤ => fun z => η (v + z))^[m] η) 0
        ((n : ℤ) • v) ≠ ⊤ := hfinm 0 _
    have hfin23 : clusterArrival η 0 ((m : ℤ) • v)
        + clusterArrival ((fun η : Site d → ℤ => fun z => η (v + z))^[m] η) 0
          ((n : ℤ) • v) ≠ ⊤ := by
      intro h
      rw [ENat.add_eq_top] at h
      exact h.elim hfin2 hfin3
    have htoNat := ENat.toNat_le_toNat hineq hfin23
    rw [ENat.toNat_add hfin2 hfin3] at htoNat
    have htoNatR : (((clusterArrival η 0 ((((m + n : ℕ) : ℤ)) • v)).toNat : ℝ)
        ≤ ((clusterArrival η 0 ((m : ℤ) • v)).toNat : ℝ)
          + ((clusterArrival ((fun η : Site d → ℤ => fun z => η (v + z))^[m] η) 0
              ((n : ℤ) • v)).toNat : ℝ)) := by
      exact_mod_cast htoNat
    rw [lwc8_gv_of_mem hη (m + n), lwc8_gv_of_mem hη m, lwc8_gv_of_mem hηm n]
    exact htoNatR
  · have hηm : (fun η : Site d → ℤ => fun z => η (v + z))^[m] η ∉ E :=
      lwc8_shift_notMem hEshift v m hη
    simp [lwc8_gv, hη, hηm]

end Exploding

namespace Exploding

variable {d : ℕ}

/-- The per-direction limit of the cocycle, from `mk_kingman_linear`. -/
theorem lwc8_dir_limit (hmk : mk_kingman_linear) (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
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
    have hlin := lwc8_gv_linear d hd p hp hp1 hLSSB hHole hChem E hEfull v
    exact hmk (toyLaw d p) (fun η : Site d → ℤ => fun z => η (v + z)) hT herg
      (fun n η => lwc8_gv E v η n) hsub hnonneg hmeas hlin

end Exploding
