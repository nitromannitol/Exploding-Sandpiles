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

end Exploding

namespace Exploding

variable {d : ℕ}

/-- The deterministic limit shape `N` assembled from a lattice limit `L` and the extension. -/
theorem lwc8_assemble (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (L : Site d → ℝ)
    (hLc : ∀ v : Site d, ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun n : ℕ => ((clusterArrival η 0 ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
        atTop (nhds (L v)))
    (hnonneg : ∀ v, 0 ≤ L v)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, L v ≤ C * (mnorm v : ℝ))
    (hhom : ∀ (k : ℕ) (v : Site d), L ((k : ℤ) • v) = (k : ℝ) * L v)
    (hsub : ∀ u v, L (u + v) ≤ L u + L v) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧ ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        (∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤) ∧
        ∀ v : Site d,
          Tendsto (fun n : ℕ =>
              ((clusterArrival η (0 : Site d) ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
            atTop (nhds (N (lwc2_toReal v))) := by
  obtain ⟨hcont, hconv, hsmul, hlatt⟩ :=
    lwc7_extend_exists (L := L) hsub hhom hnonneg C hC hbound (by omega)
  refine ⟨lwc6_infN L, hcont, hconv, hsmul, ?_⟩
  filter_upwards [lwc_good_event_2 d hd p hp hp1 hLSSB hHole hChem,
    ae_all_iff.mpr hLc] with η hfin hlim
  refine ⟨hfin, fun v => ?_⟩
  rw [hlatt v]
  exact hlim v

end Exploding

namespace Exploding

variable {d : ℕ}

end Exploding

namespace Exploding

variable {d : ℕ}

open MeasureTheory

/-- **Subadditivity of the limit shape.**  The intermediate term
`T̃(nu, n(u+v))/n` is equidistributed with `T̃(0, nv)/n`, hence converges in probability to
`L v`; along a subsequence where it converges almost surely, the microscopic subadditivity
gives `L (u+v) ≤ L u + L v`. -/
theorem lwc8_L_subadditive (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (L : Site d → ℝ)
    (hLc : ∀ v : Site d, ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun n : ℕ => ((clusterArrival η 0 ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
        atTop (nhds (L v)))
    (u v : Site d) : L (u + v) ≤ L u + L v := by
  classical
  haveI : IsProbabilityMeasure (toyLaw d p) := by
    haveI : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
      lwc_isProbabilityMeasure_chipLaw _ _ p hp.le hp1.le
    change IsProbabilityMeasure
      (Measure.infinitePi (fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p))
    infer_instance
  obtain ⟨E, hEmeas, hEfull, hEshift, hEmem⟩ := lwc_good_event d hd p hp hp1 hLSSB hHole hChem
  have hEae : ∀ᵐ η ∂(toyLaw d p), η ∈ E := ae_iff.mpr hEfull
  let T : (Site d → ℤ) → (Site d → ℤ) := fun η => fun z => η (u + z)
  have hT : MeasurePreserving T (toyLaw d p) (toyLaw d p) := by
    rcases eq_or_ne u 0 with rfl | hu
    · have hid : T = id := by funext η z; simp [T]
      rw [hid]; exact MeasurePreserving.id _
    · exact (lwc_shift_ergodic d p hp hp1 u hu).toMeasurePreserving
  let X : ℕ → (Site d → ℤ) → ℝ := fun n η =>
    ((clusterArrival η ((n : ℤ) • u) ((n : ℤ) • (u + v))).toNat : ℝ) / (n : ℝ)
  let Y : ℕ → (Site d → ℤ) → ℝ := fun n η =>
    ((clusterArrival η 0 ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ)
  have hXY : ∀ n η, X n η = Y n (T^[n] η) := by
    intro n η
    simp only [X, Y]
    congr 1
    rw [show T^[n] η = fun z => η ((n : ℤ) • u + z) from lwc8_shift_iterate u n η]
    rw [lwc_cluster_shift d η ((n : ℤ) • u) 0 ((n : ℤ) • v), add_zero]
    congr 1
    rw [← smul_add]
  have hYmeas : ∀ n, Measurable (Y n) := fun n => (lwc_measurable d 0 ((n : ℤ) • v)).div_const n
  have hY_im : TendstoInMeasure (toyLaw d p) Y atTop (fun _ => L v) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hYmeas n).aestronglyMeasurable) (hLc v)
  have hX_im : TendstoInMeasure (toyLaw d p) X atTop (fun _ => L v) := by
    rw [tendstoInMeasure_iff_norm] at hY_im ⊢
    intro ε hε
    have heq : ∀ n, (toyLaw d p) {x | ε ≤ ‖X n x - L v‖}
        = (toyLaw d p) {x | ε ≤ ‖Y n x - L v‖} := by
      intro n
      have hmp := hT.iterate n
      have hset : {x | ε ≤ ‖X n x - L v‖} = (T^[n]) ⁻¹' {y | ε ≤ ‖Y n y - L v‖} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [hXY n x]
      have hmeas : MeasurableSet {y : Site d → ℤ | ε ≤ ‖Y n y - L v‖} :=
        measurableSet_le measurable_const (((hYmeas n).sub measurable_const).norm)
      rw [hset, hmp.measure_preimage hmeas.nullMeasurableSet]
    simp_rw [heq]
    exact hY_im ε hε
  obtain ⟨ns, hns, hns_ae⟩ := hX_im.exists_seq_tendsto_ae
  have hns_tendsto : Tendsto ns atTop atTop := hns.tendsto_atTop
  have huv_ae : ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun i : ℕ =>
        ((clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • (u + v))).toNat : ℝ) / (ns i : ℝ))
        atTop (nhds (L (u + v))) :=
    (hLc (u + v)).mono fun η hη => hη.comp hns_tendsto
  have hu_ae : ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun i : ℕ =>
        ((clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • u)).toNat : ℝ) / (ns i : ℝ))
        atTop (nhds (L u)) :=
    (hLc u).mono fun η hη => hη.comp hns_tendsto
  have hineq_ae : ∀ᵐ η ∂(toyLaw d p), ∀ᶠ i : ℕ in atTop,
      ((clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • (u + v))).toNat : ℝ) / (ns i : ℝ)
        ≤ ((clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • u)).toNat : ℝ) / (ns i : ℝ)
          + X (ns i) η := by
    filter_upwards [hEae] with η hηE
    have hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x := fun x => ((hEmem η hηE).1 x).1
    have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => ((hEmem η hηE).1 x).2
    have hlast : ∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y := (hEmem η hηE).2.1
    have hfin : ∀ a b : Site d, clusterArrival η a b ≠ ⊤ := (hEmem η hηE).2.2
    filter_upwards [hns_tendsto.eventually_ge_atTop 1] with i hi
    have h := Exploding.Frozen.approx_subadditivity d hd η hlow hhigh hlast (0 : Site d)
      (((ns i : ℕ) : ℤ) • u) ((((ns i : ℕ) : ℤ)) • (u + v))
    have hfin2 : clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • u) ≠ ⊤ := hfin 0 _
    have hfin3 : clusterArrival η ((((ns i : ℕ) : ℤ)) • u) ((((ns i : ℕ) : ℤ)) • (u + v)) ≠ ⊤ :=
      hfin _ _
    have hsum : clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • u)
        + clusterArrival η ((((ns i : ℕ) : ℤ)) • u) ((((ns i : ℕ) : ℤ)) • (u + v)) ≠ ⊤ := by
      intro hc
      rw [ENat.add_eq_top] at hc
      exact hc.elim hfin2 hfin3
    have htoNat := ENat.toNat_le_toNat h hsum
    rw [ENat.toNat_add hfin2 hfin3] at htoNat
    have htoNatR : (((clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • (u + v))).toNat : ℝ)
        ≤ ((clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • u)).toNat : ℝ)
          + ((clusterArrival η ((((ns i : ℕ) : ℤ)) • u)
              ((((ns i : ℕ) : ℤ)) • (u + v))).toNat : ℝ)) := by
      exact_mod_cast htoNat
    have hpos : (0 : ℝ) < (ns i : ℝ) := by exact_mod_cast hi
    have := div_le_div_of_nonneg_right htoNatR hpos.le
    rw [add_div] at this
    exact this
  obtain ⟨η, huv, hu, hxv, hineq⟩ :=
    (huv_ae.and (hu_ae.and (hns_ae.and hineq_ae))).exists
  have hZ : Tendsto (fun i : ℕ =>
      ((clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • (u + v))).toNat : ℝ) / (ns i : ℝ)
        - ((clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • u)).toNat : ℝ) / (ns i : ℝ))
      atTop (nhds (L (u + v) - L u)) := huv.sub hu
  have hW : Tendsto (fun i : ℕ => X (ns i) η) atTop (nhds (L v)) := hxv
  have hineq' : ∀ᶠ i : ℕ in atTop,
      ((clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • (u + v))).toNat : ℝ) / (ns i : ℝ)
        - ((clusterArrival η 0 ((((ns i : ℕ) : ℤ)) • u)).toNat : ℝ) / (ns i : ℝ)
        ≤ X (ns i) η := by
    filter_upwards [hineq] with i hi
    linarith
  have := le_of_tendsto_of_tendsto hZ hW hineq'
  linarith

end Exploding

namespace Exploding

variable {d : ℕ}

end Exploding
