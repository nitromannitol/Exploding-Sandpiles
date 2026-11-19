import Exploding.Support.PenultimateCloseUnconditional
import Exploding.Support.ApproximateSubadditiveUnconditional

/-!
# Last-wave convergence inputs

The probabilistic inputs for last-wave convergence follow from the
high-density chemical-distance estimate.
-/

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory
open scoped BigOperators Classical Topology

namespace Exploding

variable {d : ℕ}

/-- Penultimate-cluster arrival times are almost surely finite. -/
theorem lwc_good_event_2_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤ := by
  obtain ⟨γ, hγ, hclose⟩ := Exploding.last_penultimate_close_unconditional d hd p hp hp1.le
  filter_upwards [hclose] with η hη x
  obtain ⟨n0, hn0⟩ := hη
  obtain ⟨_, b, _, hb, _⟩ := (hn0 (max n0 (mnorm x).toNat) (le_max_left _ _) x (by omega)).2
  rw [hb]; exact ENat.natCast_ne_top b

/-- A shift-invariant event carries finite wave thresholds and arrival times. -/
theorem lwc_good_event_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ E : Set (Site d → ℤ), MeasurableSet E ∧ toyLaw d p Eᶜ = 0 ∧
      (∀ v : Site d, ∀ η ∈ E, (fun z => η (v + z)) ∈ E) ∧
      ∀ η ∈ E, (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) ∧
        (∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y) ∧
        ∀ a b : Site d, clusterArrival η a b ≠ ⊤ := by
  set Q : (Site d → ℤ) → Prop := fun η => (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) ∧
    (∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)) ∧
    (∀ x, clusterArrival η (0 : Site d) x ≠ ⊤) with hQdef
  have hQae : ∀ᵐ η ∂(toyLaw d p), Q η := by
    filter_upwards [lwc_good_event_1 d p hp hp1,
      Exploding.finite_exploding_unconditional d hd p hp hp1.le,
      lwc_good_event_2_unconditional d hd p hp hp1] with η h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨E0, hE0meas, hE0full, hE0Q⟩ := lwc_good_event_3 p Q hQae
  have hshiftmeas : ∀ v : Site d, Measurable (fun η : Site d → ℤ => fun z => η (v + z)) :=
    fun v => Measurable.of_eval (fun z => measurable_pi_apply (v + z))
  have hshiftmp : ∀ v : Site d, MeasurePreserving (fun η : Site d → ℤ => fun z => η (v + z))
      (toyLaw d p) (toyLaw d p) := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · have hid : (fun η : Site d → ℤ => fun z => η ((0 : Site d) + z)) = id := by
        funext η; funext z; simp
      rw [hid]; exact MeasurePreserving.id (toyLaw d p)
    · exact (lwc_shift_ergodic d p hp hp1 v hv).toMeasurePreserving
  obtain ⟨E, hEmeas, hEfull, hEshift, hEmemQ⟩ :=
    lwc_good_event_4 d p hp hp1 E0 hE0meas hE0full hshiftmeas hshiftmp
  refine ⟨E, hEmeas, hEfull, hEshift, ?_⟩
  intro η hη
  have hQ0 : Q η := by
    have h0 := hE0Q _ (hEmemQ η hη 0)
    have hid : (fun z : Site d => η ((0 : Site d) + z)) = η := by funext z; simp
    rwa [hid] at h0
  refine ⟨hQ0.1, fun y => ?_, fun a b => ?_⟩
  · obtain ⟨n, hn1, hnstab⟩ := (hE0Q _ (hEmemQ η hη y)).2.1
    refine ⟨n, hn1, fun hcon => hnstab ?_⟩
    have hiff := lwc_waveStabilizable_shift η y n (0 : Site d)
    rw [add_zero] at hiff
    exact hiff.mpr hcon
  · have hfin := (hE0Q _ (hEmemQ η hη a)).2.2 (b - a)
    have heq := lwc_cluster_shift d η a (0 : Site d) (b - a)
    rw [add_zero, show a + (b - a) = b from by abel] at heq
    rwa [heq] at hfin

/-- Penultimate-cluster arrival times satisfy a linear upper bound. -/
theorem lwc_cluster_lipschitz_1_2_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x : Site d, mnorm x ≤ (n:ℤ) → ∃ a : ℕ, clusterArrival η (0:Site d) x = (a:ℕ∞) ∧
        (a:ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ := by
  obtain ⟨γ1, C, hγ1, hC, hub⟩ :=
    Exploding.penultimate_upper_bound_unconditional d hd p hp hp1.le
  obtain ⟨γ2, hγ2, hclose⟩ :=
    Exploding.last_penultimate_close_unconditional d hd p hp hp1.le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (lwc_cluster_lipschitz_1_1 γ1 γ2)
  refine ⟨max γ1 γ2 + 1, C, by positivity, hC, ?_⟩
  filter_upwards [hub, hclose] with η hηub hηclose
  obtain ⟨n0, hn0⟩ := hηub
  obtain ⟨n0', hn0'⟩ := hηclose
  refine ⟨max (max n0 n0') N, fun n hn x hx => ?_⟩
  obtain ⟨m, hma, hmb⟩ := hn0 n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn) x hx
  obtain ⟨_, a, b, hla, hcb, hab⟩ :=
    hn0' n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn) x hx
  refine ⟨b, hcb, ?_⟩
  have hae : a = m := by exact_mod_cast hla.symm.trans hma
  rw [hae] at hab
  have hlog := hN n (le_trans (le_max_right _ _) hn)
  linarith

/-- Locally uniform convergence transfers from cluster arrivals to last-wave arrivals. -/
theorem lwc_transfer_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (N : (Fin d → ℝ) → ℝ)
    (hunif : ∀ᵐ η ∂(toyLaw d p),
      (∀ x : Site d, clusterArrival η (0 : Site d) x ≠ ⊤) ∧
        ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
            |((clusterArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
              - N y| ≤ ε) :
    ∀ᵐ η ∂(toyLaw d p),
      (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
        ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
            |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
              - N y| ≤ ε := by
  obtain ⟨γ, hγ, hclose⟩ := Exploding.last_penultimate_close_unconditional d hd p hp hp1.le
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

/-- Last-wave arrival times satisfy a Lipschitz bound with a polylogarithmic error. -/
theorem lwcl_lastArrival_lip_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x x' : Site d, mnorm x ≤ (n : ℤ) → mnorm x' ≤ (n : ℤ) →
        ∃ a a' : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
          lastArrival η (0 : Site d) x' = (a' : ℕ∞) ∧
            (a' : ℝ) ≤ (a : ℝ) + C * (mnorm (x - x') : ℝ) + Real.log n ^ γ := by
  obtain ⟨γ6, C6, hγ6, hC6, hub⟩ :=
    Exploding.penultimate_upper_bound_unconditional d hd p hp hp1.le
  obtain ⟨kb, hkb⟩ := Exploding.renormalization_properties_unconditional d hd p hp hp1.le
  obtain ⟨c, Cr, hc, hCr, hae⟩ := hkb (max kb 2) (le_max_left kb 2)
  have hd1 : 1 ≤ d := by omega
  set k : ℕ := max kb 2 with hkdef
  have hk2 : 2 ≤ k := le_max_right _ _
  set Cc : ℕ := ⌈Cr⌉₊ with hCcdef
  set Cn : ℕ := ⌈C6⌉₊ with hCndef
  set K0 : ℕ := k + Cc + Cn + d + 2 with hK0def
  set e0 : ℝ := max (5 / 2) γ6 with he0def
  have he0 : (5 / 2 : ℝ) ≤ e0 := le_max_left _ _
  have hγ6e : γ6 ≤ e0 := le_max_right _ _
  obtain ⟨E, hE⟩ := lwcl_E_le d hd1
  set E1 : ℕ := max E (3 * d + 3) with hE1def
  obtain ⟨nstar, hnstar⟩ := pclose_eventually e0 he0 K0 (E1 + 1)
  have he00 : (0 : ℝ) ≤ e0 * ((E1 + 1 : ℕ) : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  refine ⟨e0 * ((E1 + 1 : ℕ) : ℝ) + 1, max ((k : ℝ) ^ d * Cr) C6, by linarith,
    lt_max_of_lt_right hC6, ?_⟩
  filter_upwards [hae, hub, aux_pub_reach_eta_bounds d p hp hp1,
    Exploding.finite_exploding_unconditional d hd p hp hp1.le] with
    η hη hubη hetabd hexplode
  obtain ⟨Cinf, hCinf, ⟨n0h, hhole⟩, ⟨n0c, hchem⟩, -, -⟩ := hη
  obtain ⟨n06, hn6⟩ := hubη
  have hMmem := Nat.sInf_mem hexplode
  have hS : pub_Setup d η (waveThreshold η (0 : Site d)) k Cinf n0h n0c Cr :=
    { hd := hd
      hlow := fun x => (hetabd x).1
      hhigh := fun x => (hetabd x).2
      hN := hMmem.1
      hns := hMmem.2
      hk := hk2
      hCinf := hCinf
      hhole := hhole
      hCr := hCr
      hchem := fun n hn x hx y hy hxn hfar => by
        obtain ⟨m, hm, -, hm2⟩ := hchem n hn x hx y hy hxn hfar
        exact ⟨m, hm, hm2⟩ }
  refine ⟨max n06 (max n0h (max n0c nstar)), fun n hn x x' hx hx' => ?_⟩
  have hn06 : n06 ≤ n := le_trans (le_max_left _ _) hn
  have hn0h : n0h ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn0c : n0c ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hn
  have hnst : nstar ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hn
  obtain ⟨hn2, hℓ1, hZpow, hsz⟩ := hnstar n hnst
  set Z : ℕ := pcloseZ e0 K0 n with hZdef
  obtain ⟨hK0Z, hhole5, -, hℓ6⟩ := pclose_scale_facts e0 he0 K0 n hℓ1 hn2 γ6 hγ6e
  have hZ2 : 2 ≤ Z := by omega
  have hkZ : k ≤ Z := by omega
  have hCcZ : Cc ≤ Z := by omega
  have hCnZ : Cn ≤ Z := by omega
  have hdZ : d ≤ Z := by omega
  have hZ1 : 1 ≤ Z := by omega
  have hsize : 8 * Z ^ E1 ≤ n := by
    have h1 : Z ^ (E1 + 1) = Z * Z ^ E1 := by ring
    have h2 : 2 * Z ^ E1 ≤ Z ^ (E1 + 1) := by
      rw [h1]; exact Nat.mul_le_mul_right _ hZ2
    omega
  have hholeZ : ∀ y ∈ (cent d (2 * n) : Set (Site d)), y ∉ Cinf →
      (componentIn Cinfᶜ y).Finite ∧ (componentIn Cinfᶜ y).ncard < Z := by
    intro y hy hyC
    obtain ⟨hfin, hcard⟩ := hhole (2 * n) (by omega) y hy hyC
    refine ⟨hfin, ?_⟩
    have h1 : ((componentIn Cinfᶜ y).ncard : ℝ) < (Z : ℝ) := by
      calc ((componentIn Cinfᶜ y).ncard : ℝ) < Real.log (((2 * n : ℕ) : ℝ)) ^ ((5 : ℝ) / 2) :=
          hcard
        _ = Real.log (2 * (n : ℝ)) ^ ((5 : ℝ) / 2) := by push_cast; rfl
        _ ≤ (Z : ℝ) := hhole5
    exact_mod_cast h1
  obtain ⟨a, ha, -⟩ := hn6 n hn06 x hx
  obtain ⟨a', ha', -⟩ := hn6 n hn06 x' hx'
  have hubn : ∀ w : Site d, mnorm w ≤ (n : ℤ) → ∃ m : ℕ, lastArrival η (0 : Site d) w = (m : ℕ∞) ∧
      (m : ℝ) ≤ C6 * (mnorm w : ℝ) + Real.log (n : ℝ) ^ γ6 :=
    fun w hw => hn6 n hn06 w hw
  obtain ⟨τ, hτ1, hτpos, hτle⟩ := lwcl_lip_core hd hS n Z Cc Cn E E1 hZ2 hkZ hCnZ hdZ
    (Nat.le_ceil Cr) (hE Z k Cc hZ2 hkZ hCcZ hdZ) (le_max_left _ _) (le_max_right _ _) hsize
    (by omega) (by omega) hhole5 hholeZ C6 (Real.log (n : ℝ) ^ γ6) hC6.le (Nat.le_ceil C6)
    hℓ6 hubn x x' hx hx' a ha
  refine ⟨a, a', ha, ha', ?_⟩
  have hle : lastArrival η (0 : Site d) x' ≤ (τ : ℕ∞) := lastArrival_le η (0 : Site d) x' τ hτ1 hτpos
  rw [ha'] at hle
  have hle' : a' ≤ τ := by exact_mod_cast hle
  have hleR : (a' : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hle'
  have hZE : (Z : ℝ) ^ E1 ≤ (Z : ℝ) ^ (E1 + 1) :=
    pow_le_pow_right₀ (by exact_mod_cast hZ1) (Nat.le_succ E1)
  linarith

/-- Cluster arrival times satisfy a Lipschitz bound with a polylogarithmic error. -/
theorem lwcl_far_lipschitz_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x x' : Site d, x ∈ cent d n → x' ∈ cent d n →
        |((clusterArrival η (0 : Site d) x).toNat : ℝ) -
          ((clusterArrival η (0 : Site d) x').toNat : ℝ)|
            ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ := by
  obtain ⟨γ1, C, hγ1, hC, hlip⟩ := lwcl_lastArrival_lip_unconditional d hd p hp hp1
  obtain ⟨γ2, hγ2, hclose⟩ := Exploding.last_penultimate_close_unconditional d hd p hp hp1.le
  have hd1 : 1 ≤ d := by omega
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (lwc_cluster_lipschitz_1_1 γ1 γ2)
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
    (lwc_cluster_lipschitz_1_5 d hd1 (max γ1 γ2 + 1) (by positivity))
  filter_upwards [hlip, hclose] with η hl hc
  obtain ⟨n0l, hn0l⟩ := hl
  obtain ⟨n0c, hn0c⟩ := hc
  refine ⟨C, max γ1 γ2 + 1 + 1, hC, by positivity,
    max (max n0l n0c) (max N1 N2), fun n hn x x' hx hx' => ?_⟩
  have hnl : n0l ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnc : n0c ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hdn : n ≤ d * n := Nat.le_mul_of_pos_left n (by omega)
  have hcast : (((d * n : ℕ)) : ℝ) = (d : ℝ) * (n : ℝ) := by push_cast; ring
  have hxM : mnorm x ≤ ((d * n : ℕ) : ℤ) := by
    push_cast; exact lwc_cluster_lipschitz_1_6 d n x hx
  have hx'M : mnorm x' ≤ ((d * n : ℕ) : ℤ) := by
    push_cast; exact lwc_cluster_lipschitz_1_6 d n x' hx'
  obtain ⟨a, a', hax, hax', hab⟩ := hn0l (d * n) (by omega) x x' hxM hx'M
  obtain ⟨a3, a4, ha3, ha4, hab'⟩ := hn0l (d * n) (by omega) x' x hx'M hxM
  obtain ⟨hle1, a1, b1, ha1, hb1, hbb1⟩ := hn0c (d * n) (by omega) x hxM
  obtain ⟨hle2, a2, b2, ha2, hb2, hbb2⟩ := hn0c (d * n) (by omega) x' hx'M
  have huniq : ∀ u v : ℕ, (u : ℕ∞) = (v : ℕ∞) → u = v := fun u v h => by exact_mod_cast h
  have hA : a = a1 := huniq _ _ (hax.symm.trans ha1)
  have hA' : a' = a2 := huniq _ _ (hax'.symm.trans ha2)
  have hA3 : a3 = a2 := huniq _ _ (ha3.symm.trans ha2)
  have hA4 : a4 = a1 := huniq _ _ (ha4.symm.trans ha1)
  have hAR : (a : ℝ) = (a1 : ℝ) := by exact_mod_cast hA
  have hA'R : (a' : ℝ) = (a2 : ℝ) := by exact_mod_cast hA'
  have hA3R : (a3 : ℝ) = (a2 : ℝ) := by exact_mod_cast hA3
  have hA4R : (a4 : ℝ) = (a1 : ℝ) := by exact_mod_cast hA4
  rw [ha1, hb1] at hle1
  rw [ha2, hb2] at hle2
  have hle1R : (a1 : ℝ) ≤ (b1 : ℝ) := by exact_mod_cast (by exact_mod_cast hle1 : a1 ≤ b1)
  have hle2R : (a2 : ℝ) ≤ (b2 : ℝ) := by exact_mod_cast (by exact_mod_cast hle2 : a2 ≤ b2)
  have hsym : mnorm (x' - x) = mnorm (x - x') := pub_mnorm_sub_comm x' x
  rw [hsym] at hab'
  have hlog1 := hN1 (d * n) (by omega)
  have hlog2 := hN2 n hn2
  have hlog3 : Real.log ((d : ℝ) * (n : ℝ)) ^ (max γ1 γ2 + 1) ≤
      Real.log n ^ (max γ1 γ2 + 1 + 1) := hlog2
  rw [hcast] at hlog1 hab hab' hbb1 hbb2
  rw [hb1, hb2, ENat.toNat_natCast, ENat.toNat_natCast]
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The lattice time constant extends to a continuous convex homogeneous function. -/
theorem lwc8_assemble_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
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
  filter_upwards [lwc_good_event_2_unconditional d hd p hp hp1,
    ae_all_iff.mpr hLc] with η hfin hlim
  refine ⟨hfin, fun v => ?_⟩
  rw [hlatt v]
  exact hlim v

/-- The directional limits are subadditive. -/
theorem lwc8_L_subadditive_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (L : Site d → ℝ)
    (hLc : ∀ v : Site d, ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun n : ℕ => ((clusterArrival η 0 ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
        atTop (nhds (L v)))
    (u v : Site d) : L (u + v) ≤ L u + L v := by
  classical
  have : IsProbabilityMeasure (toyLaw d p) := by
    have : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
      lwc_isProbabilityMeasure_chipLaw _ _ p hp.le hp1.le
    change IsProbabilityMeasure
      (Measure.infinitePi (fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p))
    infer_instance
  obtain ⟨E, hEmeas, hEfull, hEshift, hEmem⟩ := lwc_good_event_unconditional d hd p hp hp1
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
        simp only [Set.mem_ofPred_eq, Set.mem_preimage]
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

/-- The directional cocycle satisfies the Lipschitz condition for Kingman’s theorem. -/
theorem king_wire_lip_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (E : Set (Site d → ℤ)) (hEfull : toyLaw d p Eᶜ = 0) (v : Site d) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ n' : ℕ, n ≤ n' →
      n' ≤ 2 * n → lwc8_gv E v η n' ≤ lwc8_gv E v η n + C * ((n' : ℝ) - n) + ε * n := by
  have hEae : ∀ᵐ η ∂(toyLaw d p), η ∈ E := ae_iff.mpr hEfull
  have hfar := lwcl_far_lipschitz_unconditional d hd p hp hp1
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

/-- The directional cocycle has an almost-sure asymptotic limit. -/
theorem king_dir_limit_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1)
    (E : Set (Site d → ℤ)) (hEmeas : MeasurableSet E) (hEfull : toyLaw d p Eᶜ = 0)
    (hEshift : ∀ v, ∀ η ∈ E, (fun z => η (v + z)) ∈ E)
    (hEmem : ∀ η ∈ E, (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) ∧
      (∀ y, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y) ∧
      ∀ a b : Site d, clusterArrival η a b ≠ ⊤)
    (v : Site d) :
    ∃ Lv : ℝ, ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun n : ℕ => lwc8_gv E v η n / (n : ℝ)) atTop (nhds Lv) := by
  classical
  have : IsProbabilityMeasure (toyLaw d p) := by
    have : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
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
      by_cases h : η ∈ E <;> simp only [lwc8_gv, h, ite_true, ite_false]
      · positivity
      · linarith
    have hsub : ∀ m n η, lwc8_gv E v η (m + n)
        ≤ lwc8_gv E v η m
          + lwc8_gv E v ((fun η : Site d → ℤ => fun z => η (v + z))^[m] η) n :=
      lwc8_gv_sub d hd E hEshift hEmem v
    have hlipg := king_wire_lip_unconditional d hd p hp hp1 E hEfull v
    exact king_lipKingman (toyLaw d p) (fun η : Site d → ℤ => fun z => η (v + z)) hT herg
      (fun n η => lwc8_gv E v η n) hsub hnonneg hmeas hlipg


/-- The directional limits are nonnegative, linearly bounded and homogeneous. -/
theorem king_L_data_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1) :
    ∃ L : Site d → ℝ,
      (∀ v : Site d, ∀ᵐ η ∂(toyLaw d p),
        Tendsto (fun n : ℕ => ((clusterArrival η 0 ((n : ℤ) • v)).toNat : ℝ) / (n : ℝ))
          atTop (nhds (L v))) ∧
      (∀ v : Site d, 0 ≤ L v) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ v : Site d, L v ≤ C * (mnorm v : ℝ)) ∧
      (∀ (k : ℕ) (v : Site d), L ((k : ℤ) • v) = (k : ℝ) * L v) := by
  classical
  have : IsProbabilityMeasure (toyLaw d p) := by
    have : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
      lwc_isProbabilityMeasure_chipLaw _ _ p hp.le hp1.le
    change IsProbabilityMeasure
      (Measure.infinitePi (fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p))
    infer_instance
  obtain ⟨E, hEmeas, hEfull, hEshift, hEmem⟩ := lwc_good_event_unconditional d hd p hp hp1
  have hEae : ∀ᵐ η ∂(toyLaw d p), η ∈ E := ae_iff.mpr hEfull
  have hdir : ∀ v : Site d, ∃ Lv : ℝ, ∀ᵐ η ∂(toyLaw d p),
      Tendsto (fun n : ℕ => lwc8_gv E v η n / (n : ℝ)) atTop (nhds Lv) :=
    fun v => king_dir_limit_unconditional d hd p hp hp1 E hEmeas hEfull hEshift hEmem v
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
  obtain ⟨γ, C0, hγ, hC0, hbase⟩ := lwc_cluster_lipschitz_1_2_unconditional d hd p hp hp1
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
        simp only [ENat.toNat_natCast]
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

/-- The cluster arrival times have a continuous convex homogeneous limit. -/
theorem king_hking_unconditional (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1) :
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
    king_L_data_unconditional d hd p hp hp1
  exact lwc8_assemble_unconditional d hd p hp hp1 L hLc hnonneg C hC hbound hhom
    (fun u v => lwc8_L_subadditive_unconditional d hd p hp hp1 L hLc u v)

end Exploding
