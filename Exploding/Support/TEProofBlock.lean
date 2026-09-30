/-
A background with arbitrarily large blocks of sites holding at least `2d` chips is
not stabilizable, and an i.i.d. background with a positive density of such sites has
such blocks almost surely.

In a block of radius `R` around `x₀` on which the initial sandpile is at least `2d`,
the parallel toppling odometer at time `t ≤ R + 1` equals `t` on the block of radius
`R + 1 - t` around `x₀`: the firing of a site is forced while all its neighbours have
fired as often as it has.  Hence the odometer at the centre grows to `R + 1` by time
`R + 1`, while an odometer that is constant from time `T` on is at most `T`.
-/
import Exploding.Support.Toppling
import Exploding.Support.Hypotheses
import Exploding.Support.TEProofLaw

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

theorem te_unit_abs (i j : Fin d) : |(unit i) j| ≤ 1 := by
  by_cases h : j = i
  · subst h; simp [unit]
  · simp [unit, Pi.single_eq_of_ne h]

/-- The parallel toppling odometer at time `t` is at most `t`. -/
theorem te_podo_le_time (s0 : Site d → ℤ) (t : ℕ) (x : Site d) : podo s0 t x ≤ t := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    rw [podo_succ]
    have := ih x
    split_ifs <;> push_cast <;> omega

/-- On a block where the initial sandpile is at least `2d`, the odometer at time `t`
equals `t` on the concentric block of radius `R + 1 - t`. -/
theorem te_podo_block (s0 : Site d → ℤ) (x0 : Site d) (R : ℕ)
    (h : ∀ y : Site d, (∀ j, |y j - x0 j| ≤ (R : ℤ)) → 2 * (d : ℤ) ≤ s0 y) :
    ∀ t : ℕ, t ≤ R + 1 → ∀ z : Site d, (∀ j, |z j - x0 j| ≤ (R : ℤ) + 1 - t) →
      podo s0 t z = t := by
  intro t
  induction t with
  | zero => intro _ z _; simp
  | succ t ih =>
    intro ht z hz
    have ht' : t ≤ R + 1 := by omega
    have hz' : ∀ j, |z j - x0 j| ≤ (R : ℤ) - t := by
      intro j
      have := hz j
      push_cast at this
      linarith
    have hzt : podo s0 t z = t :=
      ih ht' z (fun j => by have := hz' j; linarith)
    have hnb : ∀ w : Site d, (∀ j, |w j - z j| ≤ 1) → podo s0 t w = t := by
      intro w hw
      apply ih ht' w
      intro j
      have h1 := hw j
      have h2 := hz' j
      calc |w j - x0 j| = |(w j - z j) + (z j - x0 j)| := by ring_nf
        _ ≤ |w j - z j| + |z j - x0 j| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hnbr : nbrSumZ (podo s0 t) z = 2 * (d : ℤ) * t := by
      have : ∀ i : Fin d, podo s0 t (z + unit i) + podo s0 t (z - unit i) = 2 * (t : ℤ) := by
        intro i
        have e1 : podo s0 t (z + unit i) = t := hnb _ (fun j => by
          simpa using te_unit_abs i j)
        have e2 : podo s0 t (z - unit i) = t := hnb _ (fun j => by
          simpa [abs_sub_comm] using te_unit_abs i j)
        rw [e1, e2]; ring
      simp only [nbrSumZ]
      rw [Finset.sum_congr rfl (fun i _ => this i)]
      simp
      ring
    have hzR : 2 * (d : ℤ) ≤ s0 z := h z (fun j => by
      have := hz' j
      have : (0 : ℤ) ≤ t := by positivity
      linarith [hz' j])
    have hp : pconf s0 t z = s0 z := by
      simp only [pconf, lap_eq, hnbr, hzt]
      ring
    rw [podo_succ, hzt, hp, if_pos hzR]
    push_cast
    ring

/-- A sandpile with arbitrarily large blocks of sites holding at least `2d` chips is not
stabilizable. -/
theorem te_not_stabilizable (s0 : Site d → ℤ)
    (h : ∀ R : ℕ, ∃ x0 : Site d, ∀ y : Site d, (∀ j, |y j - x0 j| ≤ (R : ℤ)) →
      2 * (d : ℤ) ≤ s0 y) :
    ¬ Stabilizable s0 := by
  rintro ⟨T, hT⟩
  obtain ⟨x0, hx0⟩ := h T
  have h1 := te_podo_block s0 x0 T hx0 (T + 1) le_rfl x0 (by intro j; simp)
  have h2 := congrFun (hT (T + 1) (by omega)) x0
  have h3 := te_podo_le_time s0 T x0
  rw [h2] at h1
  push_cast at h1
  omega

/-! ### Blocks in an i.i.d. background -/

/-- The event that some block of radius `R` consists of sites holding at least `2d` chips. -/
def teBlockEvent (d : ℕ) (R : ℕ) : Set (Site d → ℤ) :=
  {β | ∃ x0 : Site d, ∀ y : Site d, (∀ j, |y j - x0 j| ≤ (R : ℤ)) → 2 * (d : ℤ) ≤ β y}

theorem measurableSet_teBlockEvent (d R : ℕ) : MeasurableSet (teBlockEvent d R) := by
  have : teBlockEvent d R = ⋃ x0 : Site d, ⋂ y : Site d, ⋂ (_ : ∀ j, |y j - x0 j| ≤ (R : ℤ)),
      {β : Site d → ℤ | 2 * (d : ℤ) ≤ β y} := by
    ext β
    simp [teBlockEvent]
  rw [this]
  exact MeasurableSet.iUnion fun x0 => MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ =>
    measurableSet_le measurable_const (measurable_pi_apply y)

theorem teShift_preimage_teBlockEvent (d R : ℕ) (v : Site d) :
    teShift v ⁻¹' teBlockEvent d R = teBlockEvent d R := by
  ext β
  simp only [Set.mem_preimage, teBlockEvent, Set.mem_setOf_eq, teShift]
  constructor
  · rintro ⟨x0, hx0⟩
    refine ⟨x0 + v, fun y hy => ?_⟩
    have := hx0 (y - v) (fun j => by
      have := hy j
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      have e : y j - v j - x0 j = y j - (x0 j + v j) := by ring
      rw [e]; exact this)
    simpa using this
  · rintro ⟨x1, hx1⟩
    refine ⟨x1 - v, fun y hy => hx1 (v + y) (fun j => ?_)⟩
    have := hy j
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    have e : v j + y j - x1 j = y j - (x1 j - v j) := by ring
    rw [e]; exact this

/-- If a positive proportion of sites hold at least `2d` chips, then almost surely every
radius contains a block of sites holding at least `2d` chips. -/
theorem te_blocks_ae (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hq : 0 < ν {m : ℤ | 2 * (d : ℤ) ≤ m}) :
    ∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => ν), ∀ R : ℕ, β ∈ teBlockEvent d R := by
  rw [ae_all_iff]
  intro R
  have hv : unit (⟨0, by omega⟩ : Fin d) ≠ 0 := unit_ne_zero _
  rcases te_zero_one d ν hν (measurableSet_teBlockEvent d R) _ hv
      (teShift_preimage_teBlockEvent d R _) with h0 | h1
  · exfalso
    classical
    let S : Finset (Site d) :=
      Fintype.piFinset fun _ : Fin d => Finset.Icc (-(R : ℤ)) (R : ℤ)
    have hsub : (↑S : Set (Site d)).pi (fun _ => Set.Ici (2 * (d : ℤ))) ⊆ teBlockEvent d R := by
      intro β hβ
      refine ⟨0, fun y hy => ?_⟩
      have hyS : y ∈ S := by
        simp only [S, Fintype.mem_piFinset, Finset.mem_Icc]
        intro j
        have := hy j
        simp only [Pi.zero_apply, sub_zero] at this
        exact abs_le.mp this
      exact hβ y hyS
    have hpos : (Measure.infinitePi fun _ : Site d => ν)
        ((↑S : Set (Site d)).pi (fun _ => Set.Ici (2 * (d : ℤ)))) ≠ 0 := by
      rw [Measure.infinitePi_pi (μ := fun _ : Site d => ν) (fun _ _ => measurableSet_Ici)]
      rw [Finset.prod_ne_zero_iff]
      intro i _
      exact hq.ne'
    exact hpos (measure_mono_null hsub h0)
  · have : (Measure.infinitePi fun _ : Site d => ν) (teBlockEvent d R)ᶜ = 0 := by
      rw [measure_compl (measurableSet_teBlockEvent d R) (measure_ne_top _ _), h1]
      simp
    exact this

/-- A background with a positive proportion of sites holding at least `2d` chips is
not robust, almost surely. -/
theorem te_explosive_of_blocks (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
    (hν : IsProbabilityMeasure ν) (hq : 0 < ν {m : ℤ | 2 * (d : ℤ) ≤ m}) :
    ∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => ν), Explosive β := by
  filter_upwards [te_blocks_ae d hd ν hν hq] with β hβ
  intro hrob
  have hstab := hrob 1 le_rfl
  refine te_not_stabilizable _ (fun R => ?_) hstab
  obtain ⟨x0, hx0⟩ := hβ R
  refine ⟨x0, fun y hy => ?_⟩
  have h1 := hx0 y hy
  have h2 : (0 : ℤ) ≤ ((1 : ℕ) : ℤ) * dirac (0 : Site d) y := by
    unfold dirac
    split_ifs <;> simp
  linarith

end Exploding
