/-
Measurability of the explosive event, and its law consequence on the bounded-background carrier.

The parallel toppling odometer `podo` is a measurable function of the background at every finite
time and site (`podo_measurable`), by induction on the time as `bc_fodo_measurable` does for the
frozen odometer. An odometer that stops moving at one step stops for good (`podo_eq_of_step`), so
stabilizability is a countable union over the step time (`stabilizable_iff_podo_step`). Robustness
is a countable intersection over `n`, and explosiveness is its complement
(`measurableSet_explosive`).

On the carrier `Ω = {η // InOmega d ηmin η}`, the consumer `explosiveLaw_map_subtype_iff` states
that the push-forward of a probability measure `Q` is explosive exactly when `Q` gives the explosive
event probability one. Nothing here adds a hypothesis: every statement is about `podo`,
`Stabilizable`, `Robust`, `Explosive`, `ExplosiveLaw` and `InOmega` as they are defined.
-/
import Exploding.Support.Hypotheses

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- If the odometer does not move from time `T` to `T + 1`, it never moves again. -/
theorem podo_eq_of_step (s0 : Site d → ℤ) (T : ℕ) (h : podo s0 (T + 1) = podo s0 T) :
    ∀ k : ℕ, podo s0 (T + k) = podo s0 T := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hz : ∀ x, (if 2 * (d : ℤ) ≤ pconf s0 T x then (1 : ℤ) else 0) = 0 := by
      intro x
      have hx := congrFun h x
      rw [podo_succ] at hx
      linarith
    show podo s0 (T + k + 1) = podo s0 T
    funext x
    have hpc : pconf s0 (T + k) x = pconf s0 T x := by
      simp only [pconf, ih]
    rw [podo_succ, hpc, ih, hz x, add_zero]

/-- `s₀` is stabilizable exactly when the odometer does not move from some time `T` to `T + 1`. -/
theorem stabilizable_iff_podo_step (s0 : Site d → ℤ) :
    Stabilizable s0 ↔ ∃ T : ℕ, podo s0 (T + 1) = podo s0 T := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T, hT (T + 1) (Nat.le_succ T)⟩
  · rintro ⟨T, hT⟩
    refine ⟨T, fun t ht => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact podo_eq_of_step s0 T hT k

/-- At each finite time and site, the odometer is a measurable function of the background `η`,
where the background enters through the coordinatewise measurable map `F`: induction on the time,
generalizing the site, with `podo_succ` and `Measurable.ite` on `{η | 2d ≤ pconf (F η) t x}`. -/
theorem podo_measurable (F : (Site d → ℤ) → (Site d → ℤ)) (hF : ∀ y, Measurable fun η => F η y)
    (t : ℕ) (x : Site d) : Measurable fun η : Site d → ℤ => podo (F η) t x := by
  induction t generalizing x with
  | zero =>
    simp only [podo_zero]
    exact measurable_const
  | succ t ih =>
    simp only [podo_succ]
    apply Measurable.add (ih x)
    apply Measurable.ite
    · apply measurableSet_le measurable_const
      unfold pconf lap nbrSumZ
      apply Measurable.add (hF x)
      apply Measurable.sub
      · apply Finset.measurable_sum
        intro i _
        apply Measurable.add
        · exact ih (x + unit i)
        · exact ih (x - unit i)
      · apply Measurable.mul measurable_const (ih x)
    · exact measurable_const
    · exact measurable_const

/-- The stabilizable backgrounds form a measurable set, for any coordinatewise measurable
shift `F` of the background. The event is a countable union over the step time of countable
intersections over the sites of equalities of two measurable real-valued functions. -/
theorem measurableSet_stabilizable (F : (Site d → ℤ) → (Site d → ℤ))
    (hF : ∀ y, Measurable fun η => F η y) :
    MeasurableSet {η : Site d → ℤ | Stabilizable (F η)} := by
  have heq : {η : Site d → ℤ | Stabilizable (F η)} =
      ⋃ T : ℕ, ⋂ x : Site d, {η : Site d → ℤ | podo (F η) (T + 1) x = podo (F η) T x} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, stabilizable_iff_podo_step,
      funext_iff]
  rw [heq]
  refine MeasurableSet.iUnion fun T => MeasurableSet.iInter fun x => ?_
  have hset : {η : Site d → ℤ | podo (F η) (T + 1) x = podo (F η) T x} =
      (fun η : Site d → ℤ => podo (F η) (T + 1) x - podo (F η) T x) ⁻¹' ({0} : Set ℤ) := by
    ext η
    simp [sub_eq_zero]
  rw [hset]
  exact (Measurable.sub (podo_measurable F hF (T + 1) x) (podo_measurable F hF T x))
    MeasurableSet.of_discrete

/-- The robust backgrounds form a measurable set: a countable intersection over `n` of the
measurable stabilizability events of the shifts `η + n δ₀`. -/
theorem measurableSet_robust : MeasurableSet {η : Site d → ℤ | Robust η} := by
  have heq : {η : Site d → ℤ | Robust η} =
      ⋂ n : ℕ, {η : Site d → ℤ | 1 ≤ n →
        Stabilizable (fun x => η x + n * dirac (0 : Site d) x)} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Robust]
  rw [heq]
  refine MeasurableSet.iInter fun n => ?_
  by_cases hn : 1 ≤ n
  · simp only [hn, true_implies]
    exact measurableSet_stabilizable (fun η x => η x + n * dirac (0 : Site d) x)
      (fun y => (measurable_pi_apply y).add measurable_const)
  · have huniv : {η : Site d → ℤ | 1 ≤ n →
        Stabilizable (fun x => η x + n * dirac (0 : Site d) x)} = Set.univ := by
      ext η
      simp [hn]
    rw [huniv]
    exact MeasurableSet.univ

/-- The explosive backgrounds form a measurable set: the complement of the robust ones. -/
theorem measurableSet_explosive : MeasurableSet {η : Site d → ℤ | Explosive η} := by
  have heq : {η : Site d → ℤ | Explosive η} = {η : Site d → ℤ | Robust η}ᶜ := by
    ext η
    simp [Explosive]
  rw [heq]
  exact measurableSet_robust.compl

/-- On the bounded-background carrier `Ω = {η // InOmega d ηmin η}`, the push-forward of a
probability measure `Q` is explosive, in the almost-sure sense of `ExplosiveLaw`, exactly when `Q`
gives the explosive event probability one. The event is measurable on `Ω` as the preimage of the
ambient explosive event under the coordinate projection. -/
theorem explosiveLaw_map_subtype_iff (ηmin : ℤ)
    (Q : Measure {η : Site d → ℤ // InOmega d ηmin η}) [IsProbabilityMeasure Q] :
    ExplosiveLaw d (Q.map Subtype.val) ↔ Q {ω | Explosive ω.val} = 1 := by
  have hval : Measurable (Subtype.val : {η : Site d → ℤ // InOmega d ηmin η} → Site d → ℤ) :=
    measurable_subtype_coe
  have hev : MeasurableSet {ω : {η : Site d → ℤ // InOmega d ηmin η} | Explosive ω.val} :=
    (measurableSet_explosive (d := d)).preimage hval
  unfold ExplosiveLaw
  rw [ae_map_iff hval.aemeasurable (measurableSet_explosive (d := d)), ae_iff]
  exact prob_compl_eq_zero_iff hev

end Exploding
