/-
Recurrence of the clamped product law, for Theorem 1.4.

A background with `d ≤ η ≤ 2d - 1` is recurrent as soon as the constant background
`d` is: the `V^c`-frozen odometer is monotone in the background and is capped at
`1` when the background is at most `2d - 1`.  Then the product law with one-site
law supported in `[d, 2d - 1]` is almost surely recurrent.
-/
import Exploding.Support.Hypotheses
import Exploding.Support.SubFodo

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The `S`-frozen odometer is monotone in the background. -/
theorem te_fodo_mono (S : Set (Site d)) (s0 s0' w0 : Site d → ℤ)
    (hle : ∀ x, s0 x ≤ s0' x) (t : ℕ) (x : Site d) :
    fodo S s0 w0 t x ≤ fodo S s0' w0 t x := by
  induction t generalizing x with
  | zero => simp [fodo_zero]
  | succ t ih =>
    rw [fodo_succ, fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx]
      by_cases hlt : fodo S s0 w0 t x < fodo S s0' w0 t x
      · have h1 : (if 2 * (d : ℤ) ≤ fconf S s0 w0 t x then (1 : ℤ) else 0) ≤ 1 := by
          split <;> omega
        have h2 : (0 : ℤ) ≤ (if 2 * (d : ℤ) ≤ fconf S s0' w0 t x then (1 : ℤ) else 0) := by
          split <;> omega
        linarith
      · have heq : fodo S s0 w0 t x = fodo S s0' w0 t x := le_antisymm (ih x) (not_lt.mp hlt)
        have hconf : fconf S s0 w0 t x ≤ fconf S s0' w0 t x := by
          simp only [fconf, lap_eq]
          have hn : nbrSumZ (fodo S s0 w0 t) x ≤ nbrSumZ (fodo S s0' w0 t) x :=
            nbrSumZ_mono (fun y => ih y) x
          have hv : 2 * (d : ℤ) * fodo S s0 w0 t x = 2 * (d : ℤ) * fodo S s0' w0 t x := by
            rw [heq]
          linarith [hle x]
        have h3 : (if 2 * (d : ℤ) ≤ fconf S s0 w0 t x then (1 : ℤ) else 0) ≤
            (if 2 * (d : ℤ) ≤ fconf S s0' w0 t x then (1 : ℤ) else 0) := by
          by_cases h : 2 * (d : ℤ) ≤ fconf S s0 w0 t x
          · rw [if_pos h, if_pos (le_trans h hconf)]
          · rw [if_neg h]; split <;> omega
        linarith

/-- A background between a recurrent one and `2d - 1` is recurrent. -/
theorem te_recurrent_mono {η1 η2 : Site d → ℤ} (hle : ∀ x, η1 x ≤ η2 x)
    (hub : ∀ x, η2 x ≤ 2 * (d : ℤ) - 1) (h1 : Recurrent η1) : Recurrent η2 := by
  classical
  intro V t ht x hx
  have hle1 : fodo ((↑V : Set (Site d))ᶜ) η1
      (fun y => if y ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0) t x
      ≤ fodo ((↑V : Set (Site d))ᶜ) η2
      (fun y => if y ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0) t x :=
    te_fodo_mono _ η1 η2 _ hle t x
  have hup : fodo ((↑V : Set (Site d))ᶜ) η2
      (fun y => if y ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0) t x ≤ 1 :=
    fodo_le_one _ η2 _ hub (fun y => by split_ifs <;> omega)
      (fun y => by split_ifs <;> omega) t x
  rw [h1 V t ht x hx] at hle1
  exact le_antisymm hup hle1

/-- A property holding with full one-site mass holds at every site, almost surely. -/
theorem te_ae_prod (d : ℕ) (μ : Measure ℤ) (hμ : IsProbabilityMeasure μ) (p : ℤ → Prop)
    (hpmeas : MeasurableSet {m : ℤ | p m}) (hp : μ {m : ℤ | p m} = 1) :
    ∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => μ), ∀ x : Site d, p (β x) := by
  haveI : IsProbabilityMeasure μ := hμ
  haveI hinst : ∀ i : Site d, IsProbabilityMeasure ((fun _ : Site d => μ) i) := fun _ => hμ
  rw [ae_all_iff]
  intro x
  have hmapx := Measure.infinitePi_map_eval (μ := fun _ : Site d => μ) x
  have hmeas : Measurable fun β : Site d → ℤ => β x := measurable_pi_apply x
  have hzero : μ {m : ℤ | p m}ᶜ = 0 := by
    rw [measure_compl hpmeas (measure_ne_top _ _), hp]
    simp
  rw [ae_iff]
  have hpre : {β : Site d → ℤ | ¬ p (β x)} = (fun β : Site d → ℤ => β x) ⁻¹' {m : ℤ | p m}ᶜ := by
    ext β; simp
  rw [hpre, ← Measure.map_apply hmeas hpmeas.compl, hmapx]
  exact hzero

/-- The product law with one-site law supported in `[d, 2d - 1]` is almost surely recurrent,
given that the constant background `d` is recurrent. -/
theorem te_recurrent_law (d : ℕ) (hconst : Recurrent (fun _ : Site d => (d : ℤ)))
    (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1)
    (hupper : ν {m : ℤ | m ≤ 2 * (d : ℤ) - 1} = 1) :
    RecurrentLaw d (Measure.infinitePi fun _ : Site d => ν) := by
  rw [RecurrentLaw]
  have hlow_ae := te_ae_prod d ν hν (fun m : ℤ => (d : ℤ) ≤ m) measurableSet_Ici hlow
  have hupper_ae := te_ae_prod d ν hν (fun m : ℤ => m ≤ 2 * (d : ℤ) - 1)
    measurableSet_Iic hupper
  filter_upwards [hlow_ae, hupper_ae] with η hη hηu
  exact te_recurrent_mono (fun x => hη x) (fun x => hηu x) hconst

end Exploding
