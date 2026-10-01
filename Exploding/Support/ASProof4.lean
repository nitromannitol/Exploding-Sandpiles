/-
Discharge of the last two claims of
`Exploding.Frozen.approximate_subadditive`.  Sorry-free support file.

## `hrobust`: robustness forbids a non-stabilizable centred wave

The persistent-source comparison is already formalised in
`Exploding/Support/GLWProofAux.lean`:

* `glw_wave_to_explosive_pstable`: the terminal odometer `v` of a stabilizable
  pile is stable, `s0 x + lap v x ≤ 2d - 1`;
* `glw_wave_to_explosive_v0`: if `s0 = η + (2dn+1) δ_0` stabilizes with terminal
  `v`, then `v 0 ≥ n` (the extra `2dn+1` chips at the origin force it to topple
  at least `n` times);
* `glw_wave_to_explosive_dom`: a nonnegative stable `v` with `v 0 ≥ n` dominates
  the `n`-wave, `wave η n 0 t x ≤ v x`.

So if `η` is robust, `v := podo (η + (2dn+1) δ_0) T` (terminal) dominates the
`n`-wave.  Off the origin `s0 = η ≤ 2d - 1`, so by `as3_podo_support_le_time` the
support of `v` is contained in the finite ball of radius `T`; the wave is thus a
monotone sequence supported in that finite ball, hence eventually constant.
-/
import Exploding.Support.ASProof
import Exploding.Support.ASProof3
import Exploding.Support.GLWProofAux

open Exploding LatticeProb MeasureTheory

set_option linter.unusedVariables false

/-- A monotone `ℤ`-valued sequence that is bounded above is eventually constant. -/
theorem as4_mono_bdd_eventually_constant (f : ℕ → ℤ) (hmono : ∀ s t : ℕ, s ≤ t → f s ≤ f t)
    (hbdd : ∃ B : ℤ, ∀ t : ℕ, f t ≤ B) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → f t = f T := by
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨ub, hub, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun k : ℤ => ∃ t : ℕ, f t = k)
    ⟨B, fun k hk => by obtain ⟨t, ht⟩ := hk; rw [← ht]; exact hB t⟩
    ⟨f 0, 0, rfl⟩
  obtain ⟨T, hT⟩ := hub
  exact ⟨T, fun t ht => le_antisymm
    (calc f t ≤ ub := hmax _ ⟨t, rfl⟩
      _ = f T := hT.symm)
    (hmono T t ht)⟩

/-- **`hrobust`.** On a background bounded by `2d - 1` off the origin, robustness
(no finite addition explodes) forbids a non-stabilizable centred wave. -/
theorem as4_hrobust (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hrob : Robust η) : ∀ n : ℕ, 1 ≤ n → WaveStabilizable η n (0 : Site d) := by
  intro n _hn
  have hη0 : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
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
    glw_wave_to_explosive_v0 η hη0 hdpos n v hv0nn hstable0
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
