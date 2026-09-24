/-
Lemma 3.3 of the paper: the last wave exceeds the penultimate wave by at most
one.
-/
import Exploding.Support.Vocab

open Exploding LatticeProb

-- The paper's `t ≥ 1` is part of the statement but not needed for the bound,
-- which holds from `t = 0` on; the hypothesis stays, so the linter is silenced.
set_option linter.unusedVariables false in
/-- **Lemma 3.3** (`exploding.tex:730-735`, label `lemma:last_wave_bound`).

"The last wave started at `z` is bounded by one outside the interior of the
penultimate-cluster of `z`.  Moreover, for all `t ≥ 1` and `x, z ∈ ℤ^d`,
`u_t^{(z)}(x) ≤ (1 + ũ^{(z)}(x))`."

The displayed inequality is the content; the sentence before it is the reading
of that inequality off `(3.3)`.  Section 3 fixes `η` as in `(1.2)`, so
`2d - 2 ≤ η ≤ 2d - 1`, and takes the last wave to be well defined, which is
Lemma 3.2: some `n ≥ 1` has a non-stabilizable wave at `z`.  Those are the two
hypotheses carried. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.last_wave_bound (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z)
    (t : ℕ) (ht : 1 ≤ t) (x : Site d) :
    lastWave η z t x ≤ 1 + penultimateWave η z x
-- FROZEN-STATEMENT-END
:= by
  have hdR : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hdz : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hη0 : ∀ y, 0 ≤ η y := fun y => by linarith [hlow y]
  have hne : {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z}.Nonempty := hlast
  have hmem : 1 ≤ waveThreshold η z ∧ ¬ WaveStabilizable η (waveThreshold η z) z :=
    Nat.sInf_mem hne
  simp only [lastWave]
  set M := waveThreshold η z with hMdef
  have key : ∀ u : Site d → ℤ, (∀ y, 0 ≤ u y) → u z = (M : ℤ) - 1 →
      (∀ y, y ≠ z → lap u y + η y ≤ 2 * (d : ℤ) - 1) →
      ∀ s : ℕ, ∀ y : Site d, wave η M z s y ≤ 1 + u y := by
    intro u hu0 huz hufix s
    induction s with
    | zero =>
      intro y
      by_cases h : y = z
      · subst h; rw [wave_at_centre]; linarith [huz]
      · rw [wave_zero]; simp only [if_neg h]; linarith [hu0 y]
    | succ s ih =>
      intro y
      by_cases h : y = z
      · subst h; rw [wave_at_centre]; linarith [huz]
      · rw [wave_of_ne _ _ _ _ _ h]
        have h1 : nbrSumZ (wave η M z s) y ≤ nbrSumZ (fun w => 1 + u w) y := nbrSumZ_mono ih y
        have h2 : nbrSumZ (fun w => 1 + u w) y = 2 * (d : ℤ) * 1 + nbrSumZ u y :=
          nbrSumZ_add_const u 1 y
        have h3 := hufix y h
        simp only [lap] at h3
        have hlt : nbrSumZ (wave η M z s) y + η y < (1 + u y + 1) * (2 * (d : ℤ)) := by
          nlinarith
        exact Int.lt_add_one_iff.mp ((Int.ediv_lt_iff_lt_mul hdz).mpr hlt)
  by_cases hM1 : M = 1
  · have hp : penultimateWave η z = 0 := by simp [penultimateWave, ← hMdef, hM1]
    rw [hp]
    have := key 0 (fun _ => le_refl 0) (by simp [hM1]) ?_ t x
    · simpa using this
    · intro y _
      have : nbrSumZ (0 : Site d → ℤ) y = 0 := by simp [nbrSumZ]
      simp only [lap, this]
      simpa using hhigh y
  · have hM2 : 2 ≤ M := by omega
    have hstab : WaveStabilizable η (M - 1) z := by
      by_contra hcon
      have hm : M - 1 ∈ {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z} := ⟨by omega, hcon⟩
      have hle : M ≤ M - 1 := Nat.sInf_le hm
      omega
    have hp : penultimateWave η z = waveTerminal η (M - 1) z := by
      simp [penultimateWave, ← hMdef, hM1]
    rw [hp]
    refine key (waveTerminal η (M - 1) z) (fun y => wave_nonneg η hη0 (M - 1) z _ y) ?_ ?_ t x
    · show wave η (M - 1) z _ z = (M : ℤ) - 1
      rw [wave_at_centre]
      have : (1 : ℕ) ≤ M := by omega
      push_cast [Nat.cast_sub this]
      ring
    · exact fun y hy => lap_le_of_fixed η hdz _ y (waveTerminal_fixed η (M - 1) z hstab hy)

