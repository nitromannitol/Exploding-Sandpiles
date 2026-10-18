/-
The last-wave bound of Lemma 3.3 for every time, and the exterior clause of the
penultimate cluster, as one conjunction.

The paper displays the inequality for `t ≥ 1`.  Its proof starts at `t = 0`, where the
bound also holds.  The exterior clause follows from the inequality, because the
penultimate wave vanishes outside the penultimate cluster.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave

namespace Exploding

open LatticeProb

/-- **Lemma 3.3** (`lemma:last_wave_bound`): the last wave is at most one plus the
penultimate wave, at every time `t : ℕ` and every site `x`.

For `2d - 2 ≤ η ≤ 2d - 1`, with the last wave from `z` well defined (some `n ≥ 1` has a
non-stabilizable `n`-wave at `z`), the bound `u_t^{(z)}(x) ≤ 1 + ũ^{(z)}(x)` holds for all
`t : ℕ`. -/
theorem lastWave_le_one_add_penultimateWave (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z) (t : ℕ) (x : Site d) :
    lastWave η z t x ≤ 1 + penultimateWave η z x := by
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

/-- **Lemma 3.3**, exterior clause (`lemma:last_wave_bound`): outside the interior
`P \ ∂°P` of the penultimate cluster `P = penultimateCluster η z`, where `∂°P` is
`innerBoundary P`, the last wave is at most one, at every time `t : ℕ`. -/
theorem lastWave_le_one_of_not_mem_interior (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z) (t : ℕ) (x : Site d)
    (hx : x ∉ penultimateCluster η z \ innerBoundary (penultimateCluster η z)) :
    lastWave η z t x ≤ 1 := by
  have hη0 : ∀ y, 0 ≤ η y := by
    intro y
    have hdZ : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith [hlow y]
  have hz : penultimateWave η z x = 0 := by
    by_cases hxP : x ∈ penultimateCluster η z
    · have hxB : x ∈ innerBoundary (penultimateCluster η z) := by
        by_contra h
        exact hx ⟨hxP, h⟩
      obtain ⟨_, y, hy, hxy⟩ := hxB
      have hnonpos : ¬ 0 < penultimateWave η z x := by
        intro hpos
        exact hy (mem_penultimateCluster_of_adj η z y x hxy hpos)
      exact le_antisymm (le_of_not_gt hnonpos) (penultimateWave_nonneg η hη0 z x)
    · exact penultimateWave_eq_zero_of_not_mem η hη0 hhigh z hlast hxP
  have h := lastWave_le_one_add_penultimateWave d hd η hlow hhigh z hlast t x
  simpa only [hz, add_zero] using h

/-- **Lemma 3.3**, complete: the displayed inequality and the exterior clause, both at
every time `t : ℕ` including `t = 0`, as one conjunction. -/
theorem lastWave_bound_complete (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z) (t : ℕ) (x : Site d) :
    lastWave η z t x ≤ 1 + penultimateWave η z x ∧
      (x ∉ penultimateCluster η z \ innerBoundary (penultimateCluster η z) →
        lastWave η z t x ≤ 1) :=
  ⟨lastWave_le_one_add_penultimateWave d hd η hlow hhigh z hlast t x,
    fun hx => lastWave_le_one_of_not_mem_interior d hd η hlow hhigh z hlast t x hx⟩

end Exploding
