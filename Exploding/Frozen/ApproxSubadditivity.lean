/-
Lemma 3.4 of the paper: the penultimate-cluster arrival times are subadditive.

The proof is the paper's.  Write `N = T̃(a,b)`.  Off the penultimate cluster of
`b` the last wave started at `a`, run for `N` extra steps, dominates the last
wave started at `b`:

  `u^{(a)}_{N+t}(x) ≥ u^{(b)}_t(x)`  whenever  `ũ^{(b)}(x) = 0`.

Inside the cluster the domination is read off Lemma 3.3 instead: there
`u^{(b)}_t ≤ 1 + ũ^{(b)} = 1` while `u^{(a)}_{N+t} ≥ 1` by the definition of `N`
and monotonicity in time.  The induction step at a site `x` outside the cluster
uses only the neighbours of `x`, and every neighbour of such an `x` carries no
penultimate mass, since a neighbour that did would put `x` in the cluster.
-/
import Exploding.Support.Wave
import Exploding.Frozen.LastWaveBound

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The domination of the paper's proof of Lemma 3.4: past the penultimate-cluster
arrival time `N = T̃(a,b)`, the last wave started at `a` dominates the last wave
started at `b` at every site carrying no penultimate mass of `b`. -/
theorem lastWave_dominates (η : Site d → ℤ) (hd : 2 ≤ d)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y)
    (a b : Site d) (N : ℕ)
    (hNb : ∀ w ∈ penultimateCluster η b, 0 < lastWave η a N w) :
    ∀ t : ℕ, ∀ x : Site d, penultimateWave η b x = 0 →
      lastWave η b t x ≤ lastWave η a (N + t) x := by
  have hdR : (2:ℤ) ≤ (d:ℤ) := by exact_mod_cast hd
  have hdz : (0:ℤ) < 2 * (d:ℤ) := by linarith
  have hη0 : ∀ y, 0 ≤ η y := fun y => by linarith [hlow y]
  have hMb : 1 ≤ waveThreshold η b := (Nat.sInf_mem (hlast b)).1
  have hMa : 1 ≤ waveThreshold η a := (Nat.sInf_mem (hlast a)).1
  have hone : ∀ s : ℕ, ∀ w ∈ penultimateCluster η b, 1 ≤ lastWave η a (N + s) w := by
    intro s w hw
    have h1 : 0 < lastWave η a N w := hNb w hw
    have h2 : lastWave η a N w ≤ lastWave η a (N + s) w :=
      wave_mono_time η hη0 hdz (waveThreshold η a) a (Nat.le_add_right N s) w
    linarith
  intro t
  induction t with
  | zero =>
    intro x hx
    by_cases hxb : x = b
    · have hM1 : waveThreshold η b = 1 := by
        have hc := penultimateWave_at_centre η b hMb
        rw [hxb] at hx
        rw [hx] at hc
        omega
      have hval : lastWave η b 0 x = 1 := by simp [lastWave, hM1, hxb]
      rw [hval]
      simpa using hone 0 x (hxb ▸ centre_mem_penultimateCluster η b)
    · have hval : lastWave η b 0 x = 0 := by simp [lastWave, wave_zero, hxb]
      rw [hval]
      exact wave_nonneg η hη0 (waveThreshold η a) a (N + 0) x
  | succ t ih =>
    intro x hx
    have h3 := Exploding.Frozen.last_wave_bound d hd η hlow hhigh b (hlast b) (t+1)
      (by omega) x
    rw [hx] at h3
    by_cases hxP : x ∈ penultimateCluster η b
    · have h4 := hone (t+1) x hxP
      linarith
    · have hxb : x ≠ b := fun h => hxP (h ▸ centre_mem_penultimateCluster η b)
      by_cases hxa : x = a
      · have hval : lastWave η a (N + (t+1)) x = (waveThreshold η a : ℤ) := by
          rw [hxa]; simp [lastWave]
        have hge : (1:ℤ) ≤ (waveThreshold η a : ℤ) := by exact_mod_cast hMa
        rw [hval]
        linarith
      · have hnb : ∀ y, (lattice d).Adj y x → lastWave η b t y ≤ lastWave η a (N + t) y := by
          intro y hy
          refine ih y ?_
          by_contra hcon
          exact hxP (mem_penultimateCluster_of_adj η b x y hy
            (lt_of_le_of_ne (penultimateWave_nonneg η hη0 b y) (Ne.symm hcon)))
        have hsum : nbrSumZ (lastWave η b t) x ≤ nbrSumZ (lastWave η a (N + t)) x :=
          nbrSumZ_mono_adj _ _ x hnb
        simp only [lastWave] at hsum ⊢
        rw [wave_of_ne η (waveThreshold η b) b x t hxb,
          show N + (t + 1) = (N + t) + 1 from by omega,
          wave_of_ne η (waveThreshold η a) a x (N + t) hxa]
        exact Int.ediv_le_ediv hdz (by linarith)

end Exploding

open Exploding LatticeProb

/-- **Lemma 3.4** (`exploding.tex:758-763`, label `lemma:approx_subadditivity`).

"The penultimate-cluster arrival times are subadditive: for all `a, b, z ∈ ℤ^d`,
`T̃(a,z) ≤ T̃(a,b) + T̃(b,z)`."

The arrival times are taken in `ℕ∞`, where addition is monotone and `⊤` absorbs,
so the inequality says exactly what the paper's does and never reads a junk
natural number.  Section 3 fixes `η` as in `(1.2)` and takes every last wave to
be well defined, which is Lemma 3.2. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.approx_subadditivity (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y)
    (a b z : Site d) :
    clusterArrival η a z ≤ clusterArrival η a b + clusterArrival η b z
-- FROZEN-STATEMENT-END
:= by
  have hdR : (2:ℤ) ≤ (d:ℤ) := by exact_mod_cast hd
  have hdz : (0:ℤ) < 2 * (d:ℤ) := by linarith
  have hη0 : ∀ y, 0 ≤ η y := fun y => by linarith [hlow y]
  by_cases hab : clusterArrival η a b = ⊤
  · simp [hab]
  by_cases hbz : clusterArrival η b z = ⊤
  · simp [hbz]
  obtain ⟨N, hN1, hNb, hNeq⟩ := clusterArrival_exists η a b hab
  obtain ⟨K, hK1, hKz, hKeq⟩ := clusterArrival_exists η b z hbz
  rw [hNeq, hKeq, ← Nat.cast_add]
  refine clusterArrival_le η a z (N + K) (by omega) ?_
  intro w hw
  by_cases hpw : penultimateWave η b w = 0
  · have hdom := lastWave_dominates η hd hlow hhigh hlast a b N hNb K w hpw
    have hpos := hKz w hw
    linarith
  · have hwb : w ∈ penultimateCluster η b := by
      by_contra hcon
      exact hpw (penultimateWave_eq_zero_of_not_mem η hη0 hhigh b (hlast b) hcon)
    have h1 : 0 < lastWave η a N w := hNb w hwb
    have h2 : lastWave η a N w ≤ lastWave η a (N + K) w :=
      wave_mono_time η hη0 hdz (waveThreshold η a) a (Nat.le_add_right N K) w
    linarith
