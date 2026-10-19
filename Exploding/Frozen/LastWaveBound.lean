/-
Lemma 3.3 of the paper: the last wave exceeds the penultimate wave by at most one at
every time, and the last wave is at most one outside the interior of the penultimate
cluster.
-/
import Exploding.Support.LastWaveBoundComplete

open Exploding LatticeProb

/-- **Lemma 3.3** (`paper/corrected-arxiv/exploding-corrected-arxiv.tex:858-863`, label `lemma:last_wave_bound`).

The displayed inequality `u_t^{(z)}(x) ≤ 1 + ũ^{(z)}(x)` is stated in the paper for `t ≥ 1`;
its proof starts at `t = 0`, so it holds for every `t : ℕ`.  The exterior clause, that the
last wave is at most one outside the interior `P \ ∂°P` of the penultimate cluster `P`, is
stated for every `t : ℕ` as well.  The two are proved in
`Exploding.Support.LastWaveBoundComplete`.  The standing hypotheses `2d - 2 ≤ η ≤ 2d - 1` and
the well-defined last wave (Lemma 3.2) are the ones Section 3 fixes. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.last_wave_bound (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z) (t : ℕ) (x : Site d) :
    lastWave η z t x ≤ 1 + penultimateWave η z x ∧
      (x ∉ penultimateCluster η z \ innerBoundary (penultimateCluster η z) →
        lastWave η z t x ≤ 1)
-- FROZEN-STATEMENT-END
:= Exploding.lastWave_bound_complete d hd η hlow hhigh z hlast t x
