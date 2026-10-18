/-
The finite-comparison form of the wave-approximation hypothesis (Hypothesis 5.5).

The paper's display `sup over cent(n) |T̂(0,x) - T(x)| = o(n)` compares two `ℕ∞`-valued
arrival times.  `SourceWaveApproximationHyp` states it with an explicit pair of natural
numbers at each comparison, so no infinite value is read as a number.
`waveApproximationHyp_iff_sourceWaveApproximationHyp` shows that it is equivalent to
`WaveApproximationHyp` for every `d` and every law `P`: the finiteness of all arrival
times is derived from the eventual comparison on the growing boxes `cent d n`.
-/
import Exploding.Support.Hypotheses

namespace Exploding

open LatticeProb MeasureTheory Filter

/-- **Hypothesis 5.5, finite-comparison form.** For almost every background `η` that is
explosive, every `ε > 0` gives, eventually in `n`, on every `x ∈ cent d n`, natural numbers
`a` and `b` with `T̂(0,x) = a`, `T(x) = b` and `|a - b| ≤ ε n`. -/
def SourceWaveApproximationHyp (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ᵐ η ∂P, Explosive η → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x ∈ cent d n,
    ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧ arrival η x = (b : ℕ∞) ∧
      |(a : ℝ) - (b : ℝ)| ≤ ε * n

/-- Every site lies in `cent d n` for all large `n`. -/
theorem eventually_mem_cent_site {d : ℕ} (x : Site d) :
    ∀ᶠ n : ℕ in atTop, x ∈ cent d n := by
  show ∀ᶠ n : ℕ in atTop, ∀ i, |x i| ≤ (n : ℤ)
  refine eventually_all.2 fun i => ?_
  refine eventually_atTop.2 ⟨(x i).natAbs, fun n hn => ?_⟩
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hn

/-- The finite-comparison form is equivalent to the wave-approximation hypothesis, for every
`d` and every law `P`. -/
theorem waveApproximationHyp_iff_sourceWaveApproximationHyp (d : ℕ)
    (P : Measure (Site d → ℤ)) :
    WaveApproximationHyp d P ↔ SourceWaveApproximationHyp d P := by
  constructor
  · intro h
    filter_upwards [h] with η hη hExp ε hε
    obtain ⟨hL, hA, hrate⟩ := hη hExp
    filter_upwards [hrate ε hε] with n hn x hx
    exact ⟨(lastArrival η (0 : Site d) x).toNat, (arrival η x).toNat,
      (ENat.coe_toNat (hL x)).symm, (ENat.coe_toNat (hA x)).symm, hn x hx⟩
  · intro h
    filter_upwards [h] with η hη
    intro hExp
    have hcomp := hη hExp
    -- each site gets finite arrival times from the comparison on one large box
    have hfin : ∀ x : Site d, ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
        arrival η x = (b : ℕ∞) := by
      intro x
      obtain ⟨n, hn, hx⟩ := ((hcomp 1 one_pos).and (eventually_mem_cent_site x)).exists
      obtain ⟨a, b, ha, hb, -⟩ := hn x hx
      exact ⟨a, b, ha, hb⟩
    refine ⟨fun x => ?_, fun x => ?_, fun ε hε => ?_⟩
    · obtain ⟨a, -, ha, -⟩ := hfin x
      rw [ha]
      exact ENat.coe_ne_top a
    · obtain ⟨-, b, -, hb⟩ := hfin x
      rw [hb]
      exact ENat.coe_ne_top b
    · filter_upwards [hcomp ε hε] with n hn x hx
      obtain ⟨a, b, ha, hb, hab⟩ := hn x hx
      rw [ha, hb, ENat.toNat_coe, ENat.toNat_coe]
      exact hab

end Exploding
