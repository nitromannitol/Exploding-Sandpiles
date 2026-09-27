/-
The crossing time of a box, read off the odometer: `crossingTime η k i z ≤ m` holds
exactly when some time `n ≤ m` has toppled the whole box, and a good cube therefore
topples completely once one of its lines is lit.
-/
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The crossing time is at most `m` exactly when some time `n ≤ m` topples the box. -/
theorem crossingTime_le_iff (η : Site d → ℤ) (k : ℕ) (i : Fin d) (z : Site d) (m : ℕ) :
    crossingTime η k i z ≤ (m : ℕ∞) ↔
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ m ∧ ∀ x ∈ cube d k, crossOdo η k i z n x = 1 := by
  unfold crossingTime
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hmem : ∀ t ∈ {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ 1 ≤ n ∧
        ∀ x ∈ cube d k, crossOdo η k i z n x = 1}, (m : ℕ∞) + 1 ≤ t := by
      intro t ht
      obtain ⟨n, rfl, hn1, hnP⟩ := ht
      by_contra hle
      have hnm : n ≤ m := by
        by_contra hnm'
        have hlt : m < n := not_le.mp hnm'
        exact hle (by exact_mod_cast (Nat.succ_le_of_lt hlt))
      obtain ⟨x, hx, hne⟩ := hc n hn1 hnm
      exact hne (hnP x hx)
    have hle := le_sInf hmem
    have h2 : (m : ℕ∞) + 1 ≤ (m : ℕ∞) := le_trans hle h
    exact absurd h2 (by simp [ENat.add_one_le_iff])
  · rintro ⟨n, hn1, hnm, hnP⟩
    exact le_trans (sInf_le ⟨n, rfl, hn1, hnP⟩) (by exact_mod_cast hnm)

/-- A good cube topples completely once one of its lines is lit, at a uniform time. -/
theorem goodCube_topples_uniform (η : Site d → ℤ) (k : ℕ) (hgood : GoodCube η k)
    (i : Fin d) (z : Site d) (hz : z ∈ closureN (cube d k)) :
    ∃ t : ℕ, 1 ≤ t ∧ ∀ x ∈ cube d k, crossOdo η k i z t x = 1 := by
  have hle := hgood i z hz
  obtain ⟨n, hn1, _, hnP⟩ := (crossingTime_le_iff η k i z (k ^ d)).mp hle
  exact ⟨n, hn1, hnP⟩

/-- A good cube topples completely once one of its lines is lit. -/
theorem goodCube_topples_of_line (η : Site d → ℤ) (k : ℕ) (hgood : GoodCube η k)
    (i : Fin d) (z : Site d) (hz : z ∈ closureN (cube d k)) :
    ∀ x ∈ cube d k, ∃ t : ℕ, 1 ≤ t ∧ crossOdo η k i z t x = 1 := by
  obtain ⟨t, ht1, ht⟩ := goodCube_topples_uniform η k hgood i z hz
  exact fun x hx => ⟨t, ht1, ht x hx⟩

end Exploding
