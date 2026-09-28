/-
The crossing property of a good cube, in the form the propagation step of
Lemma 3.2 uses it: if a line of `Q_k` through a point of its outer boundary has
already fired, then the whole cube has fired within `k^d` steps.

This is the paper's `exploding.tex:499-501`: a good cube is one whose crossing
time is at most `k^d`, and the crossing time is exactly the first time the
`{Q_k^c ∪ L}`-frozen odometer is `1` on all of `Q_k`.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubGeom

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The crossing time of a good cube is attained at a natural number at most
`k^d`. -/
theorem exists_crossOdo_of_good {d : ℕ} (η : Site d → ℤ) (k : ℕ) (i : Fin d) (z : Site d)
    (hz : z ∈ closureN (cube d k)) (hgood : GoodCube η k) :
    ∃ n : ℕ, n ≤ k ^ d ∧ ∀ x ∈ cube d k, crossOdo η k i z n x = 1 := by
  have h1 : crossingTime η k i z ≤ ((k ^ d : ℕ) : ℕ∞) := hgood i z hz
  have hex : ∃ n : ℕ, 1 ≤ n ∧ ∀ x ∈ cube d k, crossOdo η k i z n x = 1 := by
    by_contra hcon
    have h2 : crossingTime η k i z = ⊤ := sInf_coe_top hcon
    rw [h2] at h1
    exact absurd h1 (by simp)
  obtain ⟨n, hn1, hn2⟩ := sInf_coe_attained (P := fun n => 1 ≤ n ∧
    ∀ x ∈ cube d k, crossOdo η k i z n x = 1) hex
  refine ⟨n, ?_, hn1.2⟩
  have h3 : ((n : ℕ∞)) = crossingTime η k i z := hn2.symm
  rw [← h3] at h1
  exact_mod_cast h1

end Exploding
