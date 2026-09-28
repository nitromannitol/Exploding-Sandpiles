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
import Exploding.Support.SubStep

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

/-- **The paper's propagation mechanism** (`exploding.tex:499-501`): once the
support of the wave contains a line of a good cube `Q_k(j)`, the wave covers the
whole cube at a later time.  This is the crossing property of a good cube
(`exists_crossOdo_of_good`) combined with the domination of the frozen odometer
by the wave (`crossOdo_le_wave`). -/
theorem wave_covers_of_line {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N k : ℕ) (hN : 2 ≤ N)
    (j : Site d) (hgoodj : GoodAt η k j) (dir' : Fin d) (z : Site d)
    (hz : z ∈ closureN (cube d k)) (t : ℕ)
    (hline : ∀ w ∈ line d k dir' z, 0 < wave η N (0 : Site d) t (w + (k : ℤ) • j)) :
    ∃ t' : ℕ, t ≤ t' ∧ ∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t' (x + (k : ℤ) • j) := by
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  obtain ⟨n, hn, hcross⟩ := exists_crossOdo_of_good (fun x => η (x + (k : ℤ) • j)) k dir' z
    hz hgoodj
  refine ⟨t + n, Nat.le_add_right t n, fun x hx => ?_⟩
  have hdom := crossOdo_le_wave hd0 η hlow hhigh N k hN j dir' z t hline n x
  have h1 : crossOdo (fun x => η (x + (k : ℤ) • j)) k dir' z n x = 1 := hcross x hx
  rw [h1] at hdom
  omega

/-- **The line producer.**  A line of `Q_k(j)` whose base point lies in the cube is
contained in the cube, so the cover hypothesis gives the wave on it. -/
theorem line_of_cover {d : ℕ} (η : Site d → ℤ) (N k : ℕ) (i : Site d) (t : ℕ)
    (dir : Fin d) (z : Site d)
    (hcover : ∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t (x + (k : ℤ) • i))
    (hz : z ∈ cube d k) :
    ∀ y ∈ line d k dir z, 0 < wave η N (0 : Site d) t (y + (k : ℤ) • i) := by
  intro y hy
  exact hcover y (fun l => by
    by_cases hl : l = dir
    · rw [hl]; exact hy.1
    · rw [hy.2 l hl]; exact hz l)

end Exploding
