import Exploding.Support.Vocab
import LatticeProb.Walk.Energy

/-!
# Graph distance on the lattice is the Manhattan norm

On `ℤ^d` with its nearest-neighbour graph `lattice d`, the extended graph distance
`(lattice d).edist x y` equals the Manhattan norm of `x - y`, cast into `ℕ∞`.  Every edge
changes the Manhattan norm of a difference by at most one, so every walk has at least that
many steps.  Conversely, a walk that corrects one coordinate at a time, built from the step
`towardVec` of `LatticeProb.Walk.Energy`, attains that length.  The equality is exact in
`ℕ∞`: no value is truncated, and it uses no hypothesis, probabilistic input or cited result.
-/

namespace Exploding

open LatticeProb

/-- The Manhattan norm `mnorm` is the natural-number `ℓ¹` norm `nrm1` viewed in `ℤ`. -/
private theorem mnorm_eq_nrm1 {d : ℕ} (z : Site d) : mnorm z = (nrm1 z : ℤ) := by
  simp only [mnorm, nrm1, Nat.cast_sum, Int.natCast_natAbs]

/-- A coordinate unit vector has `ℓ¹` norm one. -/
private theorem nrm1_unit {d : ℕ} (i : Fin d) : nrm1 (unit i : Site d) = 1 := by
  simp only [nrm1, unit]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Adjacent sites of `lattice d` differ by a vector of `ℓ¹` norm at most one. -/
private theorem nrm1_le_one_of_adj {d : ℕ} {u v : Site d} (h : (lattice d).Adj u v) :
    nrm1 (u - v) ≤ 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · have hdiff : u - v = -unit i := by rw [hi]; abel
    rw [hdiff, nrm1_neg, nrm1_unit]
  · have hdiff : u - v = unit i := by rw [hi]; abel
    rw [hdiff, nrm1_unit]

/-- Every walk from `a` to `b` in `lattice d` has at least `nrm1 (a - b)` steps: the norm
changes by at most one along each edge, and the triangle inequality bounds the rest. -/
private theorem nrm1_le_length {d : ℕ} {a b : Site d} (w : (lattice d).Walk a b) :
    nrm1 (a - b) ≤ w.length := by
  induction w with
  | nil => simp [nrm1]
  | @cons u v z h p ih =>
    have htri := nrm1_add_le (u - v) (v - z)
    rw [show u - v + (v - z) = u - z by abel] at htri
    have hstep := nrm1_le_one_of_adj h
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- Adding a unit direction to a site gives a site adjacent to it in `lattice d`. -/
private theorem lattice_adj_add_dirVec {d : ℕ} (x : Site d) (a : Dir d) :
    (lattice d).Adj x (x + dirVec a) := by
  obtain ⟨i, s⟩ := a
  cases s with
  | false =>
    rw [dirVec_eq_neg_unit]
    exact (⟨i, Or.inr (by abel)⟩ :
      ∃ j : Fin d, x + -unit i = x + unit j ∨ x = x + -unit i + unit j)
  | true =>
    rw [dirVec_eq_unit]
    exact (⟨i, Or.inl rfl⟩ : ∃ j : Fin d, x + unit i = x + unit j ∨ x = x + unit i + unit j)

/-- From every site `x` there is a walk to `y` of length `nrm1 (y - x)`, obtained by
correcting one coordinate toward `y` at each step. -/
private theorem exists_walk_nrm1_length {d : ℕ} (y : Site d) :
    ∀ (n : ℕ) (x : Site d), nrm1 (y - x) = n →
      ∃ w : (lattice d).Walk x y, w.length = n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have hxy : x = y := (sub_eq_zero.mp (nrm1_eq_zero_iff.mp hx)).symm
    subst hxy
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ n ih =>
    intro x hx
    have hne : x ≠ y := by
      intro hxy
      have h0 : nrm1 (y - x) = 0 := by
        rw [hxy, sub_self]
        simp [nrm1]
      omega
    obtain ⟨a, ha⟩ := towardVec_isDir hne
    have hstep := nrm1_toward hne
    have hadj : (lattice d).Adj x (x + towardVec y x) := by
      rw [ha]
      exact lattice_adj_add_dirVec x a
    obtain ⟨w, hw⟩ := ih (x + towardVec y x) (by omega)
    exact ⟨SimpleGraph.Walk.cons hadj w, by rw [SimpleGraph.Walk.length_cons, hw]⟩

/-- The graph distance of `lattice d`, valued in `ℕ∞`, is the Manhattan norm of `x - y`.
Every walk from `x` to `y` has at least that many steps, and a walk of exactly that length
exists. -/
theorem lattice_edist_eq_mnorm (d : ℕ) (x y : Site d) :
    (lattice d).edist x y = ((mnorm (x - y)).toNat : ℕ∞) := by
  rw [mnorm_eq_nrm1, Int.toNat_natCast]
  refine le_antisymm ?_ ?_
  · obtain ⟨w, hw⟩ := exists_walk_nrm1_length y (nrm1 (x - y)) x (nrm1_sub_comm y x)
    have hle := SimpleGraph.edist_le w
    rw [hw] at hle
    exact hle
  · rw [SimpleGraph.edist]
    exact le_iInf fun w => by exact_mod_cast nrm1_le_length w

-- Consumer check at `d = 2`: the origin and the site `(1, 1)` are at graph distance `2`.
example : (lattice 2).edist (0 : Site 2) ![1, 1] = 2 := by
  have h : mnorm (0 - ![1, 1] : Site 2) = 2 := by
    norm_num [mnorm, Fin.sum_univ_two]
  rw [lattice_edist_eq_mnorm, h]
  rfl

end Exploding
