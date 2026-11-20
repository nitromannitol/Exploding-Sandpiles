/-
Uniform two-point connectivity in the slabs of cubes, in the bond model of this repository and in
the bond model of Lattice-Probability.

For a cube `c + [0, n)^d`, a direction `a`, a width `w` and an index `k` with `(k + 1) w ≤ n`, the
slab is the part of the cube whose `a`-th coordinate lies in `c_a + [k w, (k + 1) w)`.  Uniform
slab connectivity at density `q` asks for one width `w` and one `ρ > 0` such that any two sites
of any such slab are joined by an open path inside the slab with probability at least `ρ`.  In
the Lattice-Probability model this is the statement `UniformCubeSlabConnectivity d p` of the
Percolation-Rigidity formalization, with the integer cube written through its corner and size;
for `d ≥ 3` and `p` above the critical probability it is the slab form of the theorem of
Grimmett and Marstrand (*The supercritical phase of percolation is well behaved*, Proc. R. Soc.
Lond. A 430 (1990)).  It transfers to the bond model of this repository at every density above
`bondCritical d` (`slabConnectivity_of_latticeBond`).
-/
import Exploding.Support.APLatticeBondBridge

open LatticeProb MeasureTheory

namespace Exploding

variable {d : ℕ}

/-- The slab of the cube `c + [0, n)^d` in direction `a` of width `w` with index `k`. -/
def cubeSlab (c : Site d) (n : ℕ) (a : Fin d) (w k : ℕ) : Set (Site d) :=
  {x | (∀ i, c i ≤ x i ∧ x i < c i + (n : ℤ)) ∧ c a + ((k * w : ℕ) : ℤ) ≤ x a ∧
    x a < c a + (((k + 1) * w : ℕ) : ℤ)}

/-- Uniform two-point connectivity in the slabs of cubes for the Lattice-Probability bond law;
this is `UniformCubeSlabConnectivity d p` of Percolation-Rigidity with the integer cube given by
its corner `c` and size `n`. -/
def LatticeBond.UniformCubeSlabConnectivity (d : ℕ) (p : unitInterval) : Prop :=
  ∃ width : ℕ, 0 < width ∧ ∃ ρ : ℝ, 0 < ρ ∧
    ∀ (c : Site d) (n : ℕ) (a : Fin d) (k : ℕ), (k + 1) * width ≤ n →
      ∀ x ∈ cubeSlab c n a width k, ∀ y ∈ cubeSlab c n a width k,
        ρ ≤ (LatticeBond.latticeBondLaw d p).real
          {ω | (LatticeBond.openIn ω (cubeSlab c n a width k)).Reachable x y}

/-- Uniform two-point connectivity in the slabs of cubes for bond percolation of density `q`. -/
def SlabConnectivity (d : ℕ) (q : ℝ) : Prop :=
  ∃ width : ℕ, 0 < width ∧ ∃ ρ : ℝ, 0 < ρ ∧
    ∀ (c : Site d) (n : ℕ) (a : Fin d) (k : ℕ), (k + 1) * width ≤ n →
      ∀ x ∈ cubeSlab c n a width k, ∀ y ∈ cubeSlab c n a width k,
        ρ ≤ (bondPercolation d q).real {ω | xap_Reach ω (cubeSlab c n a width k) x y}

/-- Slab connectivity in the Lattice-Probability model gives slab connectivity of bond
percolation at the same density. -/
theorem slabConnectivity_of_latticeBond {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : LatticeBond.UniformCubeSlabConnectivity d ⟨q, hq0, hq1⟩) : SlabConnectivity d q := by
  obtain ⟨width, hwidth, ρ, hρ, hslab⟩ := h
  exact ⟨width, hwidth, ρ, hρ, fun c n a k hk x hx y hy =>
    (hslab c n a k hk x hx y hy).trans (latticeBondLaw_openIn_le hq0 hq1 hx)⟩

/-- Slab connectivity above the critical probability of the Lattice-Probability model, the form in
which the Grimmett–Marstrand theorem is proved for Percolation-Rigidity, gives slab connectivity
of bond percolation at every density above `bondCritical d`. -/
theorem slabConnectivity_of_gt_bondCritical [NeZero d]
    (h : ∀ p : unitInterval, LatticeBond.criticalProbability d < (p : ℝ) →
      LatticeBond.UniformCubeSlabConnectivity d p)
    {q : ℝ} (hq : bondCritical d < q) (hq1 : q ≤ 1) : SlabConnectivity d q := by
  have hq0 : 0 ≤ q := (xap14_bondCritical_nonneg d).trans hq.le
  exact slabConnectivity_of_latticeBond hq0 hq1
    (h ⟨q, hq0, hq1⟩ (criticalProbability_lt_of_bondCritical_lt hq hq1))

end Exploding
