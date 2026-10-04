/-
The finite-cluster half of the chemical-distance estimate.

The corrected finite-cluster bound `Exploding.xap13_FiniteClusterBound` bounds the
probability of `xap5_SmallCluster ∧ xap12_BigDistance` by `exp (-c |y|)`.  This file
records the exact obstacle to proving it from the good-site Peierls count.

The count `xap11_smallCluster_prob_le` bounds `P(SmallCluster)` by the geometric
series `∑_s (2s+1)^d (3^d)^{2s} (1-δ)^{s/3^d}`, a constant independent of `y`.  It
therefore cannot produce the factor `exp (-c |y|)`.  The extra input needed is the
`y`-dependent statement that a large chemical distance is rare: the
high-density chemical-distance large deviation of Antal--Pisztora.  That statement
is isolated below as `xmf_OpenDistanceLargeDeviation`; the corrected bound is a
consequence of it because `SmallCluster ∧ BigDistance ⊆ BigDistance`.

Two elementary facts about the distance are also proved.  First, a nearest-neighbour
open path of `m` steps changes the Manhattan norm by at most one per step, so the
chemical distance dominates `mnorm` (`xmf_mnorm_le_edist`).  Second, for a detour
ratio `ρ < 1` a finite chemical distance is exactly `BigDistance`; the constraint
`1 ≤ ρ` in the corrected bound is therefore essential, and the origin-bad event
alone is not enough to refute it.
-/
import Exploding.Support.ExtAPProof13
import Exploding.Support.PUBProofB

open Exploding LatticeProb MeasureTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-! ### The Manhattan norm is dominated by the chemical distance -/

/-- One nearest-neighbour step changes the Manhattan norm by at most one. -/
theorem xmf_mnorm_adj_le {u v : Site d} (h : (lattice d).Adj u v) :
    mnorm v ≤ mnorm u + 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · rw [hi]
    simpa using ec_mnorm_le_sub_unit (u + unit i) i
  · rw [hi]
    exact ec_mnorm_le_add_unit v i

/-- A nearest-neighbour open path of `p.length` steps changes the Manhattan norm by
at most one per step. -/
theorem xmf_walk_mnorm_le {ω : Site d × Fin d → Bool} {a b : Site d}
    (p : (openBondGraph ω).Walk a b) : mnorm b ≤ mnorm a + (p.length : ℤ) := by
  induction p with
  | nil => simp
  | cons h p' ih =>
      have hlat : (lattice d).Adj _ _ := xap_lattice_of_open h
      have h1 : mnorm _ ≤ mnorm _ + 1 := xmf_mnorm_adj_le hlat
      rw [SimpleGraph.Walk.length_cons]
      push_cast
      linarith [ih, h1]

/-- The chemical distance from `0` to `y` is at least `mnorm y`. -/
theorem xmf_mnorm_le_edist {ω : Site d × Fin d → Bool} {y : Site d} {m : ℕ}
    (hm : (openBondGraph ω).edist (0 : Site d) y = (m : ℕ∞)) : mnorm y ≤ (m : ℤ) := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hm
  have hwalk := xmf_walk_mnorm_le p
  rw [hp] at hwalk
  simpa [mnorm] using hwalk

/-! ### For a detour ratio below one, `BigDistance` is exactly connectivity -/

/-- For `ρ < 1` a finite chemical distance always beats `ρ |y|`: every open path
from `0` to `y` has at least `mnorm y` steps. -/
theorem xmf_bigDistance_of_edist_eq {ρ : ℝ} (hρ : ρ < 1) {ω : Site d × Fin d → Bool}
    {y : Site d} {m : ℕ} (hm : (openBondGraph ω).edist (0 : Site d) y = (m : ℕ∞))
    (hy : mnorm y > 0) : xap12_BigDistance d ρ ω y := by
  refine ⟨m, hm, ?_⟩
  have hle := xmf_mnorm_le_edist hm
  have hy' : (0 : ℤ) < mnorm y := hy
  have : ρ * (mnorm y : ℝ) < (mnorm y : ℝ) := by
    have : (0 : ℝ) < (mnorm y : ℝ) := by exact_mod_cast hy'
    nlinarith
  have hcast : (mnorm y : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
  linarith

/-! ### The missing large-deviation input -/

/-- The high-density chemical-distance large deviation: for `q` close enough to
`1`, the open distance from `0` to `y` exceeds `ρ |y|` only with probability
exponentially small in `|y|`.  This is Antal--Pisztora's Theorem 1.1 at high
density, and it is the exact input missing from the good-site Peierls count: the
count bounds `P(SmallCluster)` by a constant, and `BigDistance` does not force the
all-bad separator to grow with `|y|` (a long open corridor meeting a single bad
origin has `SmallCluster` and a chemical distance exceeding `ρ |y|`, while every
bad `*`-connected set has one site). -/
def xmf_OpenDistanceLargeDeviation : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q0 : ℝ, q0 < 1 ∧ ∀ q : ℝ, q0 < q → q ≤ 1 →
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q {ω | xap12_BigDistance d ρ ω y} ≤
        ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ))))

/-- The corrected finite-cluster bound follows from the large deviation of the
open distance, since `SmallCluster ∧ BigDistance` is contained in `BigDistance`. -/
theorem xmf_finiteClusterBound_of_openDistance (h : xmf_OpenDistanceLargeDeviation) :
    xap13_FiniteClusterBound := by
  intro d hd
  obtain ⟨q0, hq0, hq⟩ := h d hd
  refine ⟨q0, hq0, fun q hqq hq1 => ?_⟩
  obtain ⟨ρ, c, hρ, hc, R, hR⟩ := hq q hqq hq1
  exact ⟨ρ, c, hρ, hc, R,
    fun y hy => (measure_mono fun _ hω => hω.2).trans (hR y hy)⟩

/-- The frozen Antal--Pisztora node supplies the missing input, because the density
range of the corrected bound lies above `bondCritical d`. -/
theorem xmf_openDistanceLargeDeviation_of_antalPisztora
    (h : Exploding.External.AntalPisztoraChemicalDistance) :
    xmf_OpenDistanceLargeDeviation := by
  intro d hd
  exact ⟨bondCritical d, xap13_bondCritical_lt_one hd, fun q hq hq1 => h d hd q hq hq1⟩

/-- The corrected finite-cluster bound, conditional on the frozen Antal--Pisztora
node. -/
theorem xmf_finiteClusterBound_of_antalPisztora
    (h : Exploding.External.AntalPisztoraChemicalDistance) : xap13_FiniteClusterBound :=
  xmf_finiteClusterBound_of_openDistance (xmf_openDistanceLargeDeviation_of_antalPisztora h)

end Exploding
