/-
Two concrete steps toward the frozen statement.

*Infinite cluster.*  The good cluster of the origin is finite exactly when it is
bounded in `mnorm` (`xap15_smallCluster_iff_bounded`); equivalently, an infinite
good cluster has good sites at every distance
(`xap15_not_smallCluster_unbounded`).  A good star-walk always realises an open
path (`xap15_goodWalk_reachable`).

*Box-crossing framework.*  An open left-right crossing of a box is defined as an
open chain staying inside the box joining the two faces
(`xap15_OpenCrosses`); the missing box-crossing half of the supercritical
reduction is isolated as `xap15_BoxCrossing`, the statement that the probability
of such a crossing tends to one at every density above `bondCritical d`.
-/
import Exploding.Support.ExtAPProof14

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology

namespace Exploding

variable {d : ℕ}

/-! ### The good cluster is finite iff it is bounded -/

/-- A good cluster contained in a ball is finite. -/
theorem xap15_smallCluster_of_bounded {ω : Site d × Fin d → Bool} (n : ℕ)
    (h : ∀ z, xap3_GoodConnected ω z → mnorm z ≤ (n : ℤ)) : xap5_SmallCluster ω := by
  rw [xap5_SmallCluster]
  refine Set.Finite.subset ((xap11_ball d n).finite_toSet) (fun z hz => ?_)
  show z ∈ xap11_ball d n
  rw [xap11_ball, Fintype.mem_piFinset]
  intro i
  have hzi : |z i| ≤ mnorm z := Finset.single_le_sum (f := fun j => |z j|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have := h z hz
  rw [Finset.mem_Icc]
  exact abs_le.mp (hzi.trans this)

/-- A finite good cluster is bounded in `mnorm`. -/
theorem xap15_bounded_of_smallCluster {ω : Site d × Fin d → Bool} (h : xap5_SmallCluster ω) :
    ∃ n : ℕ, ∀ z, xap3_GoodConnected ω z → mnorm z ≤ (n : ℤ) := by
  rw [xap5_SmallCluster] at h
  obtain ⟨a, ha⟩ := Set.Finite.bddAbove (h.image mnorm)
  by_cases hne : ({z : Site d | xap3_GoodConnected ω z}).Nonempty
  · obtain ⟨z0, hz0⟩ := hne
    have hz0a : mnorm z0 ≤ a := ha ⟨z0, hz0, rfl⟩
    have haz : 0 ≤ a := le_trans (Finset.sum_nonneg (fun i _ => abs_nonneg (z0 i))) hz0a
    refine ⟨a.toNat, fun z hz => ?_⟩
    rw [Int.toNat_of_nonneg haz]
    exact ha ⟨z, hz, rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨0, fun z hz => absurd (hne ▸ hz) (Set.notMem_empty z)⟩

/-- The good cluster of the origin is finite exactly when it is bounded in
`mnorm`. -/
theorem xap15_smallCluster_iff_bounded {ω : Site d × Fin d → Bool} :
    xap5_SmallCluster ω ↔ ∃ n : ℕ, ∀ z, xap3_GoodConnected ω z → mnorm z ≤ (n : ℤ) :=
  ⟨xap15_bounded_of_smallCluster, fun ⟨n, hn⟩ => xap15_smallCluster_of_bounded n hn⟩

/-- An infinite good cluster has good sites at every distance. -/
theorem xap15_not_smallCluster_unbounded {ω : Site d × Fin d → Bool} (h : ¬ xap5_SmallCluster ω)
    (n : ℕ) : ∃ z : Site d, xap3_GoodConnected ω z ∧ (n : ℤ) < mnorm z := by
  by_contra hc
  push Not at hc
  exact h (xap15_smallCluster_of_bounded n fun z hz => hc z hz)

/-! ### A good star-walk realises an open path -/

/-- Every good star-walk is an open path. -/
theorem xap15_goodWalk_reachable {ω : Site d × Fin d → Bool} {a b : Site d}
    (p : (xap2_kingGraph d).Walk a b) (hp : ∀ z ∈ p.support, xap_Good ω z) :
    (openBondGraph ω).Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | cons h p' ih =>
      exact (xap_open_reach_of_star (hp _ (SimpleGraph.Walk.start_mem_support _)) h).trans
        (ih (fun z hz => hp z (by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ hz)))

/-! ### Open crossings of a box -/

/-- An open left-right crossing of the box `xap11_ball d n` in direction `i`: an
open chain, all of whose sites stay in the box, joining a site of `i`-coordinate
`-n` to a site of `i`-coordinate `n`. -/
def xap15_OpenCrosses (d n : ℕ) (i : Fin d) (ω : Site d × Fin d → Bool) : Prop :=
  ∃ x y : Site d, x i = -(n : ℤ) ∧ y i = (n : ℤ) ∧
    x ∈ xap11_ball d n ∧ y ∈ xap11_ball d n ∧
    Relation.ReflTransGen
      (fun a b => (openBondGraph ω).Adj a b ∧ a ∈ xap11_ball d n ∧ b ∈ xap11_ball d n) x y

theorem xap15_openCrosses_mono {n : ℕ} {i : Fin d} {ω ω' : Site d × Fin d → Bool}
    (h : ∀ a b, (openBondGraph ω).Adj a b → (openBondGraph ω').Adj a b)
    (hc : xap15_OpenCrosses d n i ω) : xap15_OpenCrosses d n i ω' := by
  obtain ⟨x, y, hx, hy, hxb, hyb, hpath⟩ := hc
  exact ⟨x, y, hx, hy, hxb, hyb,
    xap_rtg_mono (fun a b hab => ⟨h a b hab.1, hab.2.1, hab.2.2⟩) hpath⟩

/-- The box-crossing half of the supercritical-density reduction: for every
density above the critical one, a large box has an open left-right crossing with
probability tending to one.  Combined with a block argument it transports the
high-density estimate down to `bondCritical d`. -/
def xap15_BoxCrossing (d : ℕ) : Prop :=
  ∀ q : ℝ, bondCritical d < q → q ≤ 1 → ∀ i : Fin d,
    Filter.Tendsto (fun n : ℕ => bondPercolation d q {ω | xap15_OpenCrosses d n i ω})
      Filter.atTop (𝓝 1)

end Exploding
