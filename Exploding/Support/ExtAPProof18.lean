/-
The good cluster as a countable union of finite approximants.

`xap18_GoodBall M` is the set of sites reachable from the origin by a good
star-walk of length at most `M`.  These sets increase with `M`, lie in the good
cluster, and exhaust it.  By `xap17_walk_mnorm_le` every good ball lies in a
finite `mnorm` ball, so each `xap18_GoodBall M` is finite; hence a good cluster
equal to one of them is finite.  This is the filtration the finite-cluster
Peierls count needs, and it shows an infinite good cluster is not trapped by any
finite cut-off.
-/
import Exploding.Support.ExtAPProof17

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology

namespace Exploding

variable {d : ℕ}

/-- The good sites reachable from the origin by a good star-walk of length at
most `M`. -/
def xap18_GoodBall (d : ℕ) (M : ℕ) (ω : Site d × Fin d → Bool) : Set (Site d) :=
  {z | ∃ p : (xap2_kingGraph d).Walk (0 : Site d) z,
    (∀ w ∈ p.support, xap_Good ω w) ∧ p.length ≤ M}

theorem xap18_goodBall_mono {M M' : ℕ} (h : M ≤ M') {ω : Site d × Fin d → Bool} :
    xap18_GoodBall d M ω ⊆ xap18_GoodBall d M' ω := by
  rintro z ⟨p, hp, hlen⟩
  exact ⟨p, hp, le_trans hlen h⟩

theorem xap18_goodBall_subset {M : ℕ} {ω : Site d × Fin d → Bool} :
    xap18_GoodBall d M ω ⊆ {z : Site d | xap3_GoodConnected ω z} := by
  rintro z ⟨p, hp, _⟩
  exact ⟨p, hp⟩

/-- The good cluster is the union of its finite good balls. -/
theorem xap18_goodConnected_eq_iUnion {ω : Site d × Fin d → Bool} :
    {z : Site d | xap3_GoodConnected ω z} = ⋃ M : ℕ, xap18_GoodBall d M ω := by
  ext z
  constructor
  · rintro ⟨p, hp⟩
    exact Set.mem_iUnion.2 ⟨p.length, p, hp, le_rfl⟩
  · intro hz
    obtain ⟨M, hM⟩ := Set.mem_iUnion.1 hz
    exact xap18_goodBall_subset hM

/-- Every good ball lies in a finite `mnorm` ball. -/
theorem xap18_goodBall_subset_ball {M : ℕ} {ω : Site d × Fin d → Bool} :
    xap18_GoodBall d M ω ⊆ {z : Site d | mnorm z ≤ (d * M : ℕ)} := by
  rintro z ⟨p, hp, hlen⟩
  have h0 : mnorm (0 : Site d) = 0 := by simp [mnorm]
  have hwalk := xap17_walk_mnorm_le p
  rw [h0, zero_add] at hwalk
  have hlen' : ((p.length : ℕ) : ℤ) ≤ (M : ℤ) := by exact_mod_cast hlen
  have : mnorm z ≤ ((d * M : ℕ) : ℤ) := by
    have h1 : (d : ℤ) * (p.length : ℤ) ≤ (d : ℤ) * (M : ℤ) :=
      mul_le_mul_of_nonneg_left hlen' (by positivity)
    have h2 : ((d * M : ℕ) : ℤ) = (d : ℤ) * (M : ℤ) := by push_cast; ring
    rw [h2]; linarith
  exact_mod_cast this

/-- Every good ball is finite. -/
theorem xap18_goodBall_finite (M : ℕ) (ω : Site d × Fin d → Bool) :
    (xap18_GoodBall d M ω).Finite := by
  refine Set.Finite.subset ((xap11_ball d (d * M)).finite_toSet) (fun z hz => ?_)
  show z ∈ xap11_ball d (d * M)
  rw [xap11_ball, Fintype.mem_piFinset]
  intro i
  have hzi : |z i| ≤ mnorm z := Finset.single_le_sum (f := fun j => |z j|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hz' := xap18_goodBall_subset_ball hz
  rw [Finset.mem_Icc]
  exact abs_le.mp (hzi.trans hz')

/-- A good cluster exhausted by one good ball is finite. -/
theorem xap18_smallCluster_of_eq_goodBall {ω : Site d × Fin d → Bool} {M : ℕ}
    (h : {z : Site d | xap3_GoodConnected ω z} = xap18_GoodBall d M ω) :
    xap5_SmallCluster ω := by
  rw [xap5_SmallCluster, h]
  exact xap18_goodBall_finite M ω

end Exploding
