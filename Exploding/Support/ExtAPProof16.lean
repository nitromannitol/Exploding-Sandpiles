/-
Structural steps for the infinite-cluster case and the crossing interface.

The good cluster of the origin is `*`-connected: any two good-connected sites are
joined by a good star-walk (`xap16_goodConnected_connected`).  Consequently the
boundary of the good cluster (sites outside it adjacent to it) is all bad
(`xap16_boundary_allBad`), and is the natural separator of the finite-cluster
case.

On the box-crossing side, an open crossing realises an open reachable pair across
the box (`xap16_openCrosses_reachable`), and a good star-crossing gives such an
open reachable pair (`xap16_goodCrosses_reachable`).  The box-crossing
probability tends to one above `bondCritical d` (`xap15_BoxCrossing`); the
high-density half, where the good cubes percolate, is what a Peierls argument can
reach, while the full supercritical statement needs RSW / uniqueness of the
infinite cluster and is not formalised here.
-/
import Exploding.Support.ExtAPProof15

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology

namespace Exploding

variable {d : ℕ}

/-! ### The good cluster is `*`-connected -/

/-- Appending one star-step of a good site keeps good connectivity. -/
theorem xap16_goodConnected_star {ω : Site d × Fin d → Bool} {c z : Site d}
    (hc : xap3_GoodConnected ω c) (hz : xap_Good ω z) (hcz : xap_Star c z) :
    xap3_GoodConnected ω z := by
  obtain ⟨p, hp⟩ := hc
  refine ⟨p.append (SimpleGraph.Walk.cons hcz SimpleGraph.Walk.nil), ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
  rcases hw with hw | hw
  · exact hp w hw
  · rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
      List.mem_singleton] at hw
    rw [hw]; exact hz

/-- The good cluster of the origin is `*`-connected. -/
theorem xap16_goodConnected_connected {ω : Site d × Fin d → Bool} {y z : Site d}
    (hy : xap3_GoodConnected ω y) (hz : xap3_GoodConnected ω z) :
    ∃ p : (xap2_kingGraph d).Walk y z, ∀ w ∈ p.support, xap_Good ω w := by
  obtain ⟨py, hpy⟩ := hy
  obtain ⟨pz, hpz⟩ := hz
  refine ⟨py.reverse.append pz, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
  rcases hw with hw | hw
  · exact hpy w (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw)
  · exact hpz w (List.mem_of_mem_tail hw)

/-- If the good cluster is finite and nonempty, some site of its boundary is
adjacent to it: maximise the `i`-th coordinate over the cluster and step one past
it. -/
theorem xap16_boundary_nonempty {ω : Site d × Fin d → Bool} (i : Fin d)
    (hne : ({z : Site d | xap3_GoodConnected ω z}).Nonempty) (hfin : xap5_SmallCluster ω) :
    ∃ z, z ∉ {z : Site d | xap3_GoodConnected ω z} ∧
      ∃ c, xap3_GoodConnected ω c ∧ xap_Star c z := by
  obtain ⟨c, hc, hmax⟩ := hfin.toFinset.exists_max_image (fun z : Site d => z i)
    (hfin.toFinset_nonempty.mpr hne)
  have hc' : xap3_GoodConnected ω c := hfin.mem_toFinset.mp hc
  refine ⟨c + unit i, ?_, c, hc', ?_⟩
  · intro hmem
    have hle := hmax (c + unit i) (hfin.mem_toFinset.mpr hmem)
    rw [Pi.add_apply, unit, Pi.single_eq_same] at hle
    omega
  · have hne' : c ≠ c + unit i := by
      intro h
      have hthis : c - c = (c + unit i) - c := congrArg (fun w : Site d => w - c) h
      have : (unit i : Site d) = 0 := by simpa using hthis.symm
      exact unit_ne_zero i this
    refine ⟨hne', fun j => ?_⟩
    have hsub : c j - (c + unit i) j = -(unit i : Site d) j := by
      rw [Pi.add_apply]; ring
    rw [hsub, abs_neg, unit, Pi.single_apply]
    split_ifs <;> norm_num

/-- A site outside the good cluster adjacent to it is bad. -/
theorem xap16_boundary_allBad {ω : Site d × Fin d → Bool} {z : Site d}
    (hz : ¬ xap3_GoodConnected ω z)
    (h : ∃ c, xap3_GoodConnected ω c ∧ xap_Star c z) : ¬ xap_Good ω z := by
  rintro hg
  obtain ⟨c, hc, hcz⟩ := h
  exact hz (xap16_goodConnected_star hc hg hcz)

/-! ### The crossing interface -/

/-- An open crossing gives an open reachable pair across the box. -/
theorem xap16_openCrosses_reachable {n : ℕ} {i : Fin d} {ω : Site d × Fin d → Bool}
    (h : xap15_OpenCrosses d n i ω) :
    ∃ x y : Site d, x i = -(n : ℤ) ∧ y i = (n : ℤ) ∧ (openBondGraph ω).Reachable x y := by
  obtain ⟨x, y, hx, hy, _, _, hpath⟩ := h
  exact ⟨x, y, hx, hy,
    (SimpleGraph.reachable_iff_reflTransGen x y).mpr
      (xap_rtg_mono (fun _ _ hab => hab.1) hpath)⟩

/-- A good star-crossing of the box. -/
def xap16_GoodCrosses (d n : ℕ) (i : Fin d) (ω : Site d × Fin d → Bool) : Prop :=
  ∃ x y : Site d, x i = -(n : ℤ) ∧ y i = (n : ℤ) ∧
    x ∈ xap11_ball d n ∧ y ∈ xap11_ball d n ∧
    ∃ p : (xap2_kingGraph d).Walk x y,
      (∀ z ∈ p.support, xap_Good ω z) ∧ (∀ z ∈ p.support, z ∈ xap11_ball d n)

/-- A good star-crossing of the box gives an open reachable pair across it. -/
theorem xap16_goodCrosses_reachable {n : ℕ} {i : Fin d} {ω : Site d × Fin d → Bool}
    (h : xap16_GoodCrosses d n i ω) :
    ∃ x y : Site d, x i = -(n : ℤ) ∧ y i = (n : ℤ) ∧ (openBondGraph ω).Reachable x y := by
  obtain ⟨x, y, hx, hy, _, _, p, hp, _⟩ := h
  exact ⟨x, y, hx, hy, xap15_goodWalk_reachable p hp⟩

end Exploding
