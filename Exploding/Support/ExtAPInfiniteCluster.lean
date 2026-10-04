/-
The infinite-cluster half of the chemical-distance estimate.

The corrected infinite-cluster bound `Exploding.xap13_InfiniteClusterBound` bounds
`P (¬ SmallCluster ∧ BigDistance)` by `exp (-c |y|)`, where `BigDistance` is the
event that the open distance from the origin to `y` is finite and exceeds
`ρ |y|`.  This is the half complementary to the finite-cluster half.

The infinite-cluster event is genuinely different from the old formulation in
`xap12_InfiniteClusterBound`, which used `ShortWalkFails` instead of `BigDistance`.
On the infinite good cluster the origin is good (`xmi_good_of_not_smallCluster`)
and its open cluster is infinite (`xmi_openCluster_infinite_of_not_smallCluster`),
so the obstruction of the finite half — a bad origin with no good walk at all —
is absent; but `ShortWalkFails` alone is far too weak, because it also holds for
every `y` outside the good cluster, an event of positive probability.  Passing to
`BigDistance`, which also demands finite open distance, removes both obstructions;
what remains is exactly the chemical-distance large deviation of
Antal--Pisztora, isolated here as `xmi_OpenDistanceLargeDeviation`.

The file also proves that the full high-density bound is equivalent to the
conjunction of the two corrected halves (`xmi_highDensity_iff_bounds`), so the
infinite half is precisely the missing complement and cannot be dropped.
-/
import Exploding.Support.ExtAPProof18

open Exploding LatticeProb MeasureTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-! ### Elementary structure of the infinite good cluster -/

/-- If the good cluster of the origin is infinite then the origin is good: a bad
origin makes the good cluster empty, hence finite. -/
theorem xmi_good_of_not_smallCluster {ω : Site d × Fin d → Bool}
    (h : ¬ xap5_SmallCluster ω) : xap_Good ω (0 : Site d) := by
  by_contra hb
  exact h (xap13_not_good_zero_smallCluster hb)

/-- The open cluster of the origin is infinite whenever the good cluster is, since
the good cluster is contained in the open cluster. -/
theorem xmi_openCluster_infinite_of_not_smallCluster {ω : Site d × Fin d → Bool}
    (h : ¬ xap5_SmallCluster ω) :
    {x : Site d | (openBondGraph ω).Reachable (0 : Site d) x}.Infinite :=
  Set.Infinite.mono xap14_goodCluster_subset_openCluster h

/-- On the infinite-cluster event a large chemical distance still forces the origin
and `y` to be open-connected. -/
theorem xmi_reachable_of_not_smallCluster_bigDistance {ρ : ℝ}
    {ω : Site d × Fin d → Bool} {y : Site d}
    (h : ¬ xap5_SmallCluster ω ∧ xap12_BigDistance d ρ ω y) :
    (openBondGraph ω).Reachable (0 : Site d) y :=
  xap14_bigDistance_reachable h.2

/-- An infinite good cluster contains a good star-walk of length greater than `L`
for every `L`. -/
theorem xmi_infiniteCluster_longWalk (hd : 1 ≤ d) {ω : Site d × Fin d → Bool}
    (h : ¬ xap5_SmallCluster ω) (L : ℕ) :
    ∃ z : Site d, xap3_GoodConnected ω z ∧
      ∃ p : (xap2_kingGraph d).Walk (0 : Site d) z,
        (∀ w ∈ p.support, xap_Good ω w) ∧ L < p.length :=
  xap17_infiniteCluster_longWalk hd h L

/-! ### The corrected event sits inside the old `ShortWalkFails` event -/

/-- If `y` is not good-connected to the origin then no good star-walk to `y`
exists, so `ShortWalkFails` holds for every detour ratio. -/
theorem xmi_shortWalkFails_of_not_goodConnected {ρ : ℝ} {ω : Site d × Fin d → Bool}
    {y : Site d} (h : ¬ xap3_GoodConnected ω y) : xap12_ShortWalkFails d ρ ω y := by
  rintro ⟨p, hgood, _⟩
  exact h ⟨p, hgood⟩

/-- On the infinite good cluster, `y` outside the good cluster is the analogue of a
bad origin: it lies in the old `ShortWalkFails` event for every detour ratio, while
`BigDistance` fails because there is no open path to `y` at all.  This is why the
old `xap12_InfiniteClusterBound` is not the right infinite-cluster statement. -/
theorem xmi_not_goodConnected_subset_shortWalkFails {ρ : ℝ} {ω : Site d × Fin d → Bool}
    {y : Site d} (h : ¬ xap5_SmallCluster ω ∧ ¬ xap3_GoodConnected ω y) :
    ¬ xap5_SmallCluster ω ∧ xap12_ShortWalkFails d ρ ω y :=
  ⟨h.1, xmi_shortWalkFails_of_not_goodConnected h.2⟩

/-- The corrected infinite-cluster event `¬SmallCluster ∧ BigDistance` is contained
in the old `¬SmallCluster ∧ ShortWalkFails` event, because a large open distance
forbids short good star-walks.  Hence the old bound, if it held, would imply the
corrected one; the converse fails at densities where the good cluster can be
infinite while `y` stays outside it. -/
theorem xmi_infiniteClusterBound_of_shortWalkFails (h : xap12_InfiniteClusterBound) :
    xap13_InfiniteClusterBound := by
  intro d hd
  obtain ⟨q0, hq0, hq⟩ := h d hd
  refine ⟨q0, hq0, fun q hqq hq1 => ?_⟩
  obtain ⟨ρ, c, hρ, hc, R, hR⟩ := hq q hqq hq1
  exact ⟨ρ, c, hρ, hc, R, fun y hy => by
    have hsub : {ω : Site d × Fin d → Bool | ¬ xap5_SmallCluster ω ∧ xap12_BigDistance d ρ ω y}
        ⊆ {ω | ¬ xap5_SmallCluster ω ∧ xap12_ShortWalkFails d ρ ω y} :=
      fun _ hω => ⟨hω.1, xap12_bigDistance_subset_shortWalkFails hω.2⟩
    exact (measure_mono hsub).trans (hR y hy)⟩

/-! ### The missing large-deviation input -/

/-- The exact input missing from the good-site count: the high-density
chemical-distance large deviation, i.e. the statement that the open distance
from `0` to `y` exceeds `ρ |y|` only with probability exponentially small in
`|y|`, for `q` close enough to one.  The good-site Peierls estimate bounds only
`P (SmallCluster)`, a constant in `y`. -/
def xmi_OpenDistanceLargeDeviation : Prop := xap12_HighDensityBound

/-- The corrected infinite-cluster bound follows from the open-distance large
deviation, since `¬SmallCluster ∧ BigDistance` is contained in `BigDistance`. -/
theorem xmi_infiniteClusterBound_of_largeDeviation (h : xmi_OpenDistanceLargeDeviation) :
    xap13_InfiniteClusterBound := by
  intro d hd
  obtain ⟨q0, hq0, hq⟩ := h d hd
  refine ⟨q0, hq0, fun q hqq hq1 => ?_⟩
  obtain ⟨ρ, c, hρ, hc, R, hR⟩ := hq q hqq hq1
  exact ⟨ρ, c, hρ, hc, R, fun y hy =>
    (measure_mono fun _ hω => hω.2).trans (hR y hy)⟩

/-- The corrected infinite-cluster bound from the named high-density bound on the
open distance (`xap12_HighDensityBound`), which is the sharpest named input that
implies it: the infinite-cluster event is a sub-event of the `BigDistance` event,
and no sharper named statement is available -- the Peierls count controls only the
finite cluster, and the old `ShortWalkFails` formulation contains the
constant-probability event that `y` lies outside the infinite good cluster. -/
theorem xmi_infiniteClusterBound_of_highDensity (h : xap12_HighDensityBound) :
    xap13_InfiniteClusterBound :=
  xmi_infiniteClusterBound_of_largeDeviation h

/-- The frozen Antal--Pisztora node supplies the missing large deviation, because
the density range of the corrected bound lies above `bondCritical d`. -/
theorem xmi_largeDeviation_of_antalPisztora
    (h : Exploding.External.AntalPisztoraChemicalDistance) : xmi_OpenDistanceLargeDeviation := by
  intro d hd
  exact ⟨bondCritical d, xap13_bondCritical_lt_one hd, fun q hq hq1 => h d hd q hq hq1⟩

/-- The corrected infinite-cluster bound, conditional on the frozen Antal--Pisztora
node. -/
theorem xmi_infiniteClusterBound_of_antalPisztora
    (h : Exploding.External.AntalPisztoraChemicalDistance) : xap13_InfiniteClusterBound :=
  xmi_infiniteClusterBound_of_largeDeviation (xmi_largeDeviation_of_antalPisztora h)

/-! ### The full bound is the two corrected halves -/

/-- The full high-density bound implies the finite-cluster half, by monotonicity. -/
theorem xmi_finiteClusterBound_of_highDensity (h : xap12_HighDensityBound) :
    xap13_FiniteClusterBound := by
  intro d hd
  obtain ⟨q0, hq0, hq⟩ := h d hd
  refine ⟨q0, hq0, fun q hqq hq1 => ?_⟩
  obtain ⟨ρ, c, hρ, hc, R, hR⟩ := hq q hqq hq1
  exact ⟨ρ, c, hρ, hc, R, fun y hy =>
    (measure_mono fun _ hω => hω.2).trans (hR y hy)⟩

/-- The high-density bound is exactly the conjunction of the two corrected
halves: each half is a subset of the `BigDistance` event, and conversely the two
halves cover it.  Thus the infinite half is the missing complement of the finite
half and cannot be dropped from the assembly. -/
theorem xmi_highDensity_iff_bounds :
    xap12_HighDensityBound ↔ xap13_FiniteClusterBound ∧ xap13_InfiniteClusterBound := by
  constructor
  · intro h
    exact ⟨xmi_finiteClusterBound_of_highDensity h,
      xmi_infiniteClusterBound_of_largeDeviation h⟩
  · rintro ⟨hf, hi⟩
    exact xap13_highDensity_of_bounds hf hi

/-- The missing high-density large deviation is exactly the conjunction of the two
corrected halves, so it is not a separate hypothesis: it is what the finite and
infinite halves together produce. -/
theorem xmi_largeDeviation_iff_bounds :
    xmi_OpenDistanceLargeDeviation ↔
      xap13_FiniteClusterBound ∧ xap13_InfiniteClusterBound :=
  xmi_highDensity_iff_bounds

end Exploding
