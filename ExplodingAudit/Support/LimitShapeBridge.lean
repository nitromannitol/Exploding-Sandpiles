import Mathlib
import Exploding.Frozen.LimitShape
import ExplodingAudit.LimitShape.SolutionBasic

/-!
# Comparator bridge: `ExplodingAudit.LimitShape` vocabulary → repository

This file connects the statement-audit vocabulary of
`ExplodingAudit/LimitShape/Challenge.lean` (copied verbatim into
`ExplodingAudit/LimitShape/SolutionBasic.lean`, which imports only Mathlib) to the objects of
the repository `Exploding` and of the `lattice-probability` dependency, so that
`ExplodingAudit/LimitShape/Solution.lean` is literal gluing.

**It is imported by the `Solution` file only.**  The `Challenge` and `SolutionBasic` files
must stay Mathlib-only: a repository import inside the vocabulary changes instance
elaboration there and breaks the comparator's constant-by-constant closure check.

The audit vocabulary is already definitionally equal to the repository's: every constant is a
token-for-token copy, and `Site` is `Fin d → ℤ` on both sides.  Every bridge here is therefore
`rfl`.  There is no `structure` or `inductive` in the vocabulary, so no `Iff` that packs and
unpacks fields is needed; the four cited results are `Prop`-valued definitions, and
`Solution.lean` passes them to the repository theorem by `exact`.

The odometers `podo` and `spanOdo` are defined by structural recursion on time.  Lean's
smart unfolding does not unfold such a definition at a variable time, so identifying the two
copies of an odometer at a variable time (`podo_eq`, `spanOdo_eq`, and every statement that
quantifies over times) needs `set_option smartUnfolding false`; with it the two copies unfold
to the same recursor application and the identification is again `rfl`.
-/

namespace ExplodingAudit
namespace Support
namespace LimitShapeBridge

open MeasureTheory

set_option smartUnfolding false

/-! ## The lattice (`LatticeProb/Site.lean`) -/

theorem Site_eq (d : ℕ) :
    Exploding.StatementAudit.LimitShape.Site d = LatticeProb.Site d := rfl

theorem unit_eq {d : ℕ} (i : Fin d) :
    Exploding.StatementAudit.LimitShape.unit i = LatticeProb.unit i := rfl

theorem lattice_eq (d : ℕ) :
    Exploding.StatementAudit.LimitShape.lattice d = LatticeProb.lattice d := rfl

theorem componentIn_eq {d : ℕ} (S : Set (Fin d → ℤ)) (x : Fin d → ℤ) :
    Exploding.StatementAudit.LimitShape.componentIn S x = LatticeProb.componentIn S x := rfl

/-! ## Parallel toppling (`Exploding/Support/Toppling.lean`) -/

theorem dirac_eq {d : ℕ} (z : Fin d → ℤ) :
    Exploding.StatementAudit.LimitShape.dirac z = Exploding.dirac z := rfl

theorem nbrSumZ_eq {d : ℕ} (u : (Fin d → ℤ) → ℤ) (x : Fin d → ℤ) :
    Exploding.StatementAudit.LimitShape.nbrSumZ u x = Exploding.nbrSumZ u x := rfl

theorem lap_eq {d : ℕ} (u : (Fin d → ℤ) → ℤ) (x : Fin d → ℤ) :
    Exploding.StatementAudit.LimitShape.lap u x = Exploding.lap u x := rfl

theorem podo_eq {d : ℕ} (s0 : (Fin d → ℤ) → ℤ) (t : ℕ) (x : Fin d → ℤ) :
    Exploding.StatementAudit.LimitShape.podo s0 t x = Exploding.podo s0 t x := rfl

theorem Stabilizable_eq {d : ℕ} (s0 : (Fin d → ℤ) → ℤ) :
    Exploding.StatementAudit.LimitShape.Stabilizable s0 = Exploding.Stabilizable s0 := rfl

theorem explosionThreshold_eq {d : ℕ} (η : (Fin d → ℤ) → ℤ) :
    Exploding.StatementAudit.LimitShape.explosionThreshold η = Exploding.explosionThreshold η :=
  rfl

theorem explodingPile_eq {d : ℕ} (η : (Fin d → ℤ) → ℤ) (x : Fin d → ℤ) :
    Exploding.StatementAudit.LimitShape.explodingPile η x = Exploding.explodingPile η x := rfl

theorem nearestSite_eq {d : ℕ} (y : Fin d → ℝ) :
    Exploding.StatementAudit.LimitShape.nearestSite y = Exploding.nearestSite y := rfl

/-! ## Boxes and bootstrap percolation (`Exploding/Support/Vocab.lean`) -/

theorem cube_eq (d k : ℕ) :
    Exploding.StatementAudit.LimitShape.cube d k = Exploding.cube d k := rfl

theorem cent_eq (d n : ℕ) :
    Exploding.StatementAudit.LimitShape.cent d n = Exploding.cent d n := rfl

theorem mnorm_eq {d : ℕ} (x : Fin d → ℤ) :
    Exploding.StatementAudit.LimitShape.mnorm x = Exploding.mnorm x := rfl

theorem spanOdo_eq {d : ℕ} (n : ℕ) (η : (Fin d → ℤ) → ℤ) (t : ℕ) (x : Fin d → ℤ) :
    Exploding.StatementAudit.LimitShape.spanOdo n η t x = Exploding.spanOdo n η t x := rfl

theorem InternallySpanned_eq {d : ℕ} (η : (Fin d → ℤ) → ℤ) (n : ℕ) :
    Exploding.StatementAudit.LimitShape.InternallySpanned η n =
      Exploding.InternallySpanned η n := rfl

/-! ## The background law (`Exploding/Support/Vocab.lean`) -/

theorem chipLaw_eq (a b : ℤ) (p : ℝ) :
    Exploding.StatementAudit.LimitShape.chipLaw a b p = Exploding.chipLaw a b p := rfl

theorem productLaw_eq (d : ℕ) (a b : ℤ) (p : ℝ) :
    Exploding.StatementAudit.LimitShape.productLaw d a b p = Exploding.productLaw d a b p := rfl

theorem toyLaw_eq (d : ℕ) (p : ℝ) :
    Exploding.StatementAudit.LimitShape.toyLaw d p = Exploding.toyLaw d p := rfl

/-! ## Bernoulli percolation (`Exploding/Support/Percolation.lean`) -/

theorem bitLaw_eq (q : ℝ) :
    Exploding.StatementAudit.LimitShape.bitLaw q = Exploding.bitLaw q := rfl

theorem sitePercolation_eq (d : ℕ) (q : ℝ) :
    Exploding.StatementAudit.LimitShape.sitePercolation d q = Exploding.sitePercolation d q :=
  rfl

theorem openSites_eq {d : ℕ} (ω : (Fin d → ℤ) → Bool) :
    Exploding.StatementAudit.LimitShape.openSites ω = Exploding.openSites ω := rfl

theorem IsInfiniteOpenCluster_eq {d : ℕ} (ω : (Fin d → ℤ) → Bool) (C : Set (Fin d → ℤ)) :
    Exploding.StatementAudit.LimitShape.IsInfiniteOpenCluster ω C =
      Exploding.IsInfiniteOpenCluster ω C := rfl

theorem bondPercolation_eq (d : ℕ) (q : ℝ) :
    Exploding.StatementAudit.LimitShape.bondPercolation d q = Exploding.bondPercolation d q :=
  rfl

theorem openBondGraph_eq {d : ℕ} (ω : (Fin d → ℤ) × Fin d → Bool) :
    Exploding.StatementAudit.LimitShape.openBondGraph ω = Exploding.openBondGraph ω := rfl

theorem bondTheta_eq (d : ℕ) (q : ℝ) :
    Exploding.StatementAudit.LimitShape.bondTheta d q = Exploding.bondTheta d q := rfl

theorem bondCritical_eq (d : ℕ) :
    Exploding.StatementAudit.LimitShape.bondCritical d = Exploding.bondCritical d := rfl

theorem bernoulliProduct_eq (S : Type) (q : ℝ) :
    Exploding.StatementAudit.LimitShape.bernoulliProduct S q = Exploding.bernoulliProduct S q :=
  rfl

theorem IsIncreasingSet_eq {S : Type} (A : Set (S → Bool)) :
    Exploding.StatementAudit.LimitShape.IsIncreasingSet A = Exploding.IsIncreasingSet A := rfl

theorem HasDependenceGraph_eq {S : Type} (G : SimpleGraph S) (μ : Measure (S → Bool)) :
    Exploding.StatementAudit.LimitShape.HasDependenceGraph G μ =
      Exploding.HasDependenceGraph G μ := rfl

/-! ## The four cited results (`Exploding/External/`) -/

theorem LiggettSchonmannStaceyBoundedDegree_eq :
    Exploding.StatementAudit.LimitShape.LiggettSchonmannStaceyBoundedDegree =
      Exploding.External.LiggettSchonmannStaceyBoundedDegree := rfl

theorem MathieuHoleVolume_eq :
    Exploding.StatementAudit.LimitShape.MathieuHoleVolume =
      Exploding.External.MathieuHoleVolume := rfl

theorem AntalPisztoraChemicalDistance_eq :
    Exploding.StatementAudit.LimitShape.AntalPisztoraChemicalDistance =
      Exploding.External.AntalPisztoraChemicalDistance := rfl

theorem SchonmannBootstrap_eq :
    Exploding.StatementAudit.LimitShape.SchonmannBootstrap =
      Exploding.External.SchonmannBootstrap := rfl

end LimitShapeBridge
end Support
end ExplodingAudit
