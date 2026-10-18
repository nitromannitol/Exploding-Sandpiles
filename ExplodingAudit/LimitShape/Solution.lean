import Mathlib
import Exploding.Frozen.LimitShape
import ExplodingAudit.LimitShape.SolutionBasic
import ExplodingAudit.Support.LimitShapeBridge

/-!
# Solution: `LimitShape` (limit shape of exploding sandpiles)

The challenge module `ExplodingAudit/LimitShape/Challenge.lean` imports only Mathlib and states
`limit_shape` with one intentional `sorry`.  This solution imports the repository `Exploding`
together with `ExplodingAudit.LimitShape.SolutionBasic`, a verbatim copy of the challenge's
statement vocabulary, and proves the byte-identical statement from
`Exploding.Frozen.limit_shape` (`Exploding/Frozen/LimitShape.lean`).

The transport is definitional.  The audit vocabulary (`toyLaw`, `podo`, `explodingPile`,
`nearestSite`, and the four cited results `LiggettSchonmannStaceyBoundedDegree`,
`MathieuHoleVolume`, `AntalPisztoraChemicalDistance`, `SchonmannBootstrap`, with everything
they mention) is a token-for-token copy of the repository's, so each hypothesis and the
conclusion of the library theorem are definitionally equal to the audit's; the identifications
are recorded as `rfl` lemmas in `ExplodingAudit/Support/LimitShapeBridge.lean`.  The
vocabulary has no `structure`, so no field-by-field repacking is needed.  The odometers `podo`
and `spanOdo` are defined by structural recursion on time, and Lean's smart unfolding does not
unfold them at a variable time, so the proof runs with `smartUnfolding` off; this changes how
the two copies are compared, not what is stated.
-/

open MeasureTheory Filter

namespace Exploding
namespace StatementAudit
namespace LimitShape

/-- **Theorem 1.2** (`exploding.tex:246-254`, label `theorem:limit_shape`): for `d ≥ 2` and
`0 < p < 1`, there is a convex open nonempty set `B ⊆ ℝ^d`, bound before the random background
`η` drawn from the law `toyLaw d p`, such that almost surely the symmetric difference of `B` with
the rescaled support `{y : 0 < v_t([t y])}` of the odometer `v_t` of the exploding sandpile
`η + M_η δ₀` has Lebesgue measure tending to `0` as `t → ∞`.  The four cited results enter as
explicit hypotheses. -/
theorem limit_shape (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : LiggettSchonmannStaceyBoundedDegree)
    (hHole : MathieuHoleVolume)
    (hChem : AntalPisztoraChemicalDistance)
    (hSch : SchonmannBootstrap) :
    ∃ B : Set (Fin d → ℝ),
      Convex ℝ B ∧ IsOpen B ∧ B.Nonempty ∧
      ∀ᵐ η ∂(toyLaw d p),
        Tendsto
          (fun t : ℕ =>
            volume (symmDiff
              {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} B))
          atTop (nhds 0)
:= by
  set_option smartUnfolding false in
  exact Exploding.Frozen.limit_shape d hd p hp hp1.le hLSSB hHole hChem hSch

end LimitShape
end StatementAudit
end Exploding
