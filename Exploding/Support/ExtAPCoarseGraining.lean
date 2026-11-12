/-
The box-crossing coarse-graining input.

The named input `Exploding.xmj_BoxCrossingCoarseGraining` asserts that, at every
density above `bondCritical d`, the box crossings imply the exponential upper tail
of the chemical distance.  This file shows that the input is not a reduction of the
Antal--Pisztora statement `Exploding.External.AntalPisztoraChemicalDistance` to anything
simpler.

Write `BC d` for `Exploding.xap15_BoxCrossing d` and `AP` for the Antal--Pisztora statement.
The statement is `∀ d, 2 ≤ d → AP d`, where `AP d` is its statement at dimension `d`
(a tail bound at every density above `bondCritical d`), and the coarse-graining
input is exactly `∀ d, 2 ≤ d → BC d → AP d`.  Hence

* the Antal--Pisztora statement implies the coarse-graining input, the box-crossing
  hypothesis being discarded;
* box crossing and the coarse-graining input together imply the Antal--Pisztora statement;
* consequently, once box crossing is available in every dimension, the
  coarse-graining input is *equivalent* to the Antal--Pisztora statement.  Since box
  crossing is itself equivalent to the RSW extension `xmj2_SupercriticalCrossingExtension`,
  the same equivalence holds with either hypothesis.  Proving the coarse-graining is
  therefore proving the Antal--Pisztora statement; it isolates no smaller statement.
-/
import Exploding.Support.ExtAPBoxCrossingSupercritical

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-! ### The coarse-graining input and the Antal--Pisztora statement under box crossing -/

/-- The coarse-graining input follows from the Antal--Pisztora statement: the
box-crossing hypothesis is simply discarded. -/
theorem xmy_coarseGraining_of_antalPisztora
    (h : Exploding.External.AntalPisztoraChemicalDistance) :
    xmj_BoxCrossingCoarseGraining :=
  fun d _hd _hbc => h d _hd

/-- Box crossing and the coarse-graining input together give the Antal--Pisztora statement. -/
theorem xmy_antalPisztora_of_boxCrossing_coarseGraining
    (hbc : ∀ d : ℕ, 2 ≤ d → xap15_BoxCrossing d)
    (hcg : xmj_BoxCrossingCoarseGraining) :
    Exploding.External.AntalPisztoraChemicalDistance :=
  fun d hd => hcg d hd (hbc d hd)

/-- **The coarse-graining input is exactly the Antal--Pisztora statement once box crossing is
available.**  Under box crossing in every dimension the two statements are
equivalent, so the coarse-graining input does not reduce the Antal--Pisztora statement to a
weaker claim. -/
theorem xmy_coarseGraining_iff_antalPisztora_of_boxCrossing
    (hbc : ∀ d : ℕ, 2 ≤ d → xap15_BoxCrossing d) :
    xmj_BoxCrossingCoarseGraining ↔ Exploding.External.AntalPisztoraChemicalDistance :=
  ⟨xmy_antalPisztora_of_boxCrossing_coarseGraining hbc, xmy_coarseGraining_of_antalPisztora⟩

/-- The same equivalence with box crossing replaced by the RSW extension, which is
equivalent to it. -/
theorem xmy_coarseGraining_iff_antalPisztora_of_extension
    (hext : ∀ d : ℕ, 2 ≤ d → xmj2_SupercriticalCrossingExtension d) :
    xmj_BoxCrossingCoarseGraining ↔ Exploding.External.AntalPisztoraChemicalDistance :=
  xmy_coarseGraining_iff_antalPisztora_of_boxCrossing
    (fun d hd => xmx_boxCrossing_of_extension d hd (hext d hd))

/-- The supercritical reduction assembled from box crossing and the coarse-graining
input; by the equivalence above this is the Antal--Pisztora statement in another form and
adds nothing to its direct use. -/
theorem xmy_supercriticalReduction_of_boxCrossing_coarseGraining
    (hbc : ∀ d : ℕ, 2 ≤ d → xap15_BoxCrossing d)
    (hcg : xmj_BoxCrossingCoarseGraining) :
    xap12_SupercriticalReduction :=
  fun _ => xmy_antalPisztora_of_boxCrossing_coarseGraining hbc hcg

end Exploding
