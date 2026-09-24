# Audit Comparator Surface

This directory will hold Mathlib-only comparator challenges for the main theorems of the
formalization of *A shape theorem for exploding sandpiles* (Ahmed Bou-Rabee), in the form
used by the repositories this one follows: for each main theorem, a `Challenge.lean` that
imports only `Mathlib`, rebuilds from scratch every definition needed to read the theorem,
states it, and ends with one intentional `sorry`; a `Solution.lean` that fills it from the
library; and a `comparator.json` for
[`leanprover/comparator`](https://github.com/leanprover/comparator), which checks that the
two statements have identical elaborated types and that the proof reduces to the three
standard axioms.

**It holds none yet.**  None of the paper's main results is proved.  Theorems 1.2, 1.4 and
6.1 are registered as frozen statements whose proofs are still open.  Theorems 1.3 and 5.1
have written proofs, but those proofs use propositions that are still open, so their axiom
closures contain `sorryAx`.  A challenge whose solution rests on a `sorry` would certify
nothing, so the challenges will be added when the main theorems are sealed.  Until then there
is no `Audit` library in `lakefile.lean` and no comparator workflow.

What is proved so far is restated in full in
[`Exploding/MainTheorems.lean`](../Exploding/MainTheorems.lean), and
[`Exploding/Meta/AxiomsAudit.lean`](../Exploding/Meta/AxiomsAudit.lean) prints the axioms of
each.
