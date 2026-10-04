# Hand triage of the systematic Exploding audit (2026-10-03)

Triages the flags of `~/fleet/runs/exploding-sandpiles-audit/` (DeepSeek-V4.1-flash, 58 lenses,
`AUDIT-DONE`) against the frozen Lean and `paper/exploding.tex`. The reader is fallible; nothing
frozen is edited here. No statement is refuted; the items below are fidelity notes.

## Registered `External.*` hypotheses — intended design, not defects

The audit's repeated "DEFECT: the Lean adds external hypotheses not in the paper" applies to
`thm-generalized-convergence` / `thm-counterexample` / `prop-box-crossing` (and the batch-A nodes):
the binders are `Exploding.External.{LiggettSchonmannStacey, LiggettSchonmannStaceyBoundedDegree,
MathieuHoleVolume, AntalPisztoraChemicalDistance, FeyMeesterRedigLeastAction, SchonmannBootstrap,
Schauder}`, every one a registered `FROZEN` node of `ledger/manifest.yaml`. Carrying a cited input
explicitly is the intended design; fidelity of each carried `Prop` is EXTERNALS-to-zero work.

## `hlow` / `hhigh` are the model's standing range

`lem-local-convexity` and `lem-last-wave-bound` assume `2d-2 ≤ η x ≤ 2d-1`. The model's law is
`toyLaw d p = productLaw d (2d-1) (2d-2) p` (`Exploding/Support/Vocab.lean:220`), whose support is
exactly `{2d-2, 2d-1}`. The Lean states the lemma for the model's own range, as the paper's proof
does ("by monotonicity of parallel toppling, we may take `η = 2d-2`"). Not a defect.

## `lem-last-wave-bound` — faithful

The Lean states the paper's display `u_t^{(z)}(x) ≤ 1 + ũ^{(z)}(x)`. The lemma's first sentence
("bounded by one outside the interior of the penultimate-cluster") is the case `x` outside the
penultimate cluster of that same inequality, since `penultimateWave` vanishes there. The audit's
"omits the first sentence" is therefore a false positive.

## `lem-finite-exploding` — owner review (partial transcription)

The paper's lemma says "The last-wave is well-defined, `\hat M_η(0) < ∞`". The Lean conclusion is
`∀ᵐ η ∂(toyLaw d p), ∃ n ≥ 1, ¬ WaveStabilizable η n 0`: it captures the well-definedness of the
last wave (existence of a non-stabilising wave) but **does not assert `\hat M_η(0) < ∞`**. This is
the one item that may need an erratum or a companion node; it is recorded for the owner and not
self-edited. It is a weakening, not a soundness error.

## `thm-time-constant` — benign explicit rendering (flagged for the owner)

The Lean adds `Explosive η ∧ ∀ x, arrival η x ≠ ⊤` inside the a.s. event. `Explosive η` is the a.s.
content of the `hFLP` hypothesis itself (`Exploding/External/FeyLevinePeres.lean:19`), and the
finiteness of the rescaled arrival times is implicit in their convergence to the paper's finite
`N_p`. Recorded for the owner, not a confirmed defect.

## Vacuity lens

Every batch reported "no real vacuity risk"; the B reports explicitly check the only candidates
(`toyLaw` is a probability measure; `hlast` is satisfiable; the `δ ≥ 1` edge of `prop-crossing-time`
is inherited from the paper).

## Infrastructure

`tools/check_clauses.py` and `tools/check_exponents.py` match the stale `rotor.tex` stem, so both
gates inspect nothing while `verify.py` reports them green; their `REVIEWED`/`EXPECTED_ABSENT`
tables are empty. A separate packet is needed to populate them and derive the stem from the paper
path.

## Consequence

All `SEALED` nodes are proved and non-vacuous; the transcription flags are registered Externals,
the model's standing range, or the two owner-review items above (`lem-finite-exploding`'s missing
`\hat M_η(0) < ∞` and `thm-time-constant`'s explicit rendering). No proof is refuted.
