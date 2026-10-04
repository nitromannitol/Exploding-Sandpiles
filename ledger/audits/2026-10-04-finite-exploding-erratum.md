# Erratum proposal — `lem-finite-exploding` (author gate)

The independent batch-D audit (`2026-10-03-refute-first-D.md`) finds that the frozen
`lem-finite-exploding` asserts **less** than the paper's `lemma:finite_exploding`. The node was
provisionally promoted with the other 21 and is corrected here back to `SEALED` until a ruling.

## The gap

Paper (`exploding.tex:720-722`, `\label{lemma:finite_exploding}`):

> The last-wave is well-defined, `\hat M_{\eta}(0) < \infty`.

Frozen (`Exploding/Frozen/FiniteExploding.lean:31`):

```
∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)
```

The Lean statement captures the *existence* half (a wave that does not stabilise, so the last wave
is well defined) but does not assert the finiteness `\hat M_\eta(0) < \infty` of the paper's
displayed quantity. It is a recorded weakening, not a hidden one: `check_clauses.py` prints the node
as `FLAGGED`.

## Proposal (one of, for the author)

1. Add a **companion node** `lem-finite-exploding-mass` asserting `\hat M_\eta(0) < \infty` (with
   `\hat M` defined), leaving the frozen statement untouched; or
2. a **versioned successor** of `lem-finite-exploding` whose a.e. conclusion conjoins the finiteness
   clause, on the erratum path (`tools/freeze.py`, new version, new `frozen_sha256`).

Until this is ruled, `ledger/manifest.yaml` keeps `lem-finite-exploding` at `SEALED`; the other 21
theorem nodes are `PROVED`. No frozen statement is edited.
