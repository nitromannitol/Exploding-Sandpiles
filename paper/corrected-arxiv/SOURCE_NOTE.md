# Corrected arXiv-format draft

This directory contains a local corrected arXiv-format draft dated 15 October 2026:
[`exploding-corrected-arxiv.tex`](exploding-corrected-arxiv.tex), SHA-256
`59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2`.
Its included `defs.tex` input has SHA-256
`9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.

The official [arXiv v2](https://arxiv.org/abs/2102.04422v2) source is preserved at
[`paper/exploding-arxiv.tex`](../exploding-arxiv.tex) with its inputs in
[`paper/arxiv/`](../arxiv/). The draft retains the official abstract byte-for-byte.

The global Lean source default remains the corrected journal-format file
`paper/exploding.tex`. The v4 Theorem 6.1 row, v4 Proposition 2.1 row, v5 Proposition
2.2 row, v6 Theorem 1.3 row and four FROZEN literal definitions select this draft and
its `defs.tex` input. The [counterexample promotion receipt](../../ledger/audits/2026-10-15-counterexample-v4-promotion.md)
records its checks. The corrected terminal-and-deadline crossing declaration and its
bounded checks are recorded in a [separate receipt](../../ledger/audits/2026-10-15-crossing-v4-promotion.md).
The corrected homogeneous-law Theorem 1.3 for `0 < p ≤ 1` has a [source and statement
receipt](../../ledger/audits/2026-10-18-timeconstant-v6-source-statement.md); its four
cited inputs remain explicit for the strict branch, and its deterministic endpoint uses
ordinary arrivals under the actual all-high law.

Corrected-v10 Proposition 2.2 version 5 selects lines 352–367 and retains all three
cited percolation inputs. The `hHole` cited binder remains in the type but is unused in
this proof; the hole obligation is proved through in-repository `Exploding.xmf_proved`.
No new External declaration is introduced. The type
states `0 < p ≤ 1` and includes both existence of a maximal infinite good-cube component
and uniqueness of every infinite good-cube component. Its source-marker and proof-consumer
evidence is recorded in the [v5 receipt](../../ledger/audits/2026-10-18-renormalization-v5-source-marker.md).

Structural coverage is 4/24 theorem-like statements (4/22 paper-owned); the other 20
v10 statements remain uncertified. The journal-source group has coverage 15/24
(13/22 paper-owned). Official arXiv v2 Proposition 3.1, Lemmas 3.5, 3.6, 3.7 and
Proposition 4.1 form a separate 5/24 (5/22 paper-owned) group. All five official
arXiv theorem rows include the endpoint `p = 1`. The four literal definitions add no
theorem coverage. These registrations do not certify the other statements of the
corrected draft or of the official arXiv source.

The definitions, figures and precomputed bibliography needed to compile the draft are
included here. From this directory, run the following command three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error exploding-corrected-arxiv.tex
```
