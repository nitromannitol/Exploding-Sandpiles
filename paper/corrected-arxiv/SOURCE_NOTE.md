# Corrected arXiv-format draft

This directory contains a local corrected arXiv-format draft dated 15 October 2026:
[`exploding-corrected-arxiv.tex`](exploding-corrected-arxiv.tex), SHA-256
`59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2`.
Its included `defs.tex` input has SHA-256
`9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.

The official [arXiv v2](https://arxiv.org/abs/2102.04422v2) source is preserved at
[`paper/exploding-arxiv.tex`](../exploding-arxiv.tex) with its inputs in
[`paper/arxiv/`](../arxiv/). The draft retains the official abstract byte-for-byte.

The global Lean source default remains the corrected journal-format file paper/exploding.tex. The v4 Theorem 6.1 row, v4 Proposition 2.1 row and four FROZEN literal definitions select this draft and its defs.tex input. The [counterexample promotion receipt](../../ledger/audits/2026-10-15-counterexample-v4-promotion.md) records its completed checks. The corrected terminal-and-deadline crossing declaration and its bounded checks are recorded in a [separate receipt](../../ledger/audits/2026-10-15-crossing-v4-promotion.md). Structural coverage is 2/24 theorem-like statements (2/22 paper-owned); the other 22 v10 statements remain uncertified. The journal-source group has coverage 20/24 (18/22 paper-owned). Official arXiv v2 Lemmas 3.5 and 3.7 form a separate 2/24 (2/22 paper-owned) group. The four literal definitions add no theorem coverage. The corrected-source declarations do not certify any other statement of the official arXiv source.

The definitions, figures and precomputed bibliography needed to compile the draft
are included here. From this directory, run the following command three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error exploding-corrected-arxiv.tex
```
