# Corrected arXiv-format draft

This directory contains a local corrected arXiv-format draft dated 15 October 2026:
[`exploding-corrected-arxiv.tex`](exploding-corrected-arxiv.tex), SHA-256
`59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2`.
Its included `defs.tex` input has SHA-256
`9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.

The official [arXiv v2](https://arxiv.org/abs/2102.04422v2) source is preserved at
[`paper/exploding-arxiv.tex`](../exploding-arxiv.tex) with its inputs in
[`paper/arxiv/`](../arxiv/). The draft retains the official abstract byte-for-byte.

The global Lean source default is the corrected journal-format file paper/exploding.tex. The proved v4 Theorem 6.1 row and four FROZEN literal definitions select this draft and its defs.tex input. The exact declarations were approved on 15 October 2026 and passed exact-type compilation, axiom checks, a full locked build, all eleven configured checks and independent source/body/consumer audit. This accepts one corrected counterexample theorem and the four literal definition bodies. The [dated promotion receipt](../../ledger/audits/2026-10-15-counterexample-v4-promotion.md) records their exact identity. Structural coverage remains 1/24 theorem-like statements (1/22 paper-owned); the other 23 v10 statements remain uncertified. The old-source group remains 23/24. The official arXiv v2 source remains separately preserved.

The definitions, figures and precomputed bibliography needed to compile the draft
are included here. From this directory, run the following command three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error exploding-corrected-arxiv.tex
```
