# Corrected arXiv-format draft

This directory contains a local corrected arXiv-format draft dated 15 October 2026:
[`exploding-corrected-arxiv.tex`](exploding-corrected-arxiv.tex), SHA-256
`8ea6f8fb2e2885382331cedffd7a5a7951a85d04d2a71a40546ac11a491d67c8`.

The official [arXiv v2](https://arxiv.org/abs/2102.04422v2) source is preserved at
[`paper/exploding-arxiv.tex`](../exploding-arxiv.tex) with its inputs in
[`paper/arxiv/`](../arxiv/). The draft retains the official abstract byte-for-byte.

The current Lean formalization, correspondence table and certificates follow the
corrected journal-format source [`paper/exploding.tex`](../exploding.tex). This
separate draft has no Lean certification.

The definitions, figures and precomputed bibliography needed to compile the draft
are included here. From this directory, run the following command three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error exploding-corrected-arxiv.tex
```
