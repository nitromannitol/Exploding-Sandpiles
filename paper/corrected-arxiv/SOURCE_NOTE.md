# Corrected edition

`exploding-corrected-arxiv.tex` is the corrected edition of *A shape theorem for exploding
sandpiles* (Ahmed Bou-Rabee), starting from [arXiv:2102.04422v2](https://arxiv.org/abs/2102.04422v2),
whose unmodified source is [`../exploding-arxiv.tex`](../exploding-arxiv.tex). Every change is
listed, with the published text, the corrected text and the reason, in the section
"Corrections to the published version" at the end of the edition.

The SHA-256 of the edition is `0cefbf3bfc7cc08597d59d36a3473cdf94ee816076f688c978510bb7edc6e019`,
and that of its `defs.tex` input is `9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.
Both are recorded as source pins in [`ledger/manifest.yaml`](../../ledger/manifest.yaml).

The bibliography and the figures are included. To compile, run from this directory:

```sh
latexmk -pdf exploding-corrected-arxiv.tex
```

The `.bbl` is included. The compiled edition has 46 pages.
