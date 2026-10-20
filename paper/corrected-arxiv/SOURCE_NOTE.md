# Corrected edition

`exploding-corrected-arxiv.tex` is the corrected edition of *A shape theorem for exploding
sandpiles* (Ahmed Bou-Rabee), starting from [arXiv:2102.04422v2](https://arxiv.org/abs/2102.04422v2),
whose unmodified source is [`../exploding-arxiv.tex`](../exploding-arxiv.tex). Every change is
listed, with the published text, the corrected text and the reason, in the section
"Corrections to the published version" at the end of the edition.

The SHA-256 of the edition is `6e5a981a0d8d3b7abdf78e31d2630780b9db467e63aea7772e93043e4e804d0c`,
and that of its `defs.tex` input is `9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.
Both are recorded as source pins in [`ledger/manifest.yaml`](../../ledger/manifest.yaml).

The bibliography and the figures are included. To compile, run from this directory:

```sh
latexmk -pdf exploding-corrected-arxiv.tex
```

The `.bbl` is included. The compiled edition has 49 pages.
