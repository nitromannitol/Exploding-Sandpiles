# Corrected arXiv-format draft

The local corrected draft, version 11 dated 18 October 2026, is
[exploding-corrected-arxiv.tex](exploding-corrected-arxiv.tex), SHA-256
`c99ce52a57b7da1f805efe610c474c968c0aa00e0840bd8b0e92ae0d4c53f262`.
Its `defs.tex` input is
`9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.
The official [arXiv v2](https://arxiv.org/abs/2102.04422v2) extraction remains
unchanged at [paper/exploding-arxiv.tex](../exploding-arxiv.tex); its abstract
is retained byte-for-byte.

Version 11 reconciles one obsolete qualification remark with the existing
Section 5 argument: path filling implies nonnegativity, allowing qualitative
exponential finite-box seeding. It asserts no polynomial rate for general
backgrounds. Numbered statements, proofs, hypotheses and bibliography have
unchanged bytes from version 10; later source addresses shift two lines.

The manifest selects this draft for 22 numbered paper-owned theorem rows,
four literal definitions and two new cited-input definitions. The 13 retained
historical citation/input-companion rows carry their exact journal pins
explicitly. The two new radius predicates are cited, unproved inputs. Exact
source and native integration evidence is in the
[integration record](../../ledger/audits/2026-10-18-corrected-v11-integration.md).

The unnumbered planar optimality remark (Remark 1, lines 785-823) is
registered separately as `Exploding.Frozen.sharp_planar_obstruction`; see its
[audit record](../../ledger/audits/2026-10-18-sharp-planar-obstruction.md).
Compilation does not certify a whole-paper release. Final semantic closure and all
release gates remain required.

Definitions, figures and the bibliography needed to compile the draft are
included. From this directory run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error exploding-corrected-arxiv.tex
```

The checked version 11 PDF has 42 pages and no unresolved references or citations.
