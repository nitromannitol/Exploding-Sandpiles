# Proposition 4.1 @5 source and statement record

Date: 18 October 2026.

This record binds the Proposition 4.1 successor to the exact official arXiv v2 source and
its source-facing consumers. It applies to manifest node `prop-approximate-subadditive@5`
and the complete Lean declaration in `Exploding/Frozen/ApproximateSubadditive.lean`.

The source is `paper/exploding-arxiv.tex`, SHA-256
`f12deba6e481a3d81c6967bc48ecbbdae1df4fa1c5f6248a38990030b308072d`, Proposition 4.1,
lines 740–752, label `prop:approximate_subadditive`. Its `paper/defs.tex` input is pinned at
SHA-256 `9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`. The selected
source block matches maintained journal Proposition 4.1 at lines 886–898. Its standing
Bernoulli parameter range includes the endpoint `p = 1`.

The frozen statement marker is 506 bytes with SHA-256
`9b0824a6fef38f45bc7f3c1cc813ab4268d210f0eeb61ea6bf217cd93132cd44`. Against @4's 504-byte
marker (`724f16a435a724da7cf5af101b9d248d41329ddd4286e2360a1502aa9f2138a4`), its sole
statement change is `(hp1 : p < 1)` to `(hp1 : p ≤ 1)`. The full declaration file has SHA-256
`2dc9bd2c35d46789d944d71cc3f6c5ea94edbefbce2fdaa21cacb3c09d6bd2a2`.

The declaration preserves the source's almost-sure event, configuration-dependent finite
natural constants and all-site inequalities in `ℕ∞`. It retains the three cited-input
binders for the strict branch. That branch derives `p < 1` and calls the existing strict
assembly. At `p = 1`, the branch calls `Exploding.approximate_subadditive_p1`, whose exact
Support file SHA-256 is
`8a6adcb5ade7c4ccbf912bbe67e7c242f20e059ee329f9e71df42a81da1e0c07`. The endpoint law is
the actual Dirac law at the all-high background; the ordinary-arrival witnesses are
`(C₁,C₂)=(1,0)`. At `d=2`, the origin has arrival pair `(1,1)` and a unit neighbor has
`(2,1)`, so the endpoint comparison is nonvacuous.

The public wrapper `Exploding.approximate_subadditive` now has `hp1 : p ≤ 1` and restates
the exact frozen conclusion. The existing strict consumer in
`Exploding/Frozen/TimeConstant.lean` passes `hp1.le`. The internal strict assembly and its
interfaces retain `p < 1`.

The source-reporting fixture retains the old @4 statement identity and restores its matching
journal and official source-gap sets together. A separate live @5 case checks the current
18/24 journal, 4/24 official arXiv and 2/24 corrected-v10 coverage partition, rejects stale
and missing Proposition 4.1 gap allowances, checks the official `defs.tex` pin and source
citation, and keeps the historical annotation map bound to @4.
