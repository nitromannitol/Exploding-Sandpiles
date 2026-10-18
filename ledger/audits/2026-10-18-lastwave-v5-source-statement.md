# Proposition 3.1 @5 source and statement record

Date: 18 October 2026.

This record identifies the source and frozen statement for `prop-last-wave-convergence@5`.

The selected source is official arXiv v2 `paper/exploding-arxiv.tex`, SHA-256
`f12deba6e481a3d81c6967bc48ecbbdae1df4fa1c5f6248a38990030b308072d`, Proposition 3.1,
lines 706–718, label `prop:convergence_of_the_last_wave`. Its `paper/defs.tex` input is pinned
at SHA-256 `9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.

The frozen marker changes from @4's SHA-256
`757cd6a770e4ea98496b4203ac93795842f3cbafac4b0ee55cea24e49f32e679` to @5's SHA-256
`9a80cc4dcaac38eaab62fc1fbfeb46f6b0868d54c397c6b4687823ef3940ff59`. The sole change in the
marker is `(hp1 : p < 1)` to `(hp1 : p ≤ 1)`; the dimension and probability binders, all three
cited-input hypotheses, deterministic limit-function quantifier, actual `toyLaw`, finite
last-arrival clause, and locally uniform epsilon conclusion are retained.

The proof splits `p ≤ 1` into `p < 1` and `p = 1`. The strict branch reuses the prior proof
with the strict inequality derived from the split. The endpoint branch substitutes `p = 1`
and calls `Exploding.convergence_of_the_last_wave_p1` from the ordinary Support theorem. The
three cited inputs remain in the public frozen type for the strict branch and are not added to
the Support endpoint theorem. The direct consumer `Exploding.Frozen.convergence_of_time_constant`
passes its existing strict fact through `.le`. The public wrapper
`Exploding.convergence_of_the_last_wave` accepts `p ≤ 1` and restates the Frozen declaration.

The manifest and generated source map record 28 journal rows, five official arXiv rows, and
six corrected-v10 rows. The exact coverage partition is 17/24, 5/24, and 2/24 respectively.
The Proposition 3.1 claim moved from the journal source to official arXiv: its line 846 journal
statement is now an allowed gap, and its line 706 official arXiv statement is claimed. The
source reporting fixture restores the complete live Proposition 3.1 file and checks that its
marker hash equals the manifest before testing the current coverage partition.
