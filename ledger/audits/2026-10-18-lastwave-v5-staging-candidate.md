# Proposition 3.1 @5 staging candidate record

Date: 18 October 2026.

This record describes an unmerged source-side candidate for `prop-last-wave-convergence@5`
on branch `exploding-lastwave-v5-staging-20261018`, based on private main
`f3ad2600b497b1998e26af4d6d1705a80d30296b`. It is not a promotion receipt. The candidate has
not received the root integration build, exact-type axiom check, or full configured gates, and
it receives no current-main or paper credit.

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
the Support endpoint theorem. `Exploding.Frozen.TimeConstant` passes its existing strict fact
through `.le`; `Exploding.MainTheorems.convergence_of_the_last_wave` is widened to `p ≤ 1` and
continues to restate the Frozen declaration.

The manifest and generated source map record 28 journal rows, five official arXiv rows, and
six corrected-v10 rows. The exact coverage partition is 17/24, 5/24, and 2/24 respectively;
Proposition 3.1's journal gap moved from the journal allowed-gap list to the official-arXiv
claim set. No other node version, cited input, source byte, or gate is changed. The live source
reporting fixture restores the full live Prop. 3.1 file and checks that its marker hash equals
the live manifest before testing the current coverage partition.

Source-only checks passed: `check_manifest.py`; `check_coverage.py`; `check_clauses.py`;
`check_constants.py`; `check_exponents.py`; `paper_anchors.py`; `paper_citations.py`;
`sync_docs.py`; `assumptions.py --check`; `tools.test_source_reporting` (20 tests); and
`tools.test_source_tools` (16 tests). No Lean/Lake result is claimed by this record. Root must
perform the integration build, exact-type axiom check, independent final-union review, and all
configured gates before @5 can receive credit.
