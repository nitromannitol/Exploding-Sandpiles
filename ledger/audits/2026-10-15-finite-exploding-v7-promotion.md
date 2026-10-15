# Lemma 3.2 version 7: integrated promotion

The pinned source is `paper/exploding.tex:720-722`, label
`lemma:finite_exploding`, with source SHA-256
`1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44`.
The frozen declaration `Exploding.Frozen.finite_exploding` has marker SHA-256
`70e35f646e03b599a40942113c9c6f1ad34cb35dc8757901a8ca990199169701`.
Its type includes `0 < p` and `p ≤ 1`; the cited inputs remain explicit.

The endpoint proof uses the actual law at `p = 1`, where the all-high
configuration has probability one. The `d = 2, p = 1` and `d = 2, p = 1/2`
applications elaborate, while nonpositive `p` cannot satisfy the required
positivity premise. The frozen export and public wrapper close to exactly
`[propext, Classical.choice, Quot.sound]`.

An isolated full project build passed 9,400 jobs. The manifest, axiom, warning,
constant, documentation, clause, coverage, exponent, source-anchor, citation,
and assumptions checks all passed; the axiom audit found 35 clean nodes and no
`sorryAx`, and the warning audit found no registered sorry warnings. Independent
byte and source reviews checked the endpoint declaration and the integrated
tree. The integrated tree is commit `10dcb15974421a7790c0e959afd9d795e4c4c672`.
This evidence promotes `lem-finite-exploding@7` from `SEALED` to `PROVED`
without changing its frozen statement or proof.

This promotion covers Lemma 3.2 under the pinned historical source. Nine other
Bernoulli paper declarations still exclude `p = 1`, and this receipt does not
certify the separate corrected arXiv draft or the full paper.
