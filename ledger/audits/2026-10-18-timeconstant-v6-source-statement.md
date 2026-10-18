# Theorem 1.3 version 6: corrected homogeneous law and parameter-one endpoint

The manifest records `thm-time-constant@6` against the local corrected-v10 source,
`paper/corrected-arxiv/exploding-corrected-arxiv.tex:117-120`, label
`theorem:convergence_of_time_constant`. The source SHA-256 is
`59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2`, with
`paper/corrected-arxiv/defs.tex` SHA-256
`9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.
The official arXiv source and both abstracts are unchanged. This registration does
not certify Theorem 1.3 under the literal displayed official origin-marginal law:
the corrected draft explicitly fixes the homogeneous law at every site and
`0 < p ≤ 1`. The official and corrected theorem sentences are byte-identical;
the distinction is their referenced standing law.

The sole marker change from version 5 is `(hp1 : p < 1)` to `(hp1 : p ≤ 1)`.
The old marker is 864 UTF-8 bytes with SHA-256
`e2982ba6c4bcfa0f77bde5a780c388f19a53c0dea53751b01958d6d9bed8f8a1`;
the new marker is 866 bytes with SHA-256
`83239bc6236e7faecd7ba0ab147fc0af98c324fc90f32cb537a6f368fa478a07`.
Its source-level semantic closure is unchanged,
`d8de311133b2df87608b8cf2da97975aab922b242cd3966f537d68132d78608b`.
That closure is a source tripwire and does not replace kernel or axiom checking.
Historical version-5 clause/exponent annotations retain their original identity.

The complete conclusion retains a deterministic continuous, convex,
one-homogeneous function for nonnegative scalars chosen before the random background, almost-sure
explosiveness, finite ordinary arrival times at every site, and convergence
uniformly over every compact set. In particular finiteness precedes use of
`ℕ∞.toNat`. Every original binder, clause and quantifier order is preserved.
The four cited inputs `hFLP`, `hLSSB`, `hHole`, `hChem` remain explicit; the strict
Fey–Levine–Peres predicate and every External declaration are unchanged.

The proof splits `p ≤ 1` into `p < 1` and `p = 1`. The strict branch reuses the
version-5 proof with its derived strict inequality. The equality branch applies
`Exploding.convergence_of_time_constant_p1 d hd`, whose only inputs are the
dimension and `2 ≤ d`. Its actual `toyLaw d 1` is the mass-one all-high Dirac
law; the explosion threshold is one, and ordinary arrival is `|x|₁ + 1`.
The profile is `N(y) = ∑ i, |y i|`; the installed Support proof gives a global
error bound `(d + 2) / n` for positive `n`. Thus the endpoint includes the full
ordinary-arrival conclusion without assuming explosion, finite arrival or a
scaling limit. At dimension two the origin arrival is one and a unit neighbour
arrival is two, whereas the profile values are zero and one. These distinguish
the actual process from last-wave arrival.

The public wrapper has the identical widened type. The strict LimitShape
assembly in `Exploding/Support/LSProofAux.lean` supplies `hp1.le` and retains its
own strict theorem. The tracked, excluded historical decomposition
`wip/decomp/LimitShapeAux.lean` is preserved byte-for-byte; its old direct call
would require that adaptation if reactivated. No other Frozen node changes.

The source partition is 27 journal rows, five official-arXiv rows and seven
corrected-v10 rows. Structural coverage is respectively 16/24, 5/24 and 3/24;
paper-owned coverage is 14/22, 5/22 and 3/22. Journal line 259 becomes an allowed
gap, corrected line 117 is claimed, and official line 114 remains unclaimed.
The registry remains 28 PROVED theorem rows, 11 FROZEN definitions and zero
SEALED rows. Only LimitShape and Renormalization retain strict Bernoulli paper
contracts. Definitions add no theorem coverage; no whole-paper conclusion or
Proposition 2.2 discharge follows from these counts.

The source-reporting fixture restores the exact historical TimeConstant@5
marker, journal citation and matching gap sets. Live coverage controls restore
complete actual successor files and assert marker hashes first. Negative controls
reject missing corrected definitions, an old-source citation, omitted journal
259 allowance, stale corrected 117 allowance, an accidental official 114 claim,
historical identity reuse and an extra endpoint assumption.

Validation evidence for this declaration consists of the source-reporting tests,
manifest/closure/source gates and exact Frozen/public type, strict and endpoint
consumer, actual-law and standard-three axiom probes. Full library validation and
independent integration review are documented separately; this receipt does not
replace those checks or certify unclaimed source statements.
