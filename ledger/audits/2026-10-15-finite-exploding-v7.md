# Validation receipt: finite-exploding @7

The historical source remains `paper/exploding.tex:720-722`, label
`lemma:finite_exploding`, pinned at SHA-256
`1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44`.
`Exploding.Frozen.finite_exploding` is version 7. Its 385-byte frozen block has
SHA-256 `70e35f646e03b599a40942113c9c6f1ad34cb35dc8757901a8ca990199169701`;
the whole file has SHA-256
`c6048ca2cf9807373510e1959b3a5d7e833146df08d3be2bf22c9126d9cca6a9`.
The only statement change from @6 is `p < 1` to `p ≤ 1`; `d ≥ 2`, `p > 0`,
the conclusion, and the visible inputs `LiggettSchonmannStaceyBoundedDegree`,
`MathieuHoleVolume`, and `AntalPisztoraChemicalDistance` are retained. The
strict branch keeps the prior proof; the equality branch applies the unconditional
Support theorem `Exploding.finite_exploding_p1` and does not consume those inputs.

The exact Frozen/public applications at `d = 2, p = 1` and at `d = 2, p = 1/2`
elaborate. At the endpoint, `toyLaw 2 1` is the mass-one Dirac law on the
all-high configuration of height 3. For every `T`, the `n = 1` wave front has
a site reached at `T + 1` but not at `T`, so this endpoint witness is nonvacuous.
The compiled probe source was `scratch/FiniteExplodingV7Probe.lean`, SHA-256
`aa2d04cec6c63664b8a2bdcdbd9a34b5aed9d03d113051d65e5cd57ac6a34c71`.

The changed Frozen module, public wrapper, and six Support consumers build together
(8,864 jobs). The seven strict Support applications pass `hp1.le`; their enclosing
interfaces remain strict. The endpoint Support theorem, Frozen export, and public
wrapper each have axiom closure exactly `[propext, Classical.choice, Quot.sound]`.
Expected-failure probes at `p = 0` and `p = -1` leave the required positivity goal
`False` unresolved.

The manifest row is `SEALED`, pending the root-owned independent final-byte audit
and full integrated gates. This receipt does not certify whole-paper coverage of
the official arXiv or corrected-v10 source.
