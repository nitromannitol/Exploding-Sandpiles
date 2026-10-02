# Design of the comparator surface

Each headline theorem has a directory here with the same four files.

- `Challenge.lean` imports `Mathlib` and nothing else. It rebuilds from Mathlib primitives
  every object the theorem mentions: the lattice with its unit vectors and graph, the parallel
  toppling odometer and the explosion threshold, the nearest lattice point, the background law,
  Bernoulli site and bond percolation, and the four cited results the theorem takes as
  hypotheses. It states the theorem and ends in a single `sorry`. This file is the object of
  trust: a reader checks what it says, not how it is proved.
- `SolutionBasic.lean` is a verbatim, mechanical copy of the vocabulary block of
  `Challenge.lean` (between `VOCABULARY-BEGIN` and `VOCABULARY-END`). It imports only
  `Mathlib`, so the vocabulary elaborates in the solution exactly as in the challenge.
- `Solution.lean` imports the library together with `SolutionBasic` and the bridges in
  `Support/`, restates the challenge theorem byte-for-byte, and proves it from the library's
  verified statement.
- `comparator.json` names the challenge module, the solution module, the theorem and the
  permitted axioms (`propext`, `Classical.choice`, `Quot.sound`).

The files under `Support/` are part of the solutions. `LimitShapeBridge.lean` identifies the
challenge's definitions with the library's, including those of the `lattice-probability`
dependency: the vocabulary is definitionally equal, so the `*_eq` lemmas are `rfl`. The
vocabulary contains no `structure` or `inductive`, so no bridge has to pack and unpack fields;
the four cited results are `Prop`-valued definitions that `Solution.lean` passes to the
library theorem directly. The odometers `podo` and `spanOdo` are defined by structural
recursion on time, and Lean's smart unfolding does not unfold such a definition at a variable
time; the bridge and the proof in `Solution.lean` switch it off, which changes how the two
copies are compared and not what is stated.

The public workflow feeds the pair to
[leanprover/comparator](https://github.com/leanprover/comparator), which elaborates both
statements and requires them to coincide, replays the solution's proof through an independent
implementation of the Lean kernel, and rejects any axiom outside the permitted three. Nothing
a solution imports can change the statement the reader saw in the challenge; it can only
supply a kernel-checked proof of it.

`check_standalone.sh` elaborates a challenge on its own, with the library's build options, to
confirm that it depends on Mathlib alone, and with `--vocabulary` checks that the vocabulary
block is byte-identical in `Challenge.lean` and `SolutionBasic.lean`.
