# Independent refute-first audit — Exploding-Sandpiles, Batch D

* **Auditor:** DeepSeek fleet, second-key audit (independent; wrote none of the development).
* **Batch:** D — `lem-approx-subadditivity`, `prop-recurrence`, `lem-local-convexity`, `lem-finite-exploding`, `prop-crossing-time`.
* **Repository:** `~/lean/Exploding-Sandpiles`.
* **Head:** I did **not** run `git` (per instruction). The brief pins `326a151`; the batch-A report records `326a151fa10d4f4eaa0905c12b18dd4e64d9e915` and the batch-B report records `2ad193d428b6aee264a45b3750259c2bbaae0533`, an ancestor–descendant of the pin with `Exploding/Frozen`, `ledger/manifest.yaml` and every provider byte-identical. All frozen-block reads and gate runs below are on the current tree, and all five block hashes match the manifest, so the results apply at the pin.
* **Paper pin:** `paper/exploding.tex`, sha256 `1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44` (matches `ledger/manifest.yaml:source_pin`).
* **Constraints observed:** no `git`, no `lake build`, no file edited except this report.

## Gate results (exact commands and output)

```
$ python3 tools/check_manifest.py
check_manifest: OK (29 nodes, 0 unsealed; closure 29 checked, 0 skipped; 460 Exploding declarations indexed)

$ python3 tools/verify.py
...
/usr/bin/python3 tools/check_axioms.py
  clean   lem-approx-subadditivity
  clean   prop-recurrence
  clean   lem-local-convexity
  clean   lem-finite-exploding
  clean   prop-crossing-time
  ...
29 clean, 0 depend on sorryAx, 0 unresolved
verify: axiom closures agree with the manifest (29 clean, 0 open or resting on open nodes)

check_clauses: OK (22 statements, each read against the paper and its correspondence recorded; 4 where the paper is recorded as asserting more, all explained above)
check_exponents: OK (26 statements; every paper exponent appears in its Lean statement or is explained above)
check_warnings: OK (0 registered sorry warnings)

verify: all checks passed
```

`tools/check_warnings.py` (replaying `Exploding/Meta/AxiomsAudit.lean`) prints for every export, including the providers of all five nodes, exactly `depends on axioms: [propext, Classical.choice, Quot.sound]`; no `sorryAx` occurs. `check_manifest` reports `0 unsealed`, so no node is conditional on a `DRAFT_SORRY` predecessor.

Frozen-block integrity (SHA-256 over the bytes strictly between the marker lines, marker lines excluded; token scan of the block):

| node | block bytes | recomputed SHA-256 | manifest | banned tokens |
|---|---|---|---|---|
| `lem-approx-subadditivity` | 325 | `cc8f12ca936e4c7004662f4796489012419c44eb5071f5549ea1fa3cf5fc67f5` | ✅ | none |
| `prop-recurrence` | 97 | `fb09b457811848161a746759e6fd31ee024a56bee43df4e23cca58af7ae87fa1` | ✅ | none |
| `lem-local-convexity` | 442 | `c265b27336538e776144ad00d8ad3e44a93816312863f9b3cb9dc3d5997e91f4` | ✅ | none |
| `lem-finite-exploding` | 360 | `2bdfdb526cdb4146e9765019df878274f2d3d49991244591748bbce579ac9772` | ✅ | none |
| `prop-crossing-time` | 198 | `86d88877abf5e6e1dc37f9bf5e1a1552bb04588de3fa050596b1faf4fb3d5e38` | ✅ | none |

Exactly one frozen block per file, each with exactly one `theorem`; no `axiom`, `admit`, `sorry`, `native_decide` or `set_option` inside any block.

## Verdict table

| node | verdict | evidence |
|---|---|---|
| `lem-approx-subadditivity` | **PASS** | hash ✅; closure exactly `{propext, Classical.choice, Quot.sound}`; faithful to `exploding.tex:760-765`; no `External` binder; non-vacuous (toy-law a.s. witness) |
| `prop-recurrence` | **PASS** | hash ✅; closure ✅; faithful to `exploding.tex:1927-1929`; unconditional; concrete instance `d = 1`, `η ≡ 1` |
| `lem-local-convexity` | **PASS** | hash ✅; closure ✅; faithful to `exploding.tex:531-535` with the model's standing range; unconditional; non-vacuous (`m = 0`, `A = {0}`) |
| `lem-finite-exploding` | **CONCERN** | hash ✅; closure ✅; **conclusion is the existence half only** — Lean `∃ n ≥ 1, ¬ WaveStabilizable η n 0`, paper `\hat M_\eta(0) < ∞` (see below); conditional on the assumed `hChem` |
| `prop-crossing-time` | **PASS** | hash ✅; closure ✅; faithful to `exploding.tex:416-422` with `k^d` carried inside `GoodCube`; unconditional; non-vacuous |

No FAIL. No node is conditional on a `DRAFT_SORRY` predecessor.

## Per-node source fidelity, binders, non-vacuity

### `lem-approx-subadditivity` — `Exploding/Frozen/ApproxSubadditivity.lean:104-109`
Paper `exploding.tex:760-765`:
> "The penultimate-cluster arrival times are subadditive: for all $a,b,z\in\Z^d$, $\tilde{T}(a,z)\le\tilde{T}(a,b)+\tilde{T}(b,z)$."

Lean conclusion (identical relation):
```
clusterArrival η a z ≤ clusterArrival η a b + clusterArrival η b z
```
Binder classification: `d, hd` STANDING/SOURCE (`d ≥ 2` is the paper's standing dimension); `η` SOURCE; `hlow, hhigh` STANDING (the paper's Section-2 range `2d-2 ≤ η ≤ 2d-1`, i.e. the support of `toyLaw d p`; triage); `hlast : ∀ y, ∃ n ≥ 1, ¬ WaveStabilizable η n y` RULED (paper's Lemma 3.2, needed so `clusterArrival` is not the junk value of an empty `sInf`; used by the proof); `a b z` SOURCE. No EXCESS; no `External`; not conditional on a `DRAFT_SORRY`. Non-vacuous: `hlast` is the a.s. content of `finite_exploding`, so the toy law supplies configurations satisfying all hypotheses, and the `ℕ∞` inequality is the paper's exact relation (no junk `⊤` is read as a natural since the inequality is in `ℕ∞`).

### `prop-recurrence` — `Exploding/Frozen/Recurrence.lean:16-17`
Paper `exploding.tex:1927-1929`:
> "For every $d\ge1$, $\eta:\Z^d\to\{d\}$ is recurrent."

Lean:
```
theorem Exploding.Frozen.recurrence (d : ℕ) (hd : 1 ≤ d) :
    Recurrent (fun _ : Site d => (d : ℤ))
```
`d, hd` SOURCE ("for every `d ≥ 1`"); the constant background is `fun _ => d`, exactly `η ≡ d`. No EXCESS, no `External`, unconditional. Non-vacuous: `d = 1` gives the concrete configuration `η ≡ 1`, and `Recurrent` is the paper's finite-domain recurrence (firing `∂V` makes every site of `V` topple from time `|V|` on).

### `lem-local-convexity` — `Exploding/Frozen/LocalConvexity.lean:19-26`
Paper `exploding.tex:531-535`:
> "Let $A := \{z^{(i)}\}$ be a finite path $z^{(i)}\sim z^{(i+1)}$. Let $w_t$ denote $A$-frozen parallel toppling with initial conditions $w_0|_A = 1$, $s_0' = \eta$. Then, $w_t|_{\br(A)} = 1$, for all $t \ge |\br(A)|$."

Lean conclusion:
```
fodo A η (Set.indicator A 1) t x = 1
```
Binder classification: `d, hd` STANDING; `η` SOURCE; `hlow, hhigh` STANDING (Section-2 range, triage); `m, z, hpath` TYPING/SOURCE (the finite path `z 0 … z m`, consecutive adjacent); `A, hA` TYPING (the path's vertex set); `hfin : (br A).Finite` TYPING (needed so `|br A|` is `hfin.toFinset.card` rather than the junk `Set.ncard ∅ = 0`); `t, ht` SOURCE (`t ≥ |br A|`); `x, hx` SOURCE (`x ∈ br A`). No EXCESS, no `External`, unconditional. Non-vacuous: `m = 0`, `z 0 = 0`, `A = {0}`, `η ≡ 2d-2` satisfy the hypotheses, and `0 ∈ A` is frozen, so `fodo {0} η (indicator {0} 1) 1 0 = 1`.

### `prop-crossing-time` — `Exploding/Frozen/CrossingTime.lean:19-21`
Paper `exploding.tex:416-422`:
> "For every $\delta > 0$, there is a $k$ so that $\max_{i,z}\mathfrak{C}_k^{(i,z)} \le k^d$ with probability at least $(1-\delta)$."

Lean:
```
∃ k : ℕ, 1 ≤ k ∧ ENNReal.ofReal (1 - δ) ≤ toyLaw d p {η | GoodCube η k}
```
with (in `Exploding/Support/Vocab.lean:68-70`) `GoodCube η k := ∀ (i : Fin d) (z : Site d), z ∈ closureN (cube d k) → crossingTime η k i z ≤ ((k ^ d : ℕ) : ℕ∞)`. `i : Fin d` is the paper's direction `1 ≤ i ≤ d`; `z ∈ closureN (cube d k)` is `z ∈ \bar{Q}_k` (the box and its outer boundary); `crossingTime` is `𝔠_k^{(i,z)}` in `ℕ∞`, with `⊤` for the paper's `∞`; the `k^d` exponent is therefore present, carried by `GoodCube` rather than repeated in the frozen block. `d, hd, p, hp, hp1` SOURCE/STANDING; `δ, hδ` SOURCE. No EXCESS, no `External`, unconditional. Non-vacuous: `d = 2`, `p = 1/2`, `δ = 1/2` satisfy the hypotheses and the conclusion is the paper's non-trivial high-probability crossing bound.

### `lem-finite-exploding` — `Exploding/Frozen/FiniteExploding.lean:26-31` (CONCERN)

Paper `exploding.tex:720-722` (exact):
```
\begin{lemma} \label{lemma:finite_exploding}
	The last-wave is well-defined, $\hat{M}_{\eta}(0) < \infty$.
\end{lemma}
```
Lean frozen block (exact):
```
theorem Exploding.Frozen.finite_exploding (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)
```
The conclusion is the existence of a non-stabilising `n`-wave at the origin. `Exploding.waveThreshold` (`Exploding/Support/Toppling.lean:224`) is `ℕ`-valued,
```
noncomputable def waveThreshold (η : Site d → ℤ) (z : Site d) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z}
```
so under the documented ruling "read `\hat M_\eta(0)` as this `ℕ`-valued `waveThreshold`", the frozen conclusion (the defining set is non-empty, hence `waveThreshold ≥ 1` is the genuine least index) is **equivalent** to `\hat M_\eta(0) < ∞`, and the file docstring states this reading. Under any reading in which `\hat M_\eta` takes the value `∞` when no such `n` exists, the frozen conclusion states only that this value is finite — i.e. exactly the paper's assertion — but the frozen block does not display `\hat M_\eta(0) < ∞`, and a `ℕ`-valued `sInf ∅ = 0` is a separate modelling choice. Because the correspondence is not literal, this node is recorded as a **CONCERN**, and the clause gate flags it (`FLAGGED`), consistent with `ledger/audits/2026-10-03-script-audit-triage.md`, which calls it a partial transcription.

Exact reproducer:
```
$ sed -n '720,722p' paper/exploding.tex
\begin{lemma} \label{lemma:finite_exploding}
	The last-wave is well-defined, $\hat{M}_{\eta}(0) < \infty$.
\end{lemma}

$ sed -n '31p' Exploding/Frozen/FiniteExploding.lean
    ∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)

$ sed -n '224,225p' Exploding/Support/Toppling.lean
noncomputable def waveThreshold (η : Site d → ℤ) (z : Site d) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z}

$ python3 tools/check_clauses.py | grep lem-finite-exploding
  lem-finite-exploding     lemma:finite_exploding     0     2  <-- paper asserts more
  lem-finite-exploding: the paper asserts the last wave is well-defined as M̂_η(0) < ∞; Lean asserts the existence half, ∀ᵐη ∃ n ≥ 1, ¬ WaveStabilizable η n 0, and not the finiteness of M̂ (flagged: partial transcription, triage)
```
Binders: `d, hd, p, hp, hp1` SOURCE/STANDING; `hLSSB, hHole, hChem` are the registered `External` inputs the paper's Section-3 proof cites. `hLSSB` and `hHole` are discharged in-repo (`Exploding.xlse_lss_bounded_degree`, `Exploding.xmf_proved`); `hChem` (`Exploding.External.AntalPisztoraChemicalDistance`, `ext-antal-pisztora`) is **assumed, not proved in-repo**, so the node is conditional on an unproved External (same recorded caveat as Batch A, N1). No EXCESS binder. Non-vacuity: `toyLaw d p` is a probability measure for `0 < p < 1`, so the a.s. statement is not vacuous given the Externals.

## What I could not verify

* I did not run `git` (per instruction), so the head is quoted from the brief and the batch-A/B reports, not re-derived. The five frozen blocks match the manifest hashes, and the manifest and frozen tree are recorded as unchanged between the pin and the latest recorded head.
* `lem-finite-exploding`: I did not formalize the equivalence between the frozen conclusion and a literal `ℕ∞`-valued `\hat M_\eta(0) < ∞`; the claim rests on the file docstring's modelling ruling. A literal-fidelity reading would call the frozen block a strict weakening.
* I did not independently check the content of the `External` `Prop`s against the cited papers, nor discharge `hChem` (no in-repo proof exists).
* I did not machine-verify the `GoodCube`/`closureN` correspondence to `\max_{i,z}` beyond reading `Exploding/Support/Vocab.lean:22,31,68`; the exponent and quantifier domains match by inspection.

## Conclusion

Four of the five Batch-D nodes — `lem-approx-subadditivity`, `prop-recurrence`, `lem-local-convexity`, `prop-crossing-time` — **may be promoted `SEALED -> PROVED`**: each matches its manifest hash and cited `exploding.tex` statement, is proved with axiom closure exactly `{propext, Classical.choice, Quot.sound}` and no `sorryAx`, and is non-vacuous. `lem-finite-exploding` **may not yet be promoted** without an erratum/companion node (or an explicit ruling accepting the `ℕ`-valued `waveThreshold` reading): its frozen conclusion asserts only the existence of a non-stabilising wave, not the paper's displayed `\hat M_\eta(0) < \infty`, and it is additionally conditional on the assumed `hChem`.
