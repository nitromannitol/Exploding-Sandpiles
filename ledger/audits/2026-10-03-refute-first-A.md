# Independent refute-first audit — Exploding-Sandpiles, Batch A

* **Auditor:** DeepSeek fleet, second-key audit (independent; wrote none of the development).
* **Batch:** A — `thm-limit-shape`, `thm-time-constant`, `thm-explosive`, `prop-renormalization`, `lem-square-lower-bound`.
* **Repository:** `~/lean/Exploding-Sandpiles`
* **Head read:** `326a151fa10d4f4eaa0905c12b18dd4e64d9e915` (`git rev-parse HEAD`, read-only) — matches the brief's pin `326a151`.
* **Paper pin:** `paper/exploding.tex`, sha256 `1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44` (matches `ledger/manifest.yaml:source_pin`).
* **Constraint observed:** no `git add/commit/push`, no `lake build`, no file edited except this report.

## Gate results (exact commands and output)

```
$ python3 tools/check_manifest.py
check_manifest: OK (29 nodes, 0 unsealed; closure 29 checked, 0 skipped; 458 Exploding declarations indexed)

$ python3 tools/verify.py
...
/usr/bin/python3 tools/check_axioms.py
  clean   thm-limit-shape
  clean   thm-time-constant
  clean   thm-explosive
  clean   prop-renormalization
  clean   lem-square-lower-bound
  ... (all 29 clean)
29 clean, 0 depend on sorryAx, 0 unresolved
verify: axiom closures agree with the manifest (29 clean, 0 open or resting on open nodes)

verify: all checks passed
```

Per-node axiom closures (`tools/check_warnings.py`, replaying `Exploding/Meta/AxiomsAudit.lean`):

```
info: Exploding/Meta/AxiomsAudit.lean:39:0: 'Exploding.limit_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Exploding/Meta/AxiomsAudit.lean:40:0: 'Exploding.convergence_of_time_constant' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Exploding/Meta/AxiomsAudit.lean:41:0: 'Exploding.explosive' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Exploding/Meta/AxiomsAudit.lean:44:0: 'Exploding.renormalization_properties' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Exploding/Meta/AxiomsAudit.lean:47:0: 'Exploding.square_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
check_warnings: OK (0 registered sorry warnings)
```

Independent recomputation of each assigned frozen block (bytes between `BEGIN`/`END`, one leading newline dropped) reproduced the manifest `frozen_sha256` exactly; the closure hashes also all match (`closure 29 checked, 0 skipped`). No `axiom`, `admit`, `sorryAx`, `native_decide`, `set_option`, or `sorry` occurs inside any block; the whole `Exploding/` tree has no declaration-level `axiom`/`constant`/`unsafe`/`native_decide`/`@[extern]`, and `DRAFT_SORRY` appears only in the manifest header comment (0 unsealed nodes).

| node | block bytes | recomputed SHA-256 (16) | manifest match | banned tokens in block |
|---|---|---|---|---|
| `thm-limit-shape` | 612 | `7a9bc664298b2adf` | ✅ | none |
| `thm-time-constant` | 767 | `e2982ba6c4bcfa0f` | ✅ | none |
| `thm-explosive` | 295 | `8132c02216ac6b50` | ✅ | none |
| `prop-renormalization` | 950 | `79b4e8c59d8d852b` | ✅ | none |
| `lem-square-lower-bound` | 217 | `ef7444fd525fb739` | ✅ | none |

## Verdict table

| node | verdict | evidence |
|---|---|---|
| `thm-limit-shape` | **PASS** | block hash ✅; closure exactly `{propext, Classical.choice, Quot.sound}`; statement faithful to `exploding.tex:246-254`; **conditional** on four registered External hypotheses (`hChem` unproved in-repo) — see N1 |
| `thm-time-constant` | **PASS** | hash ✅; closure ✅; faithful to `exploding.tex:259-262`; **conditional** (`hFLP` proved in-repo, `hChem` unproved) — see N1, N2 |
| `thm-explosive` | **PASS** | hash ✅; closure ✅; faithful to `exploding.tex:265-268`; only External `hSch`, which is proved in-repo by `Exploding.xsr_schonmann` — see N3 |
| `prop-renormalization` | **PASS** | hash ✅; closure ✅; faithful to `exploding.tex:482-497`; **conditional** on `hLSSB`, `hHole` (both proved in-repo) and `hChem` (unproved) — see N1 |
| `lem-square-lower-bound` | **PASS** | hash ✅; closure ✅; faithful to `exploding.tex:705-707`; **unconditional**, no External binder; non-vacuous (`η≡0`) — see N4 |

No node is conditional on a `DRAFT_SORRY` predecessor. No node takes an unregistered cited result as a hypothesis. `Exploding.xsr_flp`, `Exploding.xlse_lss_bounded_degree`, `Exploding.xmf_proved`, `Exploding.xsr_schonmann`, `Exploding.xlse_lss_general` and `Exploding.xfmr_proved` all prove their corresponding `Exploding.External.*` `Prop`s in-repo.

## Per-node source fidelity

### `thm-limit-shape` — `Exploding.Frozen.limit_shape`, `Exploding/Frozen/LimitShape.lean:30-42`
Paper `exploding.tex:246-254`:
> "Let $\eta$ be as in (1.2). There exists a convex domain $\mathcal{B}(p)\subset\R^d$ so that on an event of probability 1, $|\{\bar v_t>0\}\triangle\mathcal{B}(p)|\to 0$, where $\bar v_t(x):=v_t([t x])$."

Lean conclusion:
```
∃ B : Set (Fin d → ℝ), Convex ℝ B ∧ IsOpen B ∧ B.Nonempty ∧
∀ᵐ η ∂(toyLaw d p),
  Tendsto (fun t : ℕ => volume (symmDiff
    {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} B)) atTop (nhds 0)
```
`B` is bound before `η` (deterministic, as the paper's `B(p)`), `Convex ℝ B`/`IsOpen B`/`B.Nonempty` are the paper's "convex domain" (a nonempty open convex set is connected; docstring, `CORRESPONDENCE.md`), `[t x]` is exactly `nearestSite` (paper's nearest point, ties by coordinate-wise minimum; `Vocab.lean:187`), `volume` is Lebesgue measure on `Fin d → ℝ`, `symmDiff` is `△`, and `podo (explodingPile η)` is `v_t` of the exploding sandpile `η + M_η δ₀` (`Toppling.lean:69,182`). A Mathlib-only comparator restatement (`ExplodingAudit/LimitShape/Challenge.lean`) is token-for-token the same statement (not built in this run). The four External hypotheses are the cited results the paper's proof consumes (docstring + `CORRESPONDENCE.md`). No EXCESS binder; `p<1` is RULED (paper writes `Fix p>0`; `p=1` is the deterministic endpoint excluded by the proofs).

### `thm-time-constant` — `Exploding.Frozen.convergence_of_time_constant`, `Exploding/Frozen/TimeConstant.lean:33-46`
Paper `exploding.tex:259-262`:
> "Let $\eta$ be as in (1.2) and let $T_{\eta}(x):=\min\{t\ge1:v_t(x)>0\}$. On an event of probability 1, the rescaled arrival times $\bar T_{\eta}(x):=n^{-1}T_{\eta}([n x])$ converge locally uniformly to $\mathcal{N}_{p}$, a continuous, convex, one-homogeneous function on $\R^d$."

Lean conclusion:
```
∃ N : (Fin d → ℝ) → ℝ,
  Continuous N ∧ ConvexOn ℝ Set.univ N ∧
  (∀ c, 0 ≤ c → ∀ y, N (c • y) = c * N y) ∧
  ∀ᵐ η ∂(toyLaw d p),
    Explosive η ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
      ∀ K, IsCompact K → ∀ ε, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
        |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / n - N y| ≤ ε
```
`N` is the paper's `N_p`, bound before `η`; `Continuous`/`ConvexOn ℝ Set.univ`/one-homogeneity for `c ≥ 0` match; local uniform convergence is the ε-form over compact sets (docstring ruling against `sSup ∅ = 0`); `nearestSite` is `[·]`; `arrival` is `T_η` in `ℕ∞` (`Vocab.lean:177`). The conjuncts `Explosive η` (standing: η as in (1.2) is a.s. explosive by Theorem 1.1) and `∀ x, arrival η x ≠ ⊤` (finiteness, needed so `toNat` is not the junk value of `⊤`) are STANDING/RULED. No EXCESS binder.

### `thm-explosive` — `Exploding.Frozen.explosive`, `Exploding/Frozen/Explosive.lean:28-31`
Paper `exploding.tex:265-268`:
> "Suppose $\beta:\Z^d\to\Z$ is drawn from a product measure $\mathbf{P}$. If $\beta\ge d$ and $\mathbf{P}(\beta(0)=(2d-1))>0$, then $\beta$ is explosive with probability 1."

Lean:
```
(d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
(hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)})
(hSch : Exploding.External.SchonmannBootstrap) :
∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => ν), Explosive β
```
Product measure `P` → `Measure.infinitePi (fun _ : Site d => ν)`; `β ≥ d` → `ν {m | d ≤ m} = 1` (equivalent for a product law); `P(β(0)=2d-1)>0` → `0 < ν {2d-1}`; "explosive with probability 1" → `∀ᵐ β … Explosive β`. `hSch` is the registered External Proposition 7.4 used through Proposition 7.5 in the paper's proof. No EXCESS binder.

### `prop-renormalization` — `Exploding.Frozen.renormalization_properties`, `Exploding/Frozen/Renormalization.lean:37-51`
Paper `exploding.tex:482-497`:
> "For fixed $k$ large enough, there are constants $c,C$ so that the following hold on an event of probability 1. (1) There is an infinite connected set $\mathcal{C}_\infty$ of good cubes on the macroscopic lattice $\{Q_k(i)\}$. (2) There is $n_0$ so that for $n\ge n_0$, any connected component of $\mathcal{C}_\infty^c$ that intersects $[-n,n]^d$ has volume smaller than $(\log n)^{5/2}$. (3) There is $n_0$ so that for $n\ge n_0$, for any $x,y\in\mathcal{C}_\infty$ with $|x|\le n$ and $|x-y|\ge(\log n)^2$, $c|x-y|\le d(x,y)\le C|x-y|$, where $d$ is the chemical (graph) distance on $\mathcal{C}_\infty$."

Lean:
```
∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  ∀ᵐ η ∂(toyLaw d p),
    ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k Cinf ∧
      (∃ n0, ∀ n, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
        (componentIn Cinfᶜ x).Finite ∧ ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
      (∃ n0, ∀ n, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
        mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
          ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
            c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ))
```
Quantifier order matches (`∃k0`, `∀k≥k0`, `∃c C>0`, then a.s. `η`); clause (1) is `IsInfiniteConnectedGoodSet`; clause (2) adds the finiteness of the component (RULED so that `Set.ncard` of an infinite set is not read as `0`); clause (3) writes the chemical distance in `ℕ∞` and adds `∃m, chemDist = m` (RULED, carries the paper's asserted finiteness, avoids `ENat.toNat ⊤ = 0`); `|x|`, `|x-y|` are the paper's Manhattan norm (`mnorm`, `Vocab.lean:91`; paper notation line 310). `(log n)^{5/2}` and `(log n)^2` match exactly. No EXCESS binder.

### `lem-square-lower-bound` — `Exploding.Frozen.square_lower_bound`, `Exploding/Frozen/SquareLowerBound.lean:22-24`
Paper `exploding.tex:705-707`:
> "Suppose $\eta\ge0$. For all $n\ge1$ and $m\ge(2d)^{dn}$, the support of the $m$-wave contains $[-n,n]^d$."

Lean:
```
∀ η : Site d → ℤ, (∀ x, 0 ≤ η x) → ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, (2 * d) ^ (d * n) ≤ m →
  ∀ x ∈ cent d n, ∃ t : ℕ, 0 < wave η m (0 : Site d) t x
```
`η ≥ 0` → `∀ x, 0 ≤ η x`; `n ≥ 1`, `m ≥ (2d)^{dn}` match; `[-n,n]^d` → `cent d n` (`Vocab.lean:34`); "support of the m-wave" → `∃ t, 0 < wave η m 0 t x`, the documented reading (the wave odometer is nondecreasing in time on a nonnegative background, `wave_mono_t`), and `wave` is exactly (3.1) of the paper (`Toppling.lean:137`, `u_0=nδ_z`, `u_{t+1}(x)=⌊(Σ_{y∼x}u_t(y)+η(x))/(2d)⌋` off `z`). No EXCESS binder.

## Conditionality, non-vacuity and infrastructure notes

**N1 — three nodes are conditional on an unproved External (`ext-antal-pisztora`).** `thm-limit-shape` carries `hLSSB, hHole, hChem, hSch`; `thm-time-constant` carries `hFLP, hLSSB, hHole, hChem`; `prop-renormalization` carries `hLSSB, hHole, hChem`. Of these, `hLSSB` (`Exploding.xlse_lss_bounded_degree`), `hHole` (`Exploding.xmf_proved`), `hSch` (`Exploding.xsr_schonmann`) and `hFLP` (`Exploding.xsr_flp`) are proved in-repo and can be discharged, but `hChem : Exploding.External.AntalPisztoraChemicalDistance` is **assumed**: `grep -rn AntalPisztoraChemicalDistance Exploding/` finds it only in `Exploding/External/AntalPisztora.lean` and as a hypothesis of frozen nodes; no `theorem … : AntalPisztoraChemicalDistance` exists. So as frozen these three nodes are **conditional theorems**, not unconditional proofs of the paper's Theorems 1.2/1.3 and Proposition 2.2. This is documented (`CORRESPONDENCE.md` §External inputs: "Only `ext-antal-pisztora` is assumed outright"; `Exploding/Meta/AxiomsAudit.lean:31-32`). It is by design, but if `SEALED -> PROVED` is meant to record an unconditional proof of the paper's theorem, these three are PROVED only relative to that assumption. Paper lines: 246–254 (`thm-limit-shape`), 259–262 (`thm-time-constant`), 482–497 (`prop-renormalization`); Lean binder: `(hChem : Exploding.External.AntalPisztoraChemicalDistance)` in each. Reproducer:
```
$ grep -rn "AntalPisztoraChemicalDistance" Exploding/ --include=*.lean | grep -v "External/AntalPisztora"
Exploding/Frozen/LimitShape.lean:33:    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
Exploding/Frozen/TimeConstant.lean:37:    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
Exploding/Frozen/Renormalization.lean:40:    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
... (hypotheses only; no proof)
```

**N2 — `thm-time-constant` conjoins standing facts.** `Explosive η` and `∀ x, arrival η x ≠ ⊤` are additional conjuncts of the a.s. event. They are the paper's standing setup (η as in (1.2) is explosive a.s. by Theorem 1.1, and `T_η` is a minimum over a nonempty set on that event) and prevent `(arrival …).toNat` from reading `⊤` as `0`. Not EXCESS; recorded.

**N3 — `p < 1` in every node that names `(1.2)`.** The paper writes `Fix p>0`; the frozen statements strengthen this to `0 < p < 1` (RULED, `CORRESPONDENCE.md`), excluding the deterministic endpoint `η ≡ 2d-1`. This is a hypothesis strengthening, hence a strictly weaker theorem than the literal paper statement; it is documented and the end point is outside the estimates the proofs use. Recorded, not treated as a defect.

**N4 — non-vacuity.** `lem-square-lower-bound` is unconditional and inhabited: take `η ≡ 0`, `d=2`, `n=1`, `m=16`; the proof gives `t = d·n = 2` with `wave 0 16 0 2 x > 0` for every `x ∈ cent 2 1`, a genuine (non-junk) instance. `thm-explosive`'s hypotheses are inhabited in-repo, e.g. `ν = Measure.dirac (2d-1)` satisfies `IsProbabilityMeasure`, `hlow`, `hhit` (and `toyLaw d p` does for `0<p<1`), and `hSch` is proved; the a.s. statement is over a genuine probability measure. For the three `hChem`-conditional nodes, no in-repo witness of the full hypothesis set exists (N1); `toyLaw d p` is a bona-fide probability measure for `0<p<1`, so their `∀ᵐ η` conclusions are not vacuous *given* `hChem`.

**N5 — infrastructure CONCERN: two gate scripts are vacuous.** `tools/check_clauses.py` and `tools/check_exponents.py` select nodes with the stale regex `rotor\.tex:(\d+)-(\d+)`, but this manifest writes `exploding.tex:<range>`; both therefore report `OK (0 statements …)` — they cover nothing, while `verify.py` reports them as passing gates. Moreover `check_clauses.REVIEWED` is empty, so the clause heuristic would fail every node if the regex were fixed. Reproducer:
```
$ python3 tools/check_clauses.py
node                       label                  paper  lean

Recorded correspondence, one line per statement:

check_clauses: OK (0 statements, ...)
$ python3 tools/check_exponents.py
check_exponents: OK (0 statements; ...)
$ grep -n 'rotor' tools/check_clauses.py tools/check_exponents.py
tools/check_clauses.py:113:        rng = re.search(r"rotor\.tex:(\d+)-(\d+)", src)
tools/check_exponents.py:126:        rng = re.search(r"rotor\.tex:(\d+)-(\d+)", node["source"])
```
This does not falsify any statement (I compared each block against its cited lines by hand and via the comparator for `thm-limit-shape`), but it means the "clause" and "exponent" coverage the gate suite advertises is empty for this repository.

## What I could not verify

* I did not machine-check the LaTeX-to-Lean equivalence; `check_clauses`/`check_exponents` are vacuous here (N5) and `check_constants` only checks existential-constant scope. My fidelity findings are a hand comparison against the quoted lines plus the documented rulings.
* I did not rebuild the Mathlib-only comparator (`ExplodingAudit/LimitShape`) and did not run `lake build` (per instructions); the comparator's byte-identity to the frozen `thm-limit-shape` is textual evidence only.
* I did not independently verify the content of `Exploding.External.AntalPisztoraChemicalDistance` (or the other Externals) against the cited papers; these are registered FROZEN inputs outside the assigned nodes. In particular, the conditional nodes inherit whatever strength/weakness that `Prop` has.
* I did not formalize the mathematical argument that the paper's `p=1` endpoint follows from the formalized `p<1` statements (monotonicity of the construction), nor did I verify that the omitted boundedness of `B` in `thm-limit-shape` is irrelevant (convergence forces finite Lebesgue measure, but not boundedness); both are minor, documented deltas.
* The brief's suggested `python3 tools/check_manifest.py .` is not accepted (the tool takes only `--emit`); the repository-root invocation used above is the working one.

## Conclusion

All five Batch-A nodes **may be promoted `SEALED -> PROVED`**: each frozen block matches the manifest hash and the cited `exploding.tex` statement, each is proved with axiom closure exactly `{propext, Classical.choice, Quot.sound}` and no `sorryAx`, and each is non-vacuous — with the recorded caveat that `thm-limit-shape`, `thm-time-constant` and `prop-renormalization` are **conditional** on the one registered-but-unproved External `ext-antal-pisztora` (and on documented, provable-in-repo or benign reformulations: `p<1`, the standing explosiveness/finiteness clauses, and the finiteness conjuncts guarding `ncard` and `toNat`).
