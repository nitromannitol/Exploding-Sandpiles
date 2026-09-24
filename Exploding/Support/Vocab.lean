/-
The vocabulary of `paper/exploding.tex` beyond the toppling dynamics: boxes and
their faces, boundaries, bounding rectangles, lines across a box, the crossing
time and good cubes, the last-wave and its arrival times, recurrence, and the
product measure the paper's backgrounds are drawn from.
-/
import Exploding.Support.Toppling

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-! ### Boundaries -/

/-- `∂A`, the outer boundary of `A`. -/
def outerBoundary (A : Set (Site d)) : Set (Site d) :=
  {x | x ∉ A ∧ ∃ y ∈ A, (lattice d).Adj x y}

/-- `Ā = A ∪ ∂A`. -/
def closureN (A : Set (Site d)) : Set (Site d) := A ∪ outerBoundary A

/-- `∂°A`, the inner boundary of `A`. -/
def innerBoundary (A : Set (Site d)) : Set (Site d) :=
  {x | x ∈ A ∧ ∃ y, y ∉ A ∧ (lattice d).Adj x y}

/-! ### Boxes -/

/-- The box `Q_k = {x ∈ ℤ^d : 1 ≤ x ≤ k}` of the paper. -/
def cube (d k : ℕ) : Set (Site d) := {x | ∀ i, 1 ≤ x i ∧ x i ≤ (k : ℤ)}

/-- The sup-norm box `[-n, n]^d`. -/
def cent (d : ℕ) (n : ℕ) : Set (Site d) := {x | ∀ i, |x i| ≤ (n : ℤ)}

/-- The internal face `F_i(Q_n) = {x ∈ Q_n : x_i = 1}` of `(7.2)`. -/
def faceLow (d n : ℕ) (i : Fin d) : Set (Site d) := {x ∈ cube d n | x i = 1}

/-- The internal face `F_{d+i}(Q_n) = {x ∈ Q_n : x_i = n}` of `(7.2)`. -/
def faceHigh (d n : ℕ) (i : Fin d) : Set (Site d) := {x ∈ cube d n | x i = (n : ℤ)}

/-- The line `L_k^{(i,z)}` running from one side of `Q_k` to the other through
`z` in direction `i`. -/
def line (d k : ℕ) (i : Fin d) (z : Site d) : Set (Site d) :=
  {x | (1 ≤ x i ∧ x i ≤ (k : ℤ)) ∧ ∀ l, l ≠ i → x l = z l}

/-- The bounding rectangle `br(A) = {z : m ≤ z ≤ M}`, where `m` and `M` are the
coordinatewise minimum and maximum over `A`.  Written as a pair of witnesses so
that no `sInf` of an empty set is read. -/
def br (A : Set (Site d)) : Set (Site d) :=
  {z | ∀ i, (∃ y ∈ A, y i ≤ z i) ∧ (∃ y ∈ A, z i ≤ y i)}

/-! ### Crossing a box -/

open scoped Classical in
/-- The odometer of `{Q_k^c ∪ L_k^{(i,z)}}`-frozen parallel toppling started
from `w_0 = 1{x ∈ L_k^{(i,z)}}` on the background `η`. -/
noncomputable def crossOdo (η : Site d → ℤ) (k : ℕ) (i : Fin d) (z : Site d) :
    ℕ → Site d → ℤ :=
  fodo ((cube d k)ᶜ ∪ line d k i z) η (fun x => if x ∈ line d k i z then 1 else 0)

/-- The crossing time `𝔠_k^{(i,z)}`, valued in `ℕ∞` so that the paper's `∞`
is the value at the empty set rather than a junk natural number. -/
noncomputable def crossingTime (η : Site d → ℤ) (k : ℕ) (i : Fin d) (z : Site d) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ 1 ≤ n ∧ ∀ x ∈ cube d k, crossOdo η k i z n x = 1}

/-- `Q_k` is a *good cube* for `η`: `max_{i,z} 𝔠_k^{(i,z)} ≤ k^d`. -/
def GoodCube (η : Site d → ℤ) (k : ℕ) : Prop :=
  ∀ (i : Fin d) (z : Site d), z ∈ closureN (cube d k) →
    crossingTime η k i z ≤ ((k ^ d : ℕ) : ℕ∞)

/-- `Q_k(i) = Q_k + i·k` is a good cube: the macroscopic site `i` is good. -/
def GoodAt (η : Site d → ℤ) (k : ℕ) (i : Site d) : Prop :=
  GoodCube (fun x => η (x + (k : ℤ) • i)) k

/-- The set of good sites of the macroscopic lattice. -/
def goodSites (η : Site d → ℤ) (k : ℕ) : Set (Site d) := {i | GoodAt η k i}

/-- `C` is an infinite connected set of good cubes: an infinite set of good sites
of the macroscopic lattice, any two of which are joined by a nearest-neighbour
path inside `C`. -/
def IsInfiniteConnectedGoodSet (η : Site d → ℤ) (k : ℕ) (C : Set (Site d)) : Prop :=
  C.Infinite ∧ C ⊆ goodSites η k ∧ ∀ x ∈ C, ∀ y ∈ C, y ∈ componentIn C x

/-- The first unit direction `e_1`. -/
def e1 (d : ℕ) : Site d := fun i => if (i : ℕ) = 0 then 1 else 0

/-! ### Distances -/

/-- The Manhattan norm `|x|`. -/
def mnorm (x : Site d) : ℤ := ∑ i, |x i|

/-- The chemical (graph) distance inside `S`, valued in `ℕ∞`, so that the
absence of a path is `⊤` rather than a junk natural number. -/
noncomputable def chemDist (S : Set (Site d)) (x y : Site d) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ ∃ (hx : x ∈ S) (hy : y ∈ S)
    (w : ((lattice d).induce S).Walk ⟨x, hx⟩ ⟨y, hy⟩), w.length = n}

/-! ### Recurrence -/

open scoped Classical in
/-- `η` restricted to the finite domain `V` is *recurrent*: the `V^c`-frozen
odometer from `w_0 = 1{x ∈ ∂V}` is `1` on `V` from time `|V|` on. -/
def RecurrentOn (η : Site d → ℤ) (V : Finset (Site d)) : Prop :=
  ∀ t : ℕ, V.card ≤ t → ∀ x ∈ V,
    fodo ((↑V : Set (Site d))ᶜ) η (fun y => if y ∈ outerBoundary (↑V : Set (Site d)) then 1 else 0) t x = 1

/-- `η : ℤ^d → ℤ` is *recurrent* if its restriction to every finite domain is. -/
def Recurrent (η : Site d → ℤ) : Prop := ∀ V : Finset (Site d), RecurrentOn η V

/-! ### The last-wave -/

/-- The terminal odometer of the `n`-wave for `η` starting at `z`: the value at
the first time the wave is constant.  Carry `WaveStabilizable η n z` to know
that time exists. -/
noncomputable def waveTerminal (η : Site d → ℤ) (n : ℕ) (z : Site d) : Site d → ℤ :=
  wave η n z (sInf {T : ℕ | ∀ t : ℕ, T ≤ t → wave η n z t = wave η n z T})

/-- Past the stabilization time the `n`-wave equals its terminal odometer. -/
theorem waveTerminal_spec (η : Site d → ℤ) (n : ℕ) (z : Site d)
    (hs : WaveStabilizable η n z) :
    ∀ t : ℕ, sInf {T : ℕ | ∀ t : ℕ, T ≤ t → wave η n z t = wave η n z T} ≤ t →
      wave η n z t = waveTerminal η n z := by
  intro t ht
  obtain ⟨T, hT⟩ := hs
  have hne : sInf {T : ℕ | ∀ t : ℕ, T ≤ t → wave η n z t = wave η n z T} ∈
      {T : ℕ | ∀ t : ℕ, T ≤ t → wave η n z t = wave η n z T} :=
    Nat.sInf_mem ⟨T, hT⟩
  exact hne t ht

/-- The terminal odometer of a stabilizable wave satisfies the wave equation
away from its centre. -/
theorem waveTerminal_fixed (η : Site d → ℤ) (n : ℕ) (z : Site d)
    (hs : WaveStabilizable η n z) {x : Site d} (hx : x ≠ z) :
    waveTerminal η n z x = (nbrSumZ (waveTerminal η n z) x + η x) / (2 * (d : ℤ)) := by
  have h1 := waveTerminal_spec η n z hs _ (le_refl _)
  have h2 := waveTerminal_spec η n z hs _ (Nat.le_succ _)
  conv_lhs => rw [← h2]
  rw [wave_of_ne _ _ _ _ _ hx, h1]

/-- The last-wave `u_t^{(z)} = u_t^{(M̂_η(z), z)}`. -/
noncomputable def lastWave (η : Site d → ℤ) (z : Site d) : ℕ → Site d → ℤ :=
  wave η (waveThreshold η z) z

/-- The penultimate wave `ũ^{(z)}`, the terminal odometer of the
`(M̂_η(z) - 1)`-wave, and the zero function when `M̂_η(z) = 1`. -/
noncomputable def penultimateWave (η : Site d → ℤ) (z : Site d) : Site d → ℤ :=
  if waveThreshold η z = 1 then 0 else waveTerminal η (waveThreshold η z - 1) z

/-- The penultimate cluster `P(z)` of `(3.3)`. -/
def penultimateCluster (η : Site d → ℤ) (z : Site d) : Set (Site d) :=
  {z} ∪ {x | ∃ y, (lattice d).Adj y x ∧ 0 < penultimateWave η z y}

/-- The last-wave arrival time `T̂(y,x)` of `(3.4)`, valued in `ℕ∞`. -/
noncomputable def lastArrival (η : Site d → ℤ) (y x : Site d) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ 1 ≤ n ∧ 0 < lastWave η y n x}

/-- The penultimate-cluster arrival time `T̃(y,x)` of `(3.5)`, valued in `ℕ∞`. -/
noncomputable def clusterArrival (η : Site d → ℤ) (y x : Site d) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ 1 ≤ n ∧
    ∀ w ∈ penultimateCluster η x, 0 < lastWave η y n w}

/-- A time at which the last wave is positive bounds the arrival time. -/
theorem lastArrival_le (η : Site d → ℤ) (y x : Site d) (n : ℕ) (hn : 1 ≤ n)
    (h : 0 < lastWave η y n x) : lastArrival η y x ≤ (n : ℕ∞) :=
  sInf_le ⟨n, rfl, hn, h⟩

/-- A time at which the last wave is positive on the whole penultimate cluster
bounds the cluster arrival time. -/
theorem clusterArrival_le (η : Site d → ℤ) (y x : Site d) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ w ∈ penultimateCluster η x, 0 < lastWave η y n w) :
    clusterArrival η y x ≤ (n : ℕ∞) :=
  sInf_le ⟨n, rfl, hn, h⟩

/-- The arrival time `T_η(x)` of the exploding sandpile `η + M_η δ₀`, valued in
`ℕ∞`. -/
noncomputable def arrival (η : Site d → ℤ) (x : Site d) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ 1 ≤ n ∧
    0 < podo (fun y => η y + (explosionThreshold η : ℤ) * dirac (0 : Site d) y) n x}

/-- The exploding sandpile `η + M_η δ₀` of the Overview. -/
noncomputable def explodingPile (η : Site d → ℤ) : Site d → ℤ :=
  fun x => η x + (explosionThreshold η : ℤ) * dirac (0 : Site d) x

/-- `[y]`, the nearest lattice point to `y ∈ ℝ^d`, ties broken by the
coordinatewise minimum. -/
noncomputable def nearestSite {d : ℕ} (y : Fin d → ℝ) : Site d := fun i => ⌈y i - 1 / 2⌉

/-! ### Bootstrap percolation -/

open scoped Classical in
/-- The `(Q_n)^c`-frozen odometer with sites constrained to topple at most once,
started from `u_0 = 0` on the background `η`.  This is the parallel toppling
form of bootstrap percolation used in Section 7.3. -/
noncomputable def spanOdo (n : ℕ) (η : Site d → ℤ) : ℕ → Site d → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun x =>
      if x ∉ cube d n then 0
      else if spanOdo n η t x = 1 then 1
      else spanOdo n η t x +
        (if 2 * (d : ℤ) ≤ η x + lap (spanOdo n η t) x then 1 else 0)

/-- `Q_n` is `η`-*internally spanned*: every site of `Q_n` eventually topples. -/
def InternallySpanned (η : Site d → ℤ) (n : ℕ) : Prop :=
  ∀ x ∈ cube d n, ∃ t : ℕ, spanOdo n η t x = 1

/-! ### The background law -/

/-- The one-site law of `η ∼ Bernoulli(a, b, p)`: the value `a` with
probability `p` and `b` with probability `1 - p`. -/
noncomputable def chipLaw (a b : ℤ) (p : ℝ) : Measure ℤ :=
  ENNReal.ofReal p • Measure.dirac a + ENNReal.ofReal (1 - p) • Measure.dirac b

/-- The product measure `P` on backgrounds with one-site law `chipLaw a b p`. -/
noncomputable def productLaw (d : ℕ) (a b : ℤ) (p : ℝ) : Measure (Site d → ℤ) :=
  Measure.infinitePi fun _ : Site d => chipLaw a b p

/-- The law of the paper's `(1.2)`: `2d - 1` chips with probability `p` and
`2d - 2` with probability `1 - p`. -/
noncomputable def toyLaw (d : ℕ) (p : ℝ) : Measure (Site d → ℤ) :=
  productLaw d (2 * d - 1) (2 * d - 2) p

end Exploding
