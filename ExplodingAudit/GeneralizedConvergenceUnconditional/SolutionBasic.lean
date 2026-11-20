import Mathlib

/-!
# GeneralizedConvergenceUnconditional: comparator vocabulary

Definitions used to state the chemical-distance-free result.
-/

open MeasureTheory Filter

namespace Exploding
namespace StatementAudit
namespace GeneralizedConvergenceUnconditional

-- VOCABULARY-BEGIN
/-! ## The lattice (`LatticeProb/Site.lean`) -/

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

/-- A unit vector is not zero. -/
theorem unit_ne_zero {d : ℕ} (i : Fin d) : unit i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unit, Pi.single_eq_same] at this

/-- The nearest-neighbour lattice on `ℤ^d`. -/
def lattice (d : ℕ) : SimpleGraph (Site d) where
  Adj x y := ∃ i : Fin d, y = x + unit i ∨ x = y + unit i
  symm := ⟨fun _ _ h => h.imp fun _ hi => hi.symm⟩
  loopless := ⟨fun x h => by
    obtain ⟨i, hi | hi⟩ := h
    · exact unit_ne_zero i (by have := congrArg (· - x) hi; simpa using this.symm)
    · exact unit_ne_zero i (by have := congrArg (· - x) hi; simpa using this.symm)⟩

/-- The vertices joined to `x` inside `S`, along edges of the lattice. -/
def componentIn {d : ℕ} (S : Set (Site d)) (x : Site d) : Set (Site d) :=
  {y | ∃ (hx : x ∈ S) (hy : y ∈ S), ((lattice d).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩}

variable {d : ℕ}

/-! ## Parallel toppling (`Exploding/Support/Toppling.lean`) -/

/-- The unit mass at `z`. -/
def dirac (z : Site d) : Site d → ℤ := fun x => if x = z then 1 else 0

/-- The sum of `u` over the `2d` neighbours of `x`, direction by direction. -/
def nbrSumZ (u : Site d → ℤ) (x : Site d) : ℤ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))

/-- The lattice Laplacian `Δ u (x) = ∑_{y ∼ x} (u y - u x)`. -/
def lap (u : Site d → ℤ) (x : Site d) : ℤ := nbrSumZ u x - 2 * d * u x

/-- The parallel toppling odometer `v_t` for the initial sandpile `s₀`. -/
def podo (s0 : Site d → ℤ) : ℕ → Site d → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun x =>
      podo s0 t x + (if 2 * d ≤ s0 x + lap (podo s0 t) x then 1 else 0)

/-- `s₀` is stabilizable: its parallel toppling odometer is eventually constant. -/
def Stabilizable (s0 : Site d → ℤ) : Prop :=
  ∃ T : ℕ, ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T

/-- The explosion threshold `M_η = min {n ≥ 1 : η + n δ₀ is not stabilizable}`. -/
noncomputable def explosionThreshold (η : Site d → ℤ) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ ¬ Stabilizable (fun x => η x + n * dirac (0 : Site d) x)}

/-! ## The exploding sandpile and the nearest site (`Exploding/Support/Vocab.lean`) -/

/-- The exploding sandpile `η + M_η δ₀`. -/
noncomputable def explodingPile (η : Site d → ℤ) : Site d → ℤ :=
  fun x => η x + (explosionThreshold η : ℤ) * dirac (0 : Site d) x

/-- `[y]`, the nearest lattice point to `y ∈ ℝ^d`, ties broken by the coordinatewise minimum. -/
noncomputable def nearestSite {d : ℕ} (y : Fin d → ℝ) : Site d := fun i => ⌈y i - 1 / 2⌉

/-! ## Boxes and distances (`Exploding/Support/Vocab.lean`) -/

/-- The box `Q_k = {x ∈ ℤ^d : 1 ≤ x ≤ k}`. -/
def cube (d k : ℕ) : Set (Site d) := {x | ∀ i, 1 ≤ x i ∧ x i ≤ (k : ℤ)}

/-- The sup-norm box `[-n, n]^d`. -/
def cent (d : ℕ) (n : ℕ) : Set (Site d) := {x | ∀ i, |x i| ≤ (n : ℤ)}

/-- The Manhattan norm `|x|`. -/
def mnorm (x : Site d) : ℤ := ∑ i, |x i|

/-! ## Bootstrap percolation (`Exploding/Support/Vocab.lean`) -/

open scoped Classical in
/-- The `(Q_n)^c`-frozen odometer with sites constrained to topple at most once. -/
noncomputable def spanOdo (n : ℕ) (η : Site d → ℤ) : ℕ → Site d → ℤ
  | 0 => fun _ => 0
  | t + 1 => fun x =>
      if x ∉ cube d n then 0
      else if spanOdo n η t x = 1 then 1
      else spanOdo n η t x +
        (if 2 * (d : ℤ) ≤ η x + lap (spanOdo n η t) x then 1 else 0)

/-- `Q_n` is `η`-internally spanned: every site of `Q_n` eventually topples. -/
def InternallySpanned (η : Site d → ℤ) (n : ℕ) : Prop :=
  ∀ x ∈ cube d n, ∃ t : ℕ, spanOdo n η t x = 1

/-! ## The background law (`Exploding/Support/Vocab.lean`) -/

/-- The one-site law: the value `a` with probability `p` and `b` with probability `1 - p`. -/
noncomputable def chipLaw (a b : ℤ) (p : ℝ) : Measure ℤ :=
  ENNReal.ofReal p • Measure.dirac a + ENNReal.ofReal (1 - p) • Measure.dirac b

/-- The product measure on backgrounds with one-site law `chipLaw a b p`. -/
noncomputable def productLaw (d : ℕ) (a b : ℤ) (p : ℝ) : Measure (Site d → ℤ) :=
  Measure.infinitePi fun _ : Site d => chipLaw a b p

/-- The law of `(2)`: `2d - 1` chips with probability `p` and `2d - 2` with probability `1 - p`. -/
noncomputable def toyLaw (d : ℕ) (p : ℝ) : Measure (Site d → ℤ) :=
  productLaw d (2 * d - 1) (2 * d - 2) p

/-! ## Bernoulli percolation (`Exploding/Support/Percolation.lean`) -/

/-- The law of one Bernoulli(`q`) bit. -/
noncomputable def bitLaw (q : ℝ) : Measure Bool :=
  ENNReal.ofReal q • Measure.dirac true + ENNReal.ofReal (1 - q) • Measure.dirac false

/-- Bernoulli site percolation of density `q` on `ℤ^d`. -/
noncomputable def sitePercolation (d : ℕ) (q : ℝ) : Measure (Site d → Bool) :=
  Measure.infinitePi fun _ : Site d => bitLaw q

/-- The open sites of a configuration of bits. -/
def openSites (ω : Site d → Bool) : Set (Site d) := {x | ω x = true}

/-- `C` is an infinite open cluster of `ω`. -/
def IsInfiniteOpenCluster (ω : Site d → Bool) (C : Set (Site d)) : Prop :=
  C.Infinite ∧ ∃ i ∈ C, C = componentIn (openSites ω) i

/-- Bernoulli bond percolation of density `q` on `ℤ^d`. -/
noncomputable def bondPercolation (d : ℕ) (q : ℝ) : Measure (Site d × Fin d → Bool) :=
  Measure.infinitePi fun _ : Site d × Fin d => bitLaw q

/-- The graph on `ℤ^d` of the open bonds of a configuration. -/
def openBondGraph (ω : Site d × Fin d → Bool) : SimpleGraph (Site d) :=
  SimpleGraph.fromRel fun x y => ∃ i : Fin d, y = x + unit i ∧ ω (x, i) = true

/-- The percolation probability `θ(q)`: the origin's open cluster is infinite. -/
noncomputable def bondTheta (d : ℕ) (q : ℝ) : ENNReal :=
  bondPercolation d q {ω | {x : Site d | (openBondGraph ω).Reachable 0 x}.Infinite}

/-- The critical probability of bond percolation, `p_c = sup {q : θ(q) = 0}`. -/
noncomputable def bondCritical (d : ℕ) : ℝ :=
  sSup {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ bondTheta d q = 0}

/-- The product law of independent Bernoulli(`q`) bits indexed by `S`. -/
noncomputable def bernoulliProduct (S : Type) (q : ℝ) : Measure (S → Bool) :=
  Measure.infinitePi fun _ : S => bitLaw q

/-- A set of configurations of bits indexed by `S` is increasing. -/
def IsIncreasingSet {S : Type} (A : Set (S → Bool)) : Prop :=
  ∀ ω ω' : S → Bool, ω ∈ A → (∀ s, ω s = true → ω' s = true) → ω' ∈ A

/-- The law `μ` of a field of bits has dependence graph `G`. -/
def HasDependenceGraph {S : Type} (G : SimpleGraph S) (μ : Measure (S → Bool)) : Prop :=
  ∀ I J : Finset S, Disjoint I J → (∀ a ∈ I, ∀ b ∈ J, ¬ G.Adj a b) →
    ProbabilityTheory.IndepFun (fun ω : S → Bool => fun i : I => ω i)
      (fun ω : S → Bool => fun j : J => ω j) μ

/-! ## The four cited results, as hypotheses (`Exploding/External/`) -/

/-- Corollary 1.4 of Liggett, Schonmann and Stacey (domination by product measures). -/
def LiggettSchonmannStaceyBoundedDegree : Prop :=
  ∀ (S : Type) [Countable S] (G : SimpleGraph S) (Δ : ℕ), 1 ≤ Δ →
    (∀ s : S, (G.neighborSet s).Finite ∧ (G.neighborSet s).ncard ≤ Δ) →
    (∀ s : S, (G.connectedComponentMk s).supp.Finite →
      ∃ t ∈ (G.connectedComponentMk s).supp, (G.neighborSet t).ncard < Δ) →
    ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 →
      ∃ p : ℝ, p < 1 ∧ ∀ μ : Measure (S → Bool), IsProbabilityMeasure μ →
        HasDependenceGraph G μ → (∀ s : S, ENNReal.ofReal p ≤ μ {ω | ω s = true}) →
        ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A →
          bernoulliProduct S ρ A ≤ μ A

/-- Lemma 5.2 of Mathieu (polylogarithmic volume of the holes of the infinite cluster). -/
def MathieuHoleVolume : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q₀ : ℝ, q₀ < 1 ∧ ∀ q : ℝ, q₀ < q → q ≤ 1 →
    ∀ᵐ ω ∂(sitePercolation d q), ∀ C : Set (Site d), IsInfiniteOpenCluster ω C →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ C →
        (componentIn Cᶜ x).Finite ∧
          ((componentIn Cᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)

/-- Theorem 1.1 of Antal and Pisztora (linear chemical distance in supercritical bond percolation). -/
def AntalPisztoraChemicalDistance : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ q : ℝ, bondCritical d < q → q ≤ 1 →
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site d, (R : ℤ) ≤ mnorm y →
      bondPercolation d q
          {ω | ∃ m : ℕ, (openBondGraph ω).edist 0 y = (m : ℕ∞) ∧ ρ * (mnorm y : ℝ) < (m : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ))))

/-- Schonmann's large-deviation bound for bootstrap percolation (Proposition 7.4). -/
def SchonmannBootstrap : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ p : ℝ, 0 < p → p ≤ 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      ENNReal.ofReal (1 - c * Real.exp (-(C * (n : ℝ)))) ≤
        productLaw d (2 * (d : ℤ)) (d : ℤ) p {η | InternallySpanned η n}

/-- Robust in the sandpile vocabulary. -/
def Robust (η : Site d → ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → Stabilizable (fun x => η x + n * dirac (0 : Site d) x)

/-- Explosive in the sandpile vocabulary. -/
def Explosive (η : Site d → ℤ) : Prop := ¬ Robust η

/-- arrival in the sandpile vocabulary. -/
noncomputable def arrival (η : Site d → ℤ) (x : Site d) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ 1 ≤ n ∧
    0 < podo (fun y => η y + (explosionThreshold η : ℤ) * dirac (0 : Site d) y) n x}

open scoped Classical in
/-- fodo in the sandpile vocabulary. -/
noncomputable def fodo (S : Set (Site d)) (s0 w0 : Site d → ℤ) : ℕ → Site d → ℤ
  | 0 => w0
  | t + 1 => fun x =>
      if x ∈ S then w0 x
      else fodo S s0 w0 t x + (if 2 * d ≤ s0 x + lap (fodo S s0 w0 t) x then 1 else 0)

open scoped Classical in
/-- wave in the sandpile vocabulary. -/
noncomputable def wave (η : Site d → ℤ) (n : ℕ) (z : Site d) : ℕ → Site d → ℤ
  | 0 => fun x => if x = z then (n : ℤ) else 0
  | t + 1 => fun x =>
      if x = z then (n : ℤ)
      else (nbrSumZ (wave η n z t) x + η x) / (2 * d)

/-- WaveStabilizable in the sandpile vocabulary. -/
def WaveStabilizable (η : Site d → ℤ) (n : ℕ) (z : Site d) : Prop :=
  ∃ T : ℕ, ∀ t : ℕ, T ≤ t → wave η n z t = wave η n z T

/-- waveThreshold in the sandpile vocabulary. -/
noncomputable def waveThreshold (η : Site d → ℤ) (z : Site d) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z}

/-- lastWave in the sandpile vocabulary. -/
noncomputable def lastWave (η : Site d → ℤ) (z : Site d) : ℕ → Site d → ℤ :=
  wave η (waveThreshold η z) z

/-- lastArrival in the sandpile vocabulary. -/
noncomputable def lastArrival (η : Site d → ℤ) (y x : Site d) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, t = (n : ℕ∞) ∧ 1 ≤ n ∧ 0 < lastWave η y n x}

/-- outerBoundary in the sandpile vocabulary. -/
def outerBoundary (A : Set (Site d)) : Set (Site d) :=
  {x | x ∉ A ∧ ∃ y ∈ A, (lattice d).Adj x y}

/-- closureN in the sandpile vocabulary. -/
def closureN (A : Set (Site d)) : Set (Site d) := A ∪ outerBoundary A

/-- br in the sandpile vocabulary. -/
def br (A : Set (Site d)) : Set (Site d) :=
  {z | ∀ i, (∃ y ∈ A, y i ≤ z i) ∧ (∃ y ∈ A, z i ≤ y i)}

/-- rboxShift in the sandpile vocabulary. -/
def rboxShift (k : Fin d → ℕ) (j : Site d) : Set (Site d) :=
  {x | ∀ i, 1 + (k i : ℤ) * j i ≤ x i ∧ x i ≤ (k i : ℤ) * j i + (k i : ℤ)}

/-- rline in the sandpile vocabulary. -/
def rline (k : Fin d → ℕ) (j : Site d) (i : Fin d) (z : Site d) : Set (Site d) :=
  {x | (1 + (k i : ℤ) * j i ≤ x i ∧ x i ≤ (k i : ℤ) * j i + (k i : ℤ)) ∧ ∀ l, l ≠ i → x l = z l}

/-- StronglyBoxCrossed in the sandpile vocabulary. -/
def StronglyBoxCrossed (η : Site d → ℤ) (k : Fin d → ℕ) (j : Site d) : Prop :=
  ∀ (i : Fin d) (z : Site d), z ∈ closureN (rboxShift k j) →
    ∀ x ∈ rboxShift k j,
      1 ≤ fodo ((rboxShift k j)ᶜ ∪ rline k j i z) η
        (Set.indicator (rline k j i z) 1) (∏ l, k l) x

/-- FiniteRangeOfDependence in the sandpile vocabulary. -/
def FiniteRangeOfDependence (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∃ K : ℕ, ∀ I J : Finset (Site d), (∀ a ∈ I, ∀ b ∈ J, (K : ℤ) < mnorm (a - b)) →
    ProbabilityTheory.IndepFun (fun η : Site d → ℤ => fun i : I => η i)
      (fun η : Site d → ℤ => fun j : J => η j) P

/-- PathFillingHyp in the sandpile vocabulary. -/
def PathFillingHyp (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ᵐ η ∂P, ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∀ (m : ℕ) (z : ℕ → Site d),
      Real.log n ^ γ ≤ (m : ℝ) →
      (∀ i, i < m → z i ∈ cent d n) →
      (∀ i j, i < m → j < m → z i = z j → i = j) →
      (∀ i, i + 1 < m → (lattice d).Adj (z i) (z (i + 1))) →
      ∀ t : ℕ, m ^ d ≤ t → ∀ x ∈ br (z '' {i : ℕ | i < m}),
        1 ≤ fodo (z '' {i : ℕ | i < m}) η (Set.indicator (z '' {i : ℕ | i < m}) 1) t x

/-- StronglyBoxCrossingHyp in the sandpile vocabulary. -/
def StronglyBoxCrossingHyp (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ k : Fin d → ℕ, (∀ i, 0 < k i) ∧
    ∀ j : Site d, ENNReal.ofReal (1 - δ) < P {η | StronglyBoxCrossed η k j}

/-- WaveApproximationHyp in the sandpile vocabulary. -/
def WaveApproximationHyp (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ᵐ η ∂P, Explosive η →
    (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x ∈ cent d n,
        |((lastArrival η (0 : Site d) x).toNat : ℝ) - ((arrival η x).toNat : ℝ)| ≤ ε * n

/-- InOmega in the sandpile vocabulary. -/
def InOmega (d : ℕ) (ηmin : ℤ) (η : Site d → ℤ) : Prop :=
  ∀ x, ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1

/-- StationaryOn in the sandpile vocabulary. -/
def StationaryOn (d : ℕ) (L : AddSubgroup (Site d)) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ y ∈ L, P.map (fun η : Site d → ℤ => fun z => η (y + z)) = P

/-- MeasurableErgodicOn in the sandpile vocabulary. -/
def MeasurableErgodicOn (d : ℕ) (L : AddSubgroup (Site d))
    (P : Measure (Site d → ℤ)) : Prop :=
  ∀ E : Set (Site d → ℤ), MeasurableSet E →
    E = ⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (y + z)) '' E →
    P E = 0 ∨ P E = 1
-- VOCABULARY-END

end GeneralizedConvergenceUnconditional
end StatementAudit
end Exploding
