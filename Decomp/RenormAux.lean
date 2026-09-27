/-
Proposition 2.2 of the paper: an infinite connected set of good cubes on the
macroscopic lattice, with small holes and a linear chemical distance.

DECOMPOSITION (not a proof attempt).  The paper's argument (exploding.tex:478)
has three steps.  The good cubes form an independent site field (Step 0).  The good
edges, whose two cubes are both good, have a dependence graph of degree `4d - 2`, so
Corollary 1.4 of Liggett, Schonmann and Stacey (`hLSSB`) makes them dominate independent
bond percolation of density close to `1` (Step 1).  The construction of `C_∞` from that
bond process, with Lemma 5.2 of Mathieu (`hHole`) for the holes and Theorem 1.1 of Antal
and Pisztora (`hChem`) for the chemical distance, gives the three clauses (Step 2).
-/
import Exploding.Support.Vocab
import Exploding.Frozen.CrossingTime
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora
import LatticeProb.Prob.Blocks

open Exploding LatticeProb MeasureTheory

namespace Exploding.Frozen.RenormalizationDec

variable {d : ℕ}

/-! ### Step 0, part (i): `fodo`/`GoodCube`/`GoodAt` depend only on the background restricted
to the relevant box, and the boxes for distinct macroscopic sites are disjoint. -/

/-- Auxiliary (elementary, general): the `S`-frozen odometer depends on the background only
through its values off `S`, by induction on `t`: frozen sites never move, and at an unfrozen
site the recursion uses only the current odometer (equal by the inductive hypothesis) and the
background's own value there, which is exactly where the hypothesis applies. Uses
`Exploding.fodo_succ`, unfolds `Exploding.fconf`, `Exploding.lap`. -/
theorem aux_renorm_iid_field_fodo_congr (S : Set (Site d)) (s0 s0' w0 : Site d → ℤ)
    (h : ∀ x, x ∉ S → s0 x = s0' x) (t : ℕ) (x : Site d) :
    fodo S s0 w0 t x = fodo S s0' w0 t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    have hfun : fodo S s0 w0 t = fodo S s0' w0 t := funext ih
    rw [fodo_succ, fodo_succ]
    by_cases hx : x ∈ S
    · rw [if_pos hx, if_pos hx]
    · have hf : fconf S s0 w0 t x = fconf S s0' w0 t x := by
        simp only [fconf, lap, hfun, h x hx]
      rw [if_neg hx, if_neg hx, hfun, hf]

/-- Auxiliary: `GoodCube` depends on the background only through its restriction to `cube d k`,
since `crossOdo`/`crossingTime` are built from the frozen odometer on the frozen set
`(cube d k)ᶜ ∪ line d k i z`, whose complement is `⊆ cube d k`. Uses
`aux_renorm_iid_field_fodo_congr` and unfolds `Exploding.crossOdo`, `Exploding.crossingTime`,
`Exploding.GoodCube`. -/
theorem aux_renorm_iid_field_goodcube_congr (k : ℕ) (η η' : Site d → ℤ)
    (heq : ∀ x ∈ cube d k, η x = η' x) : GoodCube η k ↔ GoodCube η' k := by
  have hco : ∀ (i : Fin d) (z : Site d) (t : ℕ) (x : Site d),
      crossOdo η k i z t x = crossOdo η' k i z t x := by
    intro i z t x
    refine aux_renorm_iid_field_fodo_congr _ η η' _ (fun y hy => ?_) t x
    refine heq y ?_
    by_contra hyc
    exact hy (Set.mem_union_left _ hyc)
  have hct : ∀ (i : Fin d) (z : Site d), crossingTime η k i z = crossingTime η' k i z := by
    intro i z
    simp only [crossingTime, hco]
  simp only [GoodCube, hct]

/-- Auxiliary: `GoodAt η k i` depends on `η` only through its values on the shifted box
`k • i + cube d k`, a direct corollary of `aux_renorm_iid_field_goodcube_congr` applied to the
shifted backgrounds. Unfolds `Exploding.GoodAt`. -/
theorem aux_renorm_iid_field_goodat_congr (k : ℕ) (i : Site d) (η η' : Site d → ℤ)
    (heq : ∀ x ∈ cube d k, η (x + (k : ℤ) • i) = η' (x + (k : ℤ) • i)) :
    GoodAt η k i ↔ GoodAt η' k i :=
  aux_renorm_iid_field_goodcube_congr k (fun x => η (x + (k : ℤ) • i))
    (fun x => η' (x + (k : ℤ) • i)) heq

/-- Auxiliary: for `k ≥ 1`, the boxes `k • i + cube d k` and `k • j + cube d k` used by `GoodAt`
at distinct macroscopic sites `i ≠ j` are disjoint. If a point lay in both, the coordinatewise
difference `k • (j - i)` would have every entry of absolute value `< k` (a difference of two
values in `[1, k]`), forcing `j = i`. Elementary integer arithmetic. -/
theorem aux_renorm_iid_field_box_disjoint (k : ℕ) (hk : 1 ≤ k) (i j : Site d) (hij : i ≠ j)
    (x y : Site d) (hx : x ∈ cube d k) (hy : y ∈ cube d k) :
    x + (k : ℤ) • i ≠ y + (k : ℤ) • j := by
  intro heq
  apply hij
  funext l
  have hl : x l + (k : ℤ) * i l = y l + (k : ℤ) * j l := by
    have h := congrFun heq l
    simpa [smul_eq_mul] using h
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have h1 := hx l; have h2 := hy l
  rcases lt_trichotomy (i l) (j l) with hm | hm | hm
  · nlinarith [h1.1, h1.2, h2.1, h2.2]
  · exact hm
  · nlinarith [h1.1, h1.2, h2.1, h2.2]

/-! ### Step 0, part (ii): reading off the i.i.d. field from `Measure.infinitePi`. -/

/-- Auxiliary: `chipLaw a b p` is a probability measure for `0 ≤ p ≤ 1`. Mirrors the working
argument of `aux_ct_ae_bounded` in `prop-crossing-time-dec/node.lean`. Uses `Exploding.chipLaw`,
`ENNReal.ofReal_add`, `ENNReal.ofReal_one`. -/
theorem aux_renorm_iid_field_chiplaw_prob (a b : ℤ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (chipLaw a b p) := by
  have h_add : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
    calc ENNReal.ofReal p + ENNReal.ofReal (1 - p)
        = ENNReal.ofReal (p + (1 - p)) := by rw [ENNReal.ofReal_add hp0 (by linarith)]
      _ = ENNReal.ofReal 1 := by ring_nf
      _ = 1 := ENNReal.ofReal_one
  refine { measure_univ := ?_ }
  unfold chipLaw
  simp [h_add]

/-- Auxiliary: `toyLaw` is invariant under a fixed coordinate shift, since it is
`Measure.infinitePi` of a CONSTANT family and shifting reindexes along a bijection of `Site d`.
Uses `MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj` (injectivity of `x ↦ x + k • i` via
cancelling the shift back off) and `Exploding.toyLaw`, `Exploding.productLaw`. -/
theorem aux_renorm_iid_field_shift_inv (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (k : ℕ) (i : Site d) :
    (toyLaw d p).map (fun η x => η (x + (k : ℤ) • i)) = toyLaw d p := by
  set a : ℤ := 2 * (d : ℤ) - 1 with ha
  set b : ℤ := 2 * (d : ℤ) - 2 with hb
  have hpm : ∀ j : Site d, IsProbabilityMeasure ((fun _ : Site d => chipLaw a b p) j) :=
    fun _ => aux_renorm_iid_field_chiplaw_prob a b p (by linarith) (by linarith)
  have hinj : Function.Injective (fun x : Site d => x + (k : ℤ) • i) := fun x y h => by
    simpa using congrArg (fun z => z - (k : ℤ) • i) h
  have h := @Measure.map_infinitePi_infinitePi_of_inj (Site d) (Site d) _ _
    (fun _ : Site d => chipLaw a b p) hpm _ hinj
  simpa [toyLaw, productLaw, ha, hb] using h

/-- Auxiliary: given `{η | GoodCube η k}` measurable, `GoodAt` has the SAME probability
`toyLaw d p {η | GoodCube η k}` at every macroscopic site `i`: pulling the event back along the
shift `η ↦ η(· + k•i)` (measure-preserving by `aux_renorm_iid_field_shift_inv`) lands exactly on
`{η | GoodAt η k i}`, by `Exploding.GoodAt`'s definition. Uses `MeasureTheory.Measure.map_apply`. -/
theorem aux_renorm_iid_field_marginal_eq (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (k : ℕ)
    (hmeas : MeasurableSet {η : Site d → ℤ | GoodCube η k}) (i : Site d) :
    toyLaw d p {η : Site d → ℤ | GoodAt η k i} = toyLaw d p {η : Site d → ℤ | GoodCube η k} := by
  have hmeasf : Measurable (fun η : Site d → ℤ => fun x => η (x + (k : ℤ) • i)) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply _
  have hpre : (fun η : Site d → ℤ => fun x => η (x + (k : ℤ) • i)) ⁻¹' {η | GoodCube η k}
      = {η : Site d → ℤ | GoodAt η k i} := rfl
  rw [← hpre, ← Measure.map_apply hmeasf hmeas, aux_renorm_iid_field_shift_inv p hp hp1 k i]

/-- [NEEDS FURTHER SPLIT] `GoodCube` is measurable. Since `cube d k` is finite and `crossOdo`
touches `η` only through its values on `cube d k` (`aux_renorm_iid_field_fodo_congr`), `GoodCube
η k` factors through the finite restriction `η ↦ (cube d k).restrict η`; as
`Int.instMeasurableSpace : MeasurableSpace ℤ := ⊤`, every subset of a FINITE power of `ℤ` is
measurable (all its points are, and it is countable), so the pulled-back event is measurable.
What is missing from `Exploding.Support` is exactly the "depends on finitely many coordinates ⟹
measurable" packaging lemma (no analogue of `MeasurableSet.pi` for an arbitrary, not just
box-shaped, subset of a finite-coordinate product is present) together with a named finiteness
lemma for `cube d k` itself (only ever carried as a bare hypothesis `hfin : (cube d k).Finite`
in `prop-crossing-time-dec/node.lean`, never proved there either). -/
theorem aux_renorm_iid_field_measurable (k : ℕ) :
    MeasurableSet {η : Site d → ℤ | GoodCube η k} := by
  sorry

/-- [NEEDS FURTHER SPLIT] The `GoodAt`-events are independent across macroscopic sites. Given
`aux_renorm_iid_field_measurable` (hence, via `aux_renorm_iid_field_goodat_congr`, measurability
of the analogous event for every shifted box) and `aux_renorm_iid_field_box_disjoint` (the boxes
are pairwise disjoint), this is the same "events reading disjoint blocks of an i.i.d. field are
independent" fact as `LatticeProb.iIndepSet_of_pairwise_disjoint` (`LatticeProb/Prob/Blocks.lean`)
— but that lemma, and the `map_blocks`/`iIndepFun_restrict_of_pairwise_disjoint` chain it is
built from, is hardcoded to `Measure ℝ` there. The generic replacement route is
`MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj` +
`MeasureTheory.Measure.infinitePi_map_piCurry` (both codomain-generic, unlike the `LatticeProb`
wrapper, and already used for `aux_renorm_iid_field_shift_inv` above) composed with
`ProbabilityTheory.iIndepFun.comp`, mirroring `LatticeProb.blockIndex` / `LatticeProb.map_blocks`
verbatim with `ℤ` in place of `ℝ` (`LatticeProb.blockIndex`/`blockIndex_injective` themselves are
already codomain-generic, so they can be reused directly after `import LatticeProb.Prob.Blocks`).
This is mechanical but multi-step bookkeeping (reindex along `blockIndex`, curry, extract
`iIndepSet` from `iIndep` of the generated block algebras via
`ProbabilityTheory.iIndepSet_iff_iIndep`), left as a further split rather than attempted inline. -/
theorem aux_renorm_iid_field_indep (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (k : ℕ) (hk : 1 ≤ k) :
    ProbabilityTheory.iIndepSet (fun i : Site d => {η : Site d → ℤ | GoodAt η k i})
      (toyLaw d p) := by
  sorry

set_option linter.unusedVariables false in
/-- Step 0 (exploding.tex:499, "the set of good cubes ... dominates ... site
percolation").  For fixed `k`, distinct macroscopic sites `i ≠ j` use disjoint
translates `Q_k(i) ≠ Q_k(j)` of the box, and `GoodAt η k i` depends only on
`η` restricted to `Q_k(i)` (through `crossOdo`/`fodo`, which freeze the
odometer outside `cube d k` after the shift).  Since `toyLaw d p` is a product
measure, this makes `{GoodAt η k i}_{i : Site d}` a field of INDEPENDENT
events, each of probability `≥ 1 - δ` by `Exploding.Frozen.crossing_time`
applied to `k` large enough for the target `δ`.  This is the exact statement
that should replace "dominates a percolation process": here it literally IS
one, no stochastic domination is needed.  This is new content (elementary,
not a literature citation) but is nontrivial measure-theoretic bookkeeping
about `Measure.infinitePi` / `IsInfiniteConnectedGoodSet`'s dependence on disjoint
coordinate blocks; needs further split into (i) a measurability/independence
lemma for `GoodAt` under coordinate-shift, and (ii) reading off i.i.d.-ness
from `Measure.infinitePi`. -/
theorem aux_renorm_iid_field (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (hcross : ENNReal.ofReal (1 - δ) ≤ toyLaw d p {η | GoodCube η k}) :
    ∃ q : ℝ, 1 - δ ≤ q ∧ q ≤ 1 ∧
      ProbabilityTheory.iIndepSet (fun i : Site d => {η : Site d → ℤ | GoodAt η k i})
        (toyLaw d p) ∧
      ∀ i : Site d, toyLaw d p {η | GoodAt η k i} = ENNReal.ofReal q := by
  haveI : IsProbabilityMeasure (toyLaw d p) := by
    haveI := aux_renorm_iid_field_chiplaw_prob (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p
      (by linarith) (by linarith)
    unfold toyLaw productLaw; infer_instance
  refine ⟨(toyLaw d p {η | GoodCube η k}).toReal, ?_, ?_, ?_, ?_⟩
  · rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)] at hcross
    exact hcross
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (prob_le_one (μ := toyLaw d p) (s := {η | GoodCube η k}))
  · exact aux_renorm_iid_field_indep p hp hp1 k hk
  · intro i
    rw [aux_renorm_iid_field_marginal_eq p hp hp1 k (aux_renorm_iid_field_measurable k) i,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-! ### Step 1: the macroscopic-edge line graph and its bounded-degree domination. -/

/-- The line graph on macroscopic edges: two distinct edges are adjacent when they share an
endpoint macroscopic site. -/
def renormEdgeGraph (d : ℕ) : SimpleGraph (Site d × Fin d) :=
  SimpleGraph.fromRel fun e e' =>
    ({e.1, e.1 + unit e.2} ∩ {e'.1, e'.1 + unit e'.2} : Set (Site d)).Nonempty

/-- [NEEDS FURTHER SPLIT] Every macroscopic edge has at most `4d - 2` neighbours in
`renormEdgeGraph`: each of its two endpoint sites carries `2d` incident edges (one per direction,
forward and backward), of which at most `2d - 1` are neighbours other than itself, and no third
edge joins both endpoints (no multi-edges on `ℤ^d`). Needs a `Fintype`/cardinality argument
enumerating the `4d - 2` candidate edges through `e.1` and `e.1 + unit e.2`, not present in
`Exploding.Support` (which has no incidence-counting lemmas for `lattice d`). -/
theorem aux_renorm_edge_degree_bound (d : ℕ) (e : Site d × Fin d) :
    ((renormEdgeGraph d).neighborSet e).Finite ∧
      ((renormEdgeGraph d).neighborSet e).ncard ≤ 4 * d - 2 := by
  sorry

/-- [NEEDS FURTHER SPLIT] `renormEdgeGraph d` has no finite connected component: it is the line
graph of the connected, infinite, vertex-transitive grid `Exploding.lattice`, so every two edges
are joined by a finite chain of edge-adjacencies through a lattice path between their endpoints.
Needs an explicit path-following induction on `lattice d`'s adjacency (`Exploding.adj_add_unit`,
`Exploding.adj_sub_unit`), not present in `Exploding.Support`. -/
theorem aux_renorm_edge_no_finite_component (d : ℕ) (e : Site d × Fin d) :
    ¬ ((renormEdgeGraph d).connectedComponentMk e).supp.Finite := by
  sorry

open scoped Classical in
/-- [NEEDS FURTHER SPLIT] The pushforward law of the macroscopic-edge field has
`renormEdgeGraph d` as a dependence graph: if two finite sets of edges `I`, `J` have no
`renormEdgeGraph`-adjacency between them, the macroscopic sites they touch are disjoint, so the
restrictions of the `GoodAt`-field to those two (disjoint, finite) sets of macroscopic sites are
independent by `aux_renorm_iid_field_indep`, and the edge indicators are measurable functions of
those restrictions alone. Needs the same "independence of a finite sub-family survives composing
with per-index functions" packaging as `aux_renorm_iid_field_indep` (flagged above), applied one
level up, via `ProbabilityTheory.iIndepFun.comp`. -/
theorem aux_renorm_edge_dependence_graph (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (k : ℕ) :
    HasDependenceGraph (renormEdgeGraph d)
      ((toyLaw d p).map (fun η (e : Site d × Fin d) =>
        decide (GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2)))) := by
  sorry

/-- [NEEDS FURTHER SPLIT] `{η | GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2)}` is measurable, a
direct corollary of `aux_renorm_iid_field_measurable` and `aux_renorm_iid_field_goodat_congr`'s
underlying box-dependence once `MeasurableSet.inter` and a shift-composition measurability fact
for the two boxes are assembled; recorded separately since `aux_renorm_iid_field_measurable`
itself is still open. -/
theorem aux_renorm_edge_measurable (k : ℕ) (e : Site d × Fin d) :
    MeasurableSet {η : Site d → ℤ | GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2)} := by
  have hshift (i : Site d) : Measurable (fun η : Site d → ℤ => fun x => η (x + (k:ℤ) • i)) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply (x + (k:ℤ) • i)
  have hgood (i : Site d) : MeasurableSet {η : Site d → ℤ | GoodAt η k i} := by
    have : {η : Site d → ℤ | GoodAt η k i} =
        (fun η : Site d → ℤ => fun x => η (x + (k:ℤ) • i)) ⁻¹' {η | GoodCube η k} := rfl
    rw [this]
    exact (aux_renorm_iid_field_measurable k).preimage (hshift i)
  exact (hgood e.1).inter (hgood (e.1 + unit e.2))

/-- The probability that a macroscopic edge is good is `q * q`: its two cubes are distinct
macroscopic sites (`e.1 ≠ e.1 + unit e.2`, since `unit e.2 ≠ 0`), so
`ProbabilityTheory.iIndepSet`/`ProbabilityTheory.iIndepSet_iff_iIndep` +
`ProbabilityTheory.iIndep.indep` give independence of `{GoodAt · k e.1}` and
`{GoodAt · k (e.1+unit e.2)}` as generated `σ`-algebras, and `IndepSet` unfolds to the product of
the two events' measures. -/
theorem aux_renorm_edge_marginal (p q : ℝ) (k : ℕ)
    (hindep : ProbabilityTheory.iIndepSet (fun i : Site d => {η : Site d → ℤ | GoodAt η k i})
        (toyLaw d p))
    (hmarg : ∀ i : Site d, toyLaw d p {η | GoodAt η k i} = ENNReal.ofReal q)
    (e : Site d × Fin d) :
    toyLaw d p {η : Site d → ℤ | GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2)}
      = ENNReal.ofReal q * ENNReal.ofReal q := by
  sorry

open scoped Classical in
/-- Step 1 (Corollary 1.4 of Liggett, Schonmann and Stacey, through `hLSSB`).  Call the
macroscopic edge `(i, l)`, joining `i` and `i + e_l`, good when both of its cubes are good.
When the good cubes form an independent field of density `q`, two edges without a common
cube are independent, and each edge shares a cube with `4d - 2` others, so the law of the
good-edge field has the line graph of `ℤ^d` as a dependence graph, of degree `4d - 2`.  For
every `ρ < 1`, once `q` is close enough to `1`, the corollary makes that law dominate Bernoulli
bond percolation of density `ρ` on measurable increasing events. -/
theorem aux_renorm_edge_domination (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (k : ℕ) (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ q0 : ℝ, q0 < 1 ∧ ∀ q : ℝ, q0 < q → q ≤ 1 →
      (ProbabilityTheory.iIndepSet (fun i : Site d => {η : Site d → ℤ | GoodAt η k i})
          (toyLaw d p) ∧ ∀ i : Site d, toyLaw d p {η | GoodAt η k i} = ENNReal.ofReal q) →
      ∀ A : Set (Site d × Fin d → Bool), MeasurableSet A → IsIncreasingSet A →
        bondPercolation d ρ A ≤
          toyLaw d p ((fun η (e : Site d × Fin d) =>
            decide (GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2))) ⁻¹' A) := by
  obtain ⟨p', hp'lt1, hdom⟩ := hLSSB (Site d × Fin d) (renormEdgeGraph d) (4 * d - 2)
    (by omega) (aux_renorm_edge_degree_bound d)
    (fun e he => absurd he (aux_renorm_edge_no_finite_component d e)) ρ hρ0 hρ1
  have hq0lt1 : Real.sqrt p' < 1 := by
    by_cases h0 : 0 ≤ p'
    · calc Real.sqrt p' < Real.sqrt 1 := Real.sqrt_lt_sqrt h0 hp'lt1
        _ = 1 := Real.sqrt_one
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h0)]; exact zero_lt_one
  refine ⟨Real.sqrt p', hq0lt1, fun q hq0 hq1 ⟨hindep, hmarg⟩ A hA hincA => ?_⟩
  have hpmap : Measurable (fun η (e : Site d × Fin d) =>
      decide (GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2))) := by
    refine measurable_pi_lambda _ fun e => measurable_to_bool ?_
    have heq : (fun η : Site d → ℤ => decide (GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2)))
        ⁻¹' ({true} : Set Bool)
        = {η : Site d → ℤ | GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2)} := by
      ext η; simp
    rw [heq]; exact aux_renorm_edge_measurable k e
  haveI : IsProbabilityMeasure (toyLaw d p) := by
    haveI := aux_renorm_iid_field_chiplaw_prob (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p
      (by linarith) (by linarith)
    unfold toyLaw productLaw; infer_instance
  haveI : IsProbabilityMeasure ((toyLaw d p).map (fun η (e : Site d × Fin d) =>
      decide (GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2)))) :=
    Measure.isProbabilityMeasure_map hpmap.aemeasurable
  have hmarg' : ∀ e : Site d × Fin d, ENNReal.ofReal p' ≤
      ((toyLaw d p).map (fun η (e : Site d × Fin d) =>
        decide (GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2)))) {ω | ω e = true} := by
    intro e
    have hms : MeasurableSet {ω : Site d × Fin d → Bool | ω e = true} :=
      measurableSet_eq_fun (measurable_pi_apply e) measurable_const
    rw [Measure.map_apply hpmap hms]
    have hset : (fun η (e : Site d × Fin d) =>
        decide (GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2))) ⁻¹' {ω | ω e = true}
        = {η : Site d → ℤ | GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2)} := by
      ext η; simp
    rw [hset, aux_renorm_edge_marginal p q k hindep hmarg e,
      ← ENNReal.ofReal_mul (le_trans (Real.sqrt_nonneg p') hq0.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hqnn : (0 : ℝ) ≤ q := le_trans (Real.sqrt_nonneg p') hq0.le
    have hsq := (Real.sqrt_le_left hqnn).mp hq0.le
    nlinarith [hsq]
  have := hdom ((toyLaw d p).map (fun η (e : Site d × Fin d) =>
      decide (GoodAt η k e.1 ∧ GoodAt η k (e.1 + unit e.2))))
    inferInstance (aux_renorm_edge_dependence_graph p hp hp1 k) hmarg' A hA hincA
  rwa [Measure.map_apply hpmap hA] at this

/-! ### Step 2: the construction of `C_∞`. -/

/-- [NEEDS FURTHER SPLIT] Route B, Step 2(a): the coupling. Given the good-edge field's
domination of Bernoulli bond percolation of density close to `1` (`aux_renorm_edge_domination`),
there is a probability space carrying both a background `η` with law `toyLaw d p` and an
independent-looking Bernoulli bond percolation `ζ` of that density such that, almost surely,
every `ζ`-open edge is a good edge. Needs a Strassen-type stochastic-domination-to-coupling
theorem: checked `LatticeProb/Prob/Harris.lean`, `HarrisCube.lean`, `TwoPointOrder.lean`,
`Prob/Percolation/FiniteProductPivotal.lean` — none of them constructs a coupling from a
domination-via-increasing-events hypothesis, only compares probabilities of individual
increasing events (which is what `aux_renorm_edge_domination` itself already gives). -/
theorem aux_renorm_route_b_coupling (d : ℕ) (hd : 2 ≤ d) (p ρ : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (k : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ (η : Ω → Site d → ℤ) (ζ : Ω → Site d × Fin d → Bool),
        Measurable η ∧ Measurable ζ ∧ P.map η = toyLaw d p ∧ P.map ζ = bondPercolation d ρ ∧
        ∀ᵐ ω ∂P, ∀ e : Site d × Fin d, ζ ω e = true →
          GoodAt (η ω) k e.1 ∧ GoodAt (η ω) k (e.1 + unit e.2) := by
  sorry

/-- [NEEDS FURTHER SPLIT] Route B, Step 2(b): given the coupling of
`aux_renorm_route_b_coupling` with `ρ` supercritical for bond percolation (`bondCritical d < ρ`,
so that the `ζ`-open cluster of the origin is infinite with positive probability, and a.s.
infinite on the event that it is nonempty, by 0-1 law/ergodicity — not itself included here),
`Cinf`, the set of macroscopic sites in the `ζ`-open cluster of the origin (when infinite), is an
infinite connected set of good cubes: infinite and connected by construction of the open cluster,
and every one of its sites is good since every `ζ`-edge inside the cluster is a good edge by the
coupling, in particular every one of a site's `2d` incident `ζ`-edges being open (which happens
on the cluster) forces that site's own two neighbouring cubes to be good, hence (applied to all
`2d` neighbours) the site itself. Needs `bondTheta d ρ > 0` for `ρ` close to `1` (supercriticality
of the coupled `ζ`, not proved anywhere in `Exploding` or found in `Lattice-Probability`) plus
the cluster-to-`IsInfiniteConnectedGoodSet` translation itself. -/
theorem aux_renorm_route_b_cluster (d : ℕ) (hd : 2 ≤ d) (p ρ : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hρ : bondCritical d < ρ) (hρ1 : ρ < 1) (k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ η ∂(toyLaw d p),
      ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k Cinf ∧
        (∀ x : Site d, x ∈ Cinf ↔
          ∃ ζη : Site d × Fin d → Bool, True) := by
  sorry

/-- [NEEDS FURTHER SPLIT] Route B, Step 2(c): the hole bound. Given `Cinf` an infinite connected
good set that is (a.s., for `ρ` above `hHole`'s threshold `q₀`) exactly the site-percolation open
cluster of an independent Bernoulli site field of density `ρ` restricted to `Cinf`'s own index
set, `hHole` applied to that cluster bounds the `ℓ^∞`-local volume of the holes of `Cinf` by
`(log n)^{5/2}` for `n` large. This is the direct application of `Exploding.External.MathieuHoleVolume`
once `Cinf` is identified with such a cluster (`aux_renorm_route_b_cluster`); recorded separately
because that identification itself needs the (still open) precise relationship between `Cinf` and
an ambient site percolation, not just the coupling to bond percolation `ζ`. -/
theorem aux_renorm_route_b_holes (d : ℕ) (hd : 2 ≤ d)
    (hHole : Exploding.External.MathieuHoleVolume) (ρ : ℝ) (hρ1 : ρ < 1) (k : ℕ)
    (ζsite : Site d → ℤ → Bool) (Cinf : Set (Site d))
    (hcluster : ∀ᵐ ω ∂(sitePercolation d ρ), IsInfiniteOpenCluster ω Cinf) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2) := by
  sorry

/-- [NEEDS FURTHER SPLIT] Route B, Step 2(d): the chemical-distance upper bound. Given `Cinf`
identified (as in `aux_renorm_route_b_holes`) with an ambient bond-percolation open cluster of
density `ρ > bondCritical d`, `hChem` gives, for every `y`, an exponential tail bound on the event
that the chemical distance from `0` to `y` exceeds `ρ' |y|`; summing this bound over the (at most
polynomially many, in `n`) pairs `x, y` with `|x| ≤ n` and `|x - y| ≥ (log n)^2`, translating by
`x` (translation-invariance of bond percolation, not recorded anywhere in `Exploding.Support` or
`Lattice-Probability` either), and applying Borel–Cantelli gives the stated `C |x-y|` bound for
`n` large, a.s. Needs (i) translation invariance of `bondPercolation`/`chemDist`, (ii) the
union-bound-over-`n`-and-pairs step, and (iii) the Borel–Cantelli application itself, each a
further split beyond what is attempted here. -/
theorem aux_renorm_route_b_chem_upper (d : ℕ) (hd : 2 ≤ d)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) (ρ : ℝ) (hρ : bondCritical d < ρ)
    (hρ1 : ρ ≤ 1) (k : ℕ) (Cinf : Set (Site d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂(bondPercolation d ρ), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x ∈ Cinf, ∀ y ∈ Cinf, mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
        ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ) := by
  sorry

/-- The trivial Manhattan-distance lower bound (`c = 1`): every nearest-neighbour path has
length at least the Manhattan distance between its ends, since each step changes each coordinate
by at most `1`. Elementary, but needs an induction on `SimpleGraph.Walk` using
`Exploding.lattice`'s adjacency (`∃ i, y = x + unit i ∨ x = y + unit i`, from
`LatticeProb.lattice`) to bound `mnorm`'s change per step, which is not present in
`Exploding.Support`; recorded here as the one genuinely small remaining piece of Step 2(e). -/
theorem aux_renorm_route_b_chem_lower (Cinf : Set (Site d)) (x y : Site d) (m : ℕ)
    (hxy : chemDist Cinf x y = (m : ℕ∞)) : (mnorm (x - y) : ℝ) ≤ (m : ℝ) := by
  sorry

/-- [NEEDS FURTHER SPLIT] Route B, Step 2, assembled with the domination threshold `q0` pulled
out ahead of `k` (unlike `aux_renorm_route_b`'s own statement, where it is produced after `k` is
fixed): `q0` only depends on `d`/`hLSSB`/`hHole`/`hChem` (through `renormEdgeGraph`'s
`k`-independent degree bound `4d - 2` and a `ρ` fixed once from `hHole`/`hChem`'s own
thresholds), never on `k`, but making that manifest needs `aux_renorm_edge_domination` to be
called with one fixed `ρ` rather than re-derived per `k`, and needs
`aux_renorm_route_b_coupling`/`_cluster`/`_holes`/`_chem_upper`/`_chem_lower` assembled together.
This uniform version is what `aux_renorm_assemble` below actually needs; deriving
`aux_renorm_route_b` itself from it is immediate (see its proof). -/
theorem aux_renorm_route_b_uniform (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ q0 : ℝ, q0 < 1 ∧ ∀ k : ℕ, ∀ q : ℝ, q0 < q → q ≤ 1 →
      (ProbabilityTheory.iIndepSet (fun i : Site d => {η : Site d → ℤ | GoodAt η k i})
          (toyLaw d p) ∧ ∀ i : Site d, toyLaw d p {η | GoodAt η k i} = ENNReal.ofReal q) →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ η ∂(toyLaw d p),
        ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k Cinf ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
            (componentIn Cinfᶜ x).Finite ∧
              ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
            mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
              ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ)) := by
  sorry

open scoped Classical in
/-- Step 2 (the construction before Proposition 2.2).  Couple the good-edge field of Step 1
with an independent bond percolation process `ζ` of density close to `1` lying below it.  The
cubes all of whose `ζ`-edges are open form a site process in which cubes that are not
neighbours are independent; by `hLSSB` again it dominates Bernoulli site percolation of
density close to `1`, which has an infinite cluster.  `Cinf` is the open cluster of `ζ`
containing it: an infinite connected set of good cubes.  Its holes lie inside the holes of
that site cluster, which `hHole` bounds; its chemical distance is at most the `ζ`-chemical
distance, which `hChem`, translation invariance, a union bound over `|x| ≤ n`,
`|x - y| ≥ (log n)^2` and the Borel-Cantelli lemma bound by `C |x - y|`; the lower bound holds
with `c = 1`, since a path inside `Cinf` is at least as long as the Manhattan distance. -/
theorem aux_renorm_route_b (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (k : ℕ) (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ q0 : ℝ, q0 < 1 ∧ ∀ q : ℝ, q0 < q → q ≤ 1 →
      (ProbabilityTheory.iIndepSet (fun i : Site d => {η : Site d → ℤ | GoodAt η k i})
          (toyLaw d p) ∧ ∀ i : Site d, toyLaw d p {η | GoodAt η k i} = ENNReal.ofReal q) →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ η ∂(toyLaw d p),
        ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k Cinf ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)),
            x ∉ Cinf →
              (componentIn Cinfᶜ x).Finite ∧
                ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
            mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
              ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ)) := by
  obtain ⟨q0, hq0lt1, huniform⟩ := aux_renorm_route_b_uniform d hd p hp hp1 hLSSB hHole hChem
  exact ⟨q0, hq0lt1, fun q hq0 hq1 h => huniform k q hq0 hq1 h⟩

/-! ### Step 3: assembly. -/

/-- [NEEDS FURTHER SPLIT] The quantitative content of `Exploding.Frozen.crossing_time`'s proof
(`k^{d-1} exp(-2ε²k) → 0`, see `prop-crossing-time-dec/node.lean`'s `aux_ct_all_directions`
[sealed], `aux_ct_propagate` [still `sorry`] and `aux_ct_assemble` [still `sorry`]) makes the
good-cube probability at scale `k` tend to `1` as `k → ∞`, in the precise sense that it
eventually exceeds any target `q0 < 1`. Neither `aux_ct_propagate` nor `aux_ct_assemble` is
proved yet, and `Exploding.Frozen.crossing_time`'s own proof in `Exploding/Frozen/CrossingTime.lean`
is `:= by sorry` (only the EXISTENCE of one good `k` per `δ` is exposed there, not the tail decay
needed here for "eventually, for all `k` at once"), so no sealed, importable lemma currently
gives this; it genuinely needs `aux_ct_propagate` (deterministic bootstrap propagation) filled in
first, which is outside this node's namespace (`prop-crossing-time-dec`, a different node's
design file). -/
theorem aux_renorm_assemble_tail (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (q0 : ℝ) (hq0 : q0 < 1) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ENNReal.ofReal q0 ≤ toyLaw d p {η : Site d → ℤ | GoodCube η k} := by
  sorry

/-- Step 3 (assembly).  The target needs the conclusion for every sufficiently large `k`,
while `Exploding.Frozen.crossing_time` gives one `k` per `δ`.  Its proof gives more: the
failure probability is at most `k^{d-1} exp(-2 ε² k)`, which tends to `0`, so the probability
of a good cube is eventually above any `q0 < 1`.  That eventual bound is to be derived here
from the proof of Proposition 2.1 (see `prop-crossing-time`'s decomposition), and then
Steps 0 and 2 give the conclusion for each `k ≥ k0`. -/
theorem aux_renorm_assemble (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p),
        ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k Cinf ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)),
            x ∉ Cinf →
              (componentIn Cinfᶜ x).Finite ∧
                ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
            mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
              ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ)) := by
  obtain ⟨q0, hq0lt1, huniform⟩ := aux_renorm_route_b_uniform d hd p hp hp1 hLSSB hHole hChem
  set q0' : ℝ := (1 + q0) / 2 with hq0'def
  have hq0' : q0' < 1 := by rw [hq0'def]; linarith
  obtain ⟨k0, htail⟩ := aux_renorm_assemble_tail d hd p hp hp1 q0' hq0'
  refine ⟨max k0 1, fun k hk => ?_⟩
  have hk0 : k0 ≤ k := le_trans (le_max_left _ _) hk
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hδ : (0:ℝ) < 1 - q0' := by rw [hq0'def]; linarith
  have hcross : ENNReal.ofReal (1 - (1 - q0')) ≤ toyLaw d p {η : Site d → ℤ | GoodCube η k} := by
    simpa using htail k hk0
  obtain ⟨q, hq1, hq2, hindep, hmarg⟩ :=
    aux_renorm_iid_field d hd p hp hp1 k hk1 (1 - q0') hδ hcross
  have hq0lt : q0 < q := by rw [hq0'def] at hq1; linarith
  exact huniform k q hq0lt hq2 ⟨hindep, hmarg⟩

end Exploding.Frozen.RenormalizationDec

open Exploding LatticeProb MeasureTheory
