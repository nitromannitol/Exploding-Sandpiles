/-
Decomposition of Proposition 7.1 (`prop-explosion-criteria`,
`exploding.tex:1800-1804`, "If Hypotheses 5.1 and 5.2 are satisfied and `P` is
recurrent then `P` is explosive").

**The paper gives NO proof of this proposition.** I looked twice: the statement
at `exploding.tex:1800-1804` is followed immediately (line 1806) by "In this
section, we use Proposition 7.1 to prove Theorem 1.4" -- there is no
`\begin{proof}...\end{proof}` block, no reference to an earlier proof, nothing.
The only supporting prose anywhere in the paper is a single sentence given much
earlier, right after Hypothesis 5.2 is first stated (`exploding.tex:1156-1158`):
"If `η` were recurrent, Hypothesis 5.2 would imply `η` explodes with
probability 1. In particular, no holes would develop in the support of the
odometer." That sentence is the entire textual justification for this node.

I do NOT think this makes the statement false -- it is the kind of fact that is
"clearly true to the author" and the real content is genuinely the two
ingredients below -- but I want to flag explicitly that everything past that
one sentence is MY reconstruction of what the missing proof must say, not a
transcription of the paper's own argument, and I have only medium confidence it
is exactly the route Bou-Rabee had in mind (there may be a slicker one).

**My reconstruction has two independent parts, and I believe BOTH are needed**:

(A) A zero-one law. `ExplosiveLaw d P` asks for probability exactly `1`, but
Hypotheses 5.1/5.2 + recurrence only obviously give a *positive*-probability
event on which explosion is forced (see (B)). The bridge is: `Explosive η` (at
the fixed origin) does not depend on `η`'s values on any finite set -- changing
finitely many sites only requires finitely many extra chips at the origin to
compensate, by monotonicity of parallel toppling -- so `{η | Explosive η}` is a
tail event; combined with `FiniteRangeOfDependence` (h1) and the GIVEN
`ErgodicOn` hypothesis (herg), a tail event's probability is `0` or `1` (this
is the classical mixing argument that
`LatticeProb/Prob/ZeroOne.lean`'s abstract criterion is
built for, though that file's concrete instance derives ergodicity of a single
shift from an i.i.d. law, which is not quite our setting: here `ErgodicOn` is
already handed to us as a hypothesis about the WHOLE sublattice `L`, and the
missing bridge is "tail-measurable ⟹ a.e. equal to an `L`-invariant set", a
genuine measure-theoretic fact I did not find already packaged for this exact
combination of hypotheses).

(B) A positive-probability existence argument. Given (A), it suffices to show
`P(Explosive) > 0`. This is where "no holes develop" is doing its work: on a
positive-probability event, `FiniteRangeOfDependence` + `BoxCrossingHyp` make
the field of box-crossing macroscopic tiles a highly-supercritical dependent
0-1 field (same renormalization idea as `prop-renormalization`, but here we
only need EXISTENCE of an infinite chain of good tiles reachable from a
neighbourhood of the origin, not the sharp uniqueness/hole-volume/chemical-
distance estimates of that node), and `hrec : RecurrentLaw` guarantees that
once such a chain is entered, `Recurrent`'s definition (firing a domain's
boundary floods its interior) keeps propagating the firing outward along it
without ever stabilizing. This is again a percolation-existence citation (much
softer than Burton-Keane uniqueness, but still not present in this repo or
Mathlib): existence of an infinite cluster reaching the origin's neighbourhood
for supercritical dependent percolation with positive probability.
-/
import Exploding.Support.Hypotheses

open Exploding LatticeProb MeasureTheory

variable {d : ℕ}

/-! ### Monotonicity of `podo` in the initial sandpile

Not present in `Support/Toppling.lean` (only `wave_mono_n`/`wave_mono_t` exist,
for `wave`, not for `podo`).  Proved directly: at each site `x`, either the two
odometers already differ at time `t` (in which case the integer gap of `≥ 1`
absorbs whatever the two `≤ 1` indicators add at the next step), or they agree
at `x` at time `t`, in which case the `-2d·(value at x)` correction terms in
`lap` cancel and `nbrSumZ_mono` (using the FULL pointwise hypothesis at every
site, not just at `x`) finishes it. -/
theorem aux_criteria_podo_mono {s0 s0' : Site d → ℤ} (h : ∀ x, s0 x ≤ s0' x) (t : ℕ)
    (x : Site d) : podo s0 t x ≤ podo s0' t x := by
  induction t generalizing x with
  | zero => simp [podo]
  | succ t ih =>
    have h_podo : podo s0 t x ≤ podo s0' t x := ih x
    rw [podo_succ, podo_succ]
    split_ifs with h_fire h_fire'
    · omega
    · have h_lt : podo s0 t x < podo s0' t x := by
        by_contra h_not_lt
        have h_eq : podo s0 t x = podo s0' t x := le_antisymm h_podo (by omega)
        have h_nbr_le : nbrSumZ (podo s0 t) x ≤ nbrSumZ (podo s0' t) x :=
          nbrSumZ_mono (fun y => ih y) x
        simp only [pconf, lap, h_eq] at h_fire h_fire'
        have := h x
        omega
      omega
    · omega
    · omega

/-- **GAP** (needs new library infrastructure). This is the precise fact
`aux_criteria_finite_insensitive` needs: if `a = b` off the finite set `F`,
and `a + n·δ₀` is not stabilizable, then `b + m·δ₀` is not stabilizable for
SOME `m`. I believe this is TRUE (an instance of the classical sandpile fact
that an infinite avalanche started at one point is also seen, after enough
extra chips, from any other bounded-distance point) but its proof needs more
than `aux_criteria_podo_mono`'s pointwise domination alone: `a`, `b` are not
pointwise ordered here (they only agree off `F`, so a "dominates" comparison
first needs a compensating bump `K·1_F`, and that bump then needs to be
RELOCATED to the origin, via a reachability/simulation argument for which I
did not find, and could not derive, existing infrastructure -- especially
since `aux_criteria_finite_insensitive`'s own (unchangeable) signature carries
no boundedness hypothesis on `a`, `b` to rule out unrelated instabilities
elsewhere interfering with a uniform stabilization time.  Proof idea if a
boundedness hypothesis were available: finite propagation speed (by induction
on `t`, using `mnorm`'s triangle inequality) confines all activity to a ball
of radius `t` around `F ∪ {0}`, reducing the uniform-stabilization question to
a FINITE max over that ball. -/
theorem aux_criteria_finite_insensitive_step (a b : Site d → ℤ) (F : Finset (Site d))
    (heq : ∀ x, x ∉ (F : Set (Site d)) → a x = b x) (n : ℕ) (hn : 1 ≤ n)
    (ha : ¬ Stabilizable (fun x => a x + n * dirac (0 : Site d) x)) :
    ∃ m : ℕ, 1 ≤ m ∧ ¬ Stabilizable (fun x => b x + m * dirac (0 : Site d) x) := by
  sorry

/-- Changing a background on a finite set does not change whether it is
explosive: if `η₁ = η₂` off a finite set `F`, then `Explosive η₁ ↔ Explosive
η₂`.  Assembly from `aux_criteria_finite_insensitive_step`, applied in each
direction (the hypothesis `heq` is symmetric via `.symm`). -/
theorem aux_criteria_finite_insensitive (η₁ η₂ : Site d → ℤ) (F : Finset (Site d))
    (heq : ∀ x, x ∉ (F : Set (Site d)) → η₁ x = η₂ x) :
    Explosive η₁ ↔ Explosive η₂ := by
  have dir : ∀ a b : Site d → ℤ, (∀ x, x ∉ (F : Set (Site d)) → a x = b x) →
      Explosive a → Explosive b := by
    intro a b hab hE
    obtain ⟨n, hn, hns⟩ : ∃ n : ℕ, 1 ≤ n ∧
        ¬ Stabilizable (fun x => a x + n * dirac (0 : Site d) x) := by
      by_contra hc
      push Not at hc
      exact hE hc
    obtain ⟨m, hm, hms⟩ := aux_criteria_finite_insensitive_step a b F hab n hn hns
    exact fun hRob => hms (hRob m hm)
  exact ⟨dir η₁ η₂ heq, dir η₂ η₁ (fun x hx => (heq x hx).symm)⟩

/-- For each `t`, the function `(s0, x) ↦ podo s0 t x` is measurable: induction
on `t`, using that `lap`/`nbrSumZ` are finite sums of `Measurable.add`/`.sub`
combinations of the induction hypothesis composed with the coordinate
projections `measurable_pi_apply`, and `Measurable.ite` for the indicator. -/
theorem aux_criteria_measurable_podo (t : ℕ) :
    Measurable (fun (s0 : Site d → ℤ) (x : Site d) => podo s0 t x) := by
  induction t with
  | zero =>
    have : (fun (s0 : Site d → ℤ) (x : Site d) => podo s0 0 x) = fun _ _ => (0 : ℤ) := by
      ext s0 x; simp [podo]
    rw [this]; exact measurable_const
  | succ t ih =>
    have h_podo_at (y : Site d) : Measurable (fun (s0 : Site d → ℤ) => podo s0 t y) :=
      (measurable_pi_apply y).comp ih
    have h_lap_at (y : Site d) : Measurable (fun (s0 : Site d → ℤ) => lap (podo s0 t) y) := by
      dsimp [lap, nbrSumZ]
      have h_nbr : Measurable (fun (s0 : Site d → ℤ) => nbrSumZ (podo s0 t) y) :=
        Finset.measurable_sum _ (fun i _ =>
          Measurable.add (h_podo_at (y + unit i)) (h_podo_at (y - unit i)))
      exact Measurable.sub h_nbr (Measurable.mul measurable_const (h_podo_at y))
    refine measurable_pi_lambda _ (fun x => ?_)
    have h_succ_at_x : (fun (s0 : Site d → ℤ) => podo s0 (t + 1) x) = fun s0 =>
        podo s0 t x + (if (2 : ℤ) * (d : ℤ) ≤ s0 x + lap (podo s0 t) x then (1 : ℤ) else 0) := by
      ext s0; simp [podo_succ, pconf]
    rw [h_succ_at_x]
    have h_cond : MeasurableSet {s0 : Site d → ℤ | (2:ℤ)*(d:ℤ) ≤ s0 x + lap (podo s0 t) x} :=
      measurableSet_le measurable_const (Measurable.add (measurable_pi_apply x) (h_lap_at x))
    exact Measurable.add (h_podo_at x) (Measurable.ite h_cond measurable_const measurable_const)

/-- The function `η ↦ η + n·δ₀` is measurable. -/
theorem aux_criteria_measurable_add_dirac (n : ℕ) :
    Measurable (fun (η : Site d → ℤ) (x : Site d) => η x + n * dirac (0 : Site d) x) := by
  refine measurable_pi_lambda _ (fun x => ?_)
  exact Measurable.add (measurable_pi_apply x) measurable_const

/-- For each `n`, the set `{η | Stabilizable (η + n·δ₀)}` is measurable:
`Stabilizable` rewrites (using that `podo` is nondecreasing in `t`, so a
function-equality test at time `t` against time `T` for `t < T` is vacuous)
as a countable `⋃ T, ⋂ t, ...` of `MeasurableSet.iInter`/`.iUnion` combinations
of the coordinatewise equalities `podo (s0 η) t x = podo (s0 η) T x`, each
measurable via `aux_criteria_measurable_podo` composed with
`aux_criteria_measurable_add_dirac`. -/
theorem aux_criteria_measurable_stabilizable (n : ℕ) :
    MeasurableSet {η : Site d → ℤ | Stabilizable (fun x => η x + n * dirac (0 : Site d) x)} := by
  set s0 := fun (η : Site d → ℤ) (x : Site d) => η x + n * dirac (0 : Site d) x
  have h_s0_meas : Measurable s0 := aux_criteria_measurable_add_dirac n
  have h_podo_eq : ∀ T t : ℕ, MeasurableSet {η : Site d → ℤ | podo (s0 η) t = podo (s0 η) T} := by
    intro T t
    have h : {η : Site d → ℤ | podo (s0 η) t = podo (s0 η) T} =
        ⋂ x : Site d, {η : Site d → ℤ | podo (s0 η) t x = podo (s0 η) T x} := by
      ext η; simp [funext_iff]
    rw [h]
    refine MeasurableSet.iInter (fun x => ?_)
    have h_diff : Measurable (fun η : Site d → ℤ => podo (s0 η) t x - podo (s0 η) T x) :=
      Measurable.sub ((measurable_pi_apply x).comp (aux_criteria_measurable_podo t) |>.comp h_s0_meas)
        ((measurable_pi_apply x).comp (aux_criteria_measurable_podo T) |>.comp h_s0_meas)
    have h_eq : {η : Site d → ℤ | podo (s0 η) t x = podo (s0 η) T x} =
        {η | podo (s0 η) t x - podo (s0 η) T x = 0} := by ext η; simp [sub_eq_zero]
    rw [h_eq]; exact measurableSet_eq_fun h_diff measurable_const
  have h_iff : {η : Site d → ℤ | Stabilizable (s0 η)} =
      ⋃ T : ℕ, ⋂ t : ℕ, {η : Site d → ℤ | t < T ∨ podo (s0 η) t = podo (s0 η) T} := by
    ext η
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq, Stabilizable]
    constructor
    · rintro ⟨T, hT⟩; exact ⟨T, fun t => (lt_or_ge t T).imp id (fun h => hT t h)⟩
    · rintro ⟨T, hT⟩
      refine ⟨T, fun t ht => (hT t).resolve_left (by omega)⟩
  rw [h_iff]
  refine MeasurableSet.iUnion (fun T => MeasurableSet.iInter (fun t => ?_))
  have h_set : {η : Site d → ℤ | t < T ∨ podo (s0 η) t = podo (s0 η) T} =
      {η | t < T} ∪ {η | podo (s0 η) t = podo (s0 η) T} := by ext η; simp
  rw [h_set]
  refine MeasurableSet.union ?_ (h_podo_eq T t)
  by_cases hlt : t < T
  · simp [hlt]
  · simp [hlt]

/-- `Robust η` is a measurable predicate: a countable intersection (over `n`,
with `1 ≤ n`) of `aux_criteria_measurable_stabilizable`. -/
theorem aux_criteria_measurable_robust : MeasurableSet {η : Site d → ℤ | Robust η} := by
  have h_iff : {η : Site d → ℤ | Robust η} = ⋂ n : ℕ, ⋂ _ : 1 ≤ n,
      {η : Site d → ℤ | Stabilizable (fun x => η x + n * dirac (0 : Site d) x)} := by
    ext η; simp [Robust]
  rw [h_iff]
  exact MeasurableSet.iInter (fun n => MeasurableSet.iInter
    (fun _ => aux_criteria_measurable_stabilizable n))

/-- `Explosive` is a countable combination of pointwise-cylinder conditions on
`Site d → ℤ` (via `Robust`'s measurability, `aux_criteria_measurable_robust`),
so `{η | Explosive η}` is measurable. -/
theorem aux_criteria_measurable : MeasurableSet {η : Site d → ℤ | Explosive η} := by
  have h : {η : Site d → ℤ | Explosive η} = {η : Site d → ℤ | Robust η}ᶜ := by
    ext η; simp [Explosive]
  rw [h]; exact aux_criteria_measurable_robust.compl

/-- The shift `T_w η := fun z => η (w + z)` is a bijection, with inverse `T_{-w}`
(`add_neg_cancel_left`/`neg_add_cancel_left` via `abel`). -/
theorem aux_criteria_shift_bij (w : Site d) :
    Function.Bijective (fun η : Site d → ℤ => fun z => η (w + z)) := by
  refine ⟨fun η η' h => ?_, fun ρ => ⟨fun z => ρ (-w + z), ?_⟩⟩
  · funext z
    have h2 := congrFun h (-w + z)
    simpa [← add_assoc] using h2
  · funext z
    show ρ (-w + (w + z)) = ρ z
    rw [show -w + (w + z) = z from by abel]

/-- `T_w '' (T_y '' S) = T_{y+w} '' S`: composing the two shifts and using
`add_assoc`. -/
theorem aux_criteria_shift_image_image (y w : Site d) (S : Set (Site d → ℤ)) :
    (fun η : Site d → ℤ => fun z => η (w + z)) ''
        ((fun η : Site d → ℤ => fun z => η (y + z)) '' S)
      = (fun η : Site d → ℤ => fun z => η ((y + w) + z)) '' S := by
  rw [Set.image_image]
  congr 1
  funext η z
  show η (y + (w + z)) = η (y + w + z)
  rw [add_assoc]

/-- Reindexing `⋂ y ∈ L, T_{y+w} '' S` by `y ↦ y + w` (a bijection of `L` onto
itself, since `L` is a subgroup and `w ∈ L`) leaves the intersection over
`L` unchanged. -/
theorem aux_criteria_biInter_shift (L : AddSubgroup (Site d)) (w : Site d) (hw : w ∈ L)
    (S : Set (Site d → ℤ)) :
    (⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η ((y + w) + z)) '' S)
      = ⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (y + z)) '' S := by
  ext ρ
  simp only [Set.mem_iInter]
  constructor
  · intro h y hy
    have h2 := h (y - w) (L.sub_mem hy hw)
    simpa [sub_add_cancel] using h2
  · intro h y hy
    exact h (y + w) (L.add_mem hy hw)

/-- The set `E' := ⋂ y ∈ L, T_y '' {Explosive}` (with `T_y η := fun z => η (y +
z)` the shift `ErgodicOn` uses) is EXACTLY `L`-invariant in the sense
`ErgodicOn` needs: `E' = ⋂ w ∈ L, T_w '' E'`.  Proof: each `T_w` (`w ∈ L`) is a
BIJECTION (`aux_criteria_shift_bij`), so image commutes with the intersection
(`Set.image_iInter₂`); `T_w '' (T_y '' S) = T_{y+w} '' S`
(`aux_criteria_shift_image_image`); and reindexing the intersection over `y ∈
L` by `y + w` leaves it unchanged (`aux_criteria_biInter_shift`), so `T_w ''
E' = E'` for every `w ∈ L`, hence `E' = ⋂ w ∈ L, T_w '' E'`
(`Set.biInter_const`).  This is a purely group-theoretic fact about the SHIFT
ACTION, needing no properties of `Explosive` at all (stated here for a
generic set `S`). -/
theorem aux_criteria_zero_one_invariant (L : AddSubgroup (Site d)) (S : Set (Site d → ℤ)) :
    (⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (y + z)) '' S)
      = ⋂ w ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (w + z)) ''
          (⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (y + z)) '' S) := by
  have hfix : ∀ w ∈ (L : Set (Site d)),
      (fun η : Site d → ℤ => fun z => η (w + z)) ''
        (⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (y + z)) '' S)
        = ⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (y + z)) '' S := by
    intro w hw
    rw [Set.image_iInter₂ (aux_criteria_shift_bij w)]
    have hcongr : ∀ y ∈ (L : Set (Site d)),
        (fun η : Site d → ℤ => fun z => η (w + z)) '' ((fun η : Site d → ℤ => fun z => η (y + z)) '' S)
          = (fun η : Site d → ℤ => fun z => η ((y + w) + z)) '' S :=
      fun y _ => aux_criteria_shift_image_image y w S
    rw [Set.iInter₂_congr hcongr]
    exact aux_criteria_biInter_shift L w hw S
  have hne : (L : Set (Site d)).Nonempty := ⟨(0 : Site d), L.zero_mem⟩
  rw [Set.iInter₂_congr hfix, Set.biInter_const hne]

/-- **GAP** (needs new library infrastructure). `E' ⊆ {η | Explosive η}` is
immediate (specialize the intersection defining `E'` to `y = 0 ∈ L`), so it
remains to bound the OTHER inclusion up to a null set:
`P ({η | Explosive η} \ E') = 0`.  Since `{Explosive} \ E' = ⋃_{y ∈ L}
({Explosive} \ T_y '' {Explosive})` (a COUNTABLE union, as `L ⊆ Site d` is
countable) it would suffice to show `P ({Explosive} \ T_y '' {Explosive}) = 0`
for each fixed `y ∈ L`, i.e. that being explosive when chips are added at the
origin agrees, `P`-almost surely, with being explosive when they are added at
`y` instead.  I could not derive this from `h1 : FiniteRangeOfDependence`
alone (finite-range dependence does not by itself relate the marginal laws at
two DIFFERENT fixed points; the natural extra ingredient, `StationaryOn d L
P`, is available at this node's `Exploding.Frozen.explosion_criteria` call
site but is NOT a hypothesis of `aux_criteria_zero_one` itself, whose
signature is not mine to change). I flag this as the genuine remaining gap of
part (A) of this node's proof sketch. -/
theorem aux_criteria_zero_one_ae (L : AddSubgroup (Site d)) (P : Measure (Site d → ℤ))
    (hP : IsProbabilityMeasure P) (h1 : FiniteRangeOfDependence d P) (herg : ErgodicOn d L P) :
    P ({η | Explosive η} \
        ⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (y + z)) '' {η | Explosive η}) = 0 := by
  sorry

/-- **Part (A)**: `{η | Explosive η}` has probability `0` or `1`. Assembly:
`aux_criteria_zero_one_invariant` lets `herg` apply directly to `E'`, giving
the dichotomy for `P E'`; `E' ⊆ {Explosive}` (via `Set.biInter_subset_of_mem`
at `y = 0`) transfers the `= 1` case up by `measure_mono` and `P ≤ 1`; the `=
0` case transfers via `aux_criteria_zero_one_ae` and subadditivity
(`measure_union_le` on `{Explosive} = E' ∪ ({Explosive} \ E')`). -/
theorem aux_criteria_zero_one (L : AddSubgroup (Site d)) (P : Measure (Site d → ℤ))
    (hP : IsProbabilityMeasure P) (h1 : FiniteRangeOfDependence d P)
    (herg : ErgodicOn d L P) :
    P {η | Explosive η} = 0 ∨ P {η | Explosive η} = 1 := by
  set E' : Set (Site d → ℤ) :=
    ⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (y + z)) '' {η | Explosive η}
    with hE'def
  have hsub : E' ⊆ {η | Explosive η} := by
    have h0 := Set.biInter_subset_of_mem (t := fun y : Site d =>
      (fun η : Site d → ℤ => fun z => η (y + z)) '' {η | Explosive η}) L.zero_mem
    simpa [hE'def] using h0
  rcases herg E' (aux_criteria_zero_one_invariant L {η | Explosive η}) with h0 | hone
  · left
    have hnull := aux_criteria_zero_one_ae L P hP h1 herg
    have hle := measure_union_le (μ := P) E' ({η | Explosive η} \ E')
    rw [Set.union_sdiff_cancel hsub, h0, hnull] at hle
    simpa using hle
  · right
    have hle := measure_mono (μ := P) hsub
    rw [hone] at hle
    have hone' : P {η | Explosive η} ≤ 1 := hP.measure_univ ▸ measure_mono (Set.subset_univ _)
    exact le_antisymm hone' hle

/-- **GAP** (existence, with positive probability, of an infinite chain of
box-crossing macroscopic tiles reaching a neighbourhood of the origin, for a
highly-supercritical `K`-dependent 0-1 field: a softer, existence-only
relative of the uniqueness/hole-volume/chemical-distance percolation GAPs of
`prop-renormalization`, still not present in this repo or Mathlib).  "Reaching
a neighbourhood of the origin" is formalized as the chain containing the
macroscopic origin tile `0` itself.  Proof idea (matching this node's own
prose sketch, part (B)): `h1`+`h2` make the macroscopic field `i ↦ GoodAt η k
i` a `K`-dependent `0`-`1` field whose one-site probabilities `→ 1` as `k →
∞`; `Exploding.External.LiggettSchonmannStacey` dominates it from below by
i.i.d. Bernoulli site percolation of density `ρ → 1`; standard supercritical
i.i.d. percolation on `ℤ^d` has an infinite cluster through the origin's
neighbourhood with positive probability (a base percolation fact I could not
find already formalized in this repo or in Mathlib), and domination by
increasing events transports that positive probability back to the dependent
field. -/
theorem aux_criteria_positive_prob_chain (hd : 2 ≤ d) (P : Measure (Site d → ℤ))
    (hP : IsProbabilityMeasure P) (h1 : FiniteRangeOfDependence d P) (h2 : BoxCrossingHyp d P) :
    0 < P {η : Site d → ℤ | ∃ (k : ℕ) (C : Set (Site d)), (0 : Site d) ∈ C ∧
      IsInfiniteConnectedGoodSet η k C} := by
  sorry

/-- **GAP** (the "no holes develop" content of this node's part (B), real
mathematical content and not a citation). Given an infinite chain `C` of good
(box-crossing) macroscopic tiles reaching the macroscopic origin, and `η`
Recurrent, the firing started by adding enough chips at the origin never
stabilizes: `GoodAt η k 0` bounds the time for a boundary-fired origin tile to
cross itself, `Recurrent η` (via `RecurrentOn` on the growing sequence of
domains traced out by `C`) guarantees each newly-reached tile's boundary gets
flooded in turn once its neighbour in `C` has been crossed, and connectivity
of `C` (any two tiles joined by a nearest-neighbour path inside `C`) lets this
induction step out along the chain forever, so no finite time-`T` bound on the
odometer as in `Stabilizable` can hold. I was not able to turn this sketch
into a formal induction on `C` in the time available; see
`Exploding/Support/SubRec*.lean`/`SubFodo*.lean` for the existing
one-step recurrence-propagation lemmas (`recOdo_topple`,
`SubFodoTopple.fodo_topple_of_ge`) this induction would need to iterate. -/
theorem aux_criteria_positive_prob_flood (η : Site d → ℤ) (hRec : Recurrent η)
    (hchain : ∃ (k : ℕ) (C : Set (Site d)), (0 : Site d) ∈ C ∧ IsInfiniteConnectedGoodSet η k C) :
    Explosive η := by
  sorry

set_option linter.unusedVariables false in
/-- **Part (B)**: `P {η | Explosive η} > 0`. Assembly: `aux_criteria_positive_prob_chain`
gives positive probability to the chain event `S`; `hrec` (a.e. `Recurrent`)
has null complement, so `S ∩ {Recurrent}` still has positive probability
(`measure_union_le` on `S = (S ∩ Recurrent) ∪ (S ∩ Recurrentᶜ)`, the second
piece null since it is contained in `{Recurrent}ᶜ`); `aux_criteria_positive_prob_flood`
sends that set into `{Explosive}`, and `measure_mono` finishes it. -/
theorem aux_criteria_positive_prob (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (h1 : FiniteRangeOfDependence d P) (h2 : BoxCrossingHyp d P)
    (hrec : RecurrentLaw d P) :
    0 < P {η | Explosive η} := by
  have hSpos := aux_criteria_positive_prob_chain hd P hP h1 h2
  set S : Set (Site d → ℤ) := {η : Site d → ℤ | ∃ (k : ℕ) (C : Set (Site d)),
    (0 : Site d) ∈ C ∧ IsInfiniteConnectedGoodSet η k C} with hSdef
  have hsub : S ∩ {η | Recurrent η} ⊆ {η | Explosive η} := by
    rintro η ⟨hchain, hR⟩
    exact aux_criteria_positive_prob_flood η hR hchain
  have hcompl0 : P {η | Recurrent η}ᶜ = 0 := ae_iff.mp hrec
  have hEqS : S ∩ {η | Recurrent η} ∪ S ∩ {η | Recurrent η}ᶜ = S :=
    Set.inter_union_compl S {η | Recurrent η}
  have hdiff0 : P (S ∩ {η | Recurrent η}ᶜ) = 0 :=
    le_antisymm (le_trans (measure_mono Set.inter_subset_right) (le_of_eq hcompl0)) (by positivity)
  have hSle : P S ≤ P (S ∩ {η | Recurrent η}) + P (S ∩ {η | Recurrent η}ᶜ) := by
    calc P S = P (S ∩ {η | Recurrent η} ∪ S ∩ {η | Recurrent η}ᶜ) := by rw [hEqS]
      _ ≤ P (S ∩ {η | Recurrent η}) + P (S ∩ {η | Recurrent η}ᶜ) := measure_union_le _ _
  rw [hdiff0, add_zero] at hSle
  exact lt_of_lt_of_le hSpos hSle |>.trans_le (measure_mono hsub)

-- `hL` and `hstat` are part of the frozen, byte-identical signature but are
-- not needed by the reconstructed proof route below (only `herg` is used for
-- the zero-one law); silenced rather than dropped, since the statement may
-- not be edited.
