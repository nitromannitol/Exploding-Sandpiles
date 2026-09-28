/-
The support lemmas of Lemma 3.2 of `paper/exploding.tex`: the last wave is well
defined.  The paper's argument: the `n`-wave for large `n` covers a centred box
(`square_lower_bound`), that box meets the infinite cluster of good cubes
(Proposition 2.2), and once the wave's support covers a good cube it never
stabilizes.

The one step still open is `aux_finite_exploding_step`: covering a good cube
`Q_k(i)` propagates to an adjacent good cube `Q_k(j)`.  The paper's mechanism is
the crossing property of a good cube: a line of `Q_k(j)` that is already fired
fills `Q_k(j)` within `k^d` steps, and the wave dominates that frozen process
(`aux_finite_exploding_wave_dominates_fodo`).  What remains is the geometric
bookkeeping that produces a fired line of `Q_k(j)` from the coverage of
`Q_k(i)`.
-/
import Exploding.Support.Vocab
import Exploding.Support.Wave
import Exploding.Support.SubGeom
import Exploding.Frozen.SquareLowerBound
import Exploding.Frozen.Renormalization
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory


/-- `aux_finite_exploding_bounds`: `toyLaw`-almost every background lies
pointwise in `[2d-2, 2d-1]`.  This is real (not a literature gap) but
genuinely measure-theoretic work: `toyLaw d p` is the countable product
`Measure.infinitePi (fun _ => chipLaw (2d-1) (2d-2) p)`, each one-site marginal
gives full mass to `{2d-2, 2d-1}` by construction of `chipLaw`, and the
intersection over the countably many sites of these full-measure events is
still full measure.  (A structurally identical lemma was attempted, but not
finished, by the fleet in `scratch/leanstral/work/lem-penultimate-cluster/node.lean`
under the name `toyLaw_eta_bounds`; the same lemma is needed here, for
`lem-penultimate-cluster`, and anywhere else that needs a.e. bounds on `η`.
Since it is used by several nodes it may be worth adding to `Support/Vocab.lean`
directly rather than re-deriving per node.) -/
theorem aux_finite_exploding_bounds (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
  have hpos_p : (0 : ℝ) ≤ p := by linarith
  have hle_p : (0 : ℝ) ≤ 1 - p := by linarith
  haveI hprob : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) := by
    constructor
    simp only [chipLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply',
      MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hpos_p hle_p]
    norm_num
  haveI hprob' : ∀ _ : Site d, IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
    fun _ => hprob
  have h_each (x : Site d) : ∀ᵐ η ∂(toyLaw d p), 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
    have h_marginal_eq : (toyLaw d p).map (fun η : Site d → ℤ => η x) =
        chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p := by
      rw [toyLaw, productLaw, Measure.infinitePi_map_eval]
    have h_ae_chip : ∀ᵐ v ∂(chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p),
        v = 2 * (d : ℤ) - 2 ∨ v = 2 * (d : ℤ) - 1 := by
      have h_support : chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p
          {v : ℤ | ¬ (v = 2 * (d : ℤ) - 2 ∨ v = 2 * (d : ℤ) - 1)} = 0 := by
        simp [chipLaw]
      rw [MeasureTheory.ae_iff]
      exact h_support
    have h_ae_coord : ∀ᵐ η ∂(toyLaw d p), η x = 2 * (d : ℤ) - 2 ∨ η x = 2 * (d : ℤ) - 1 := by
      have h_meas : MeasurableSet {v : ℤ | v = 2 * (d : ℤ) - 2 ∨ v = 2 * (d : ℤ) - 1} :=
        (measurableSet_singleton _).union (measurableSet_singleton _)
      have h_aemeas : AEMeasurable (fun (η : Site d → ℤ) => η x) (toyLaw d p) :=
        (measurable_pi_apply x).aemeasurable
      rw [← MeasureTheory.ae_map_iff h_aemeas h_meas, h_marginal_eq]
      exact h_ae_chip
    filter_upwards [h_ae_coord] with η h
    rcases h with h_eq | h_eq
    · rw [h_eq]; exact ⟨by omega, by omega⟩
    · rw [h_eq]; exact ⟨by omega, by omega⟩
  exact (MeasureTheory.ae_all_iff).mpr h_each

/- `aux_finite_exploding_covers`: on the a.s. event, firing the origin enough
times makes the wave's support entirely cover some macroscopic good cube that
lies in the infinite cluster `C_∞` of Proposition 2.2.

This packages several geometric steps that the paper's one-sentence proof
("if the origin is fired a sufficient number of times, the support of the
odometer contains a good cube `Q_k ⊂ C_∞`") leaves implicit, and which are
themselves nontrivial:
(i) fix `k ≥ k0` from `renormalization_properties` to get the a.s. infinite
    connected set `Cinf` of good macroscopic cubes, with clause (2)
    bounding the cardinality of finite complementary components;
(ii) a macroscopic ball of radius `m` about the origin cannot be entirely
    covered by (finitely many, boundedly sized) components of `Cinfᶜ` once
    `m` is large, since those components have cardinality `< (log m)^{5/2} ≪
    m^d`; hence some macroscopic site `i` with `|i| ≤ m` lies in `Cinf`;
(iii) apply `Exploding.Frozen.square_lower_bound` (real project file, fully
    PROVEN, no gap: `Exploding/Frozen/SquareLowerBound.lean`) with `n` large
    enough that `cent d n` contains the microscopic cube `Q_k(i) = Q_k + k•i`
    entirely, so the resulting wave's support covers `Q_k(i)`.
Step (ii) is split out below as `aux_finite_exploding_meets_cluster`; the
The theorem itself, needing both (ii) and `square_lower_bound`, is placed after it
(a forward reference from here would not compile).

-- FIDELITY NOTE: an earlier draft of this decomposition stated the conclusion
-- with `GoodAt η k i` alone (no cluster membership).  That is not enough for
-- `aux_finite_exploding_propagate` to be true: a single good cube surrounded
-- entirely by bad ones is stable on its own, and never causes an explosion.
-- The paper's proof needs `Q_k(i) ⊂ C_∞`, i.e. `i` in the *infinite* cluster,
-- which is what lets propagation continue forever; that membership is
-- restored below (`Cinf`, `IsInfiniteConnectedGoodSet η k Cinf`, `i ∈ Cinf`). -/

/- `aux_finite_exploding_meets_cluster`: step (ii) of `aux_finite_exploding_covers`,
made a standalone deterministic fact.  A sufficiently large centred box always
meets a cluster `Cinf` whose complementary components obey the cardinality
bound of `renormalization_properties` clause (2).

If `cent d m` were disjoint from `Cinf`, it would lie entirely in `Cinfᶜ`; the
sup-norm box `cent d m` is connected under the nearest-neighbour adjacency of
`lattice d` (any two of its points are joined by a path that adjusts one
coordinate at a time towards the target, never leaving the box), so it would
then lie inside a single connected component of `Cinfᶜ`, namely
`componentIn Cinfᶜ x` for any `x ∈ cent d m`.  That component would then have
cardinality at least `|cent d m| = (2m+1)^d`, contradicting `hcomp` once `m` is
large enough that `(2m+1)^d` exceeds `(log m)^{5/2}`.

-- Provable in principle from the stated hypotheses (no literature gap): it
-- needs two combinatorial facts not yet in `Support/` — that `cent d m` is
-- connected under `lattice d`, and that a connected subset of `S` containing
-- `x` lies inside `componentIn S x` — plus the elementary count
-- `Set.ncard (cent d m) = (2 * m + 1) ^ d`. None of these needs anything
-- outside the definitions already in `Support/Vocab.lean`. Split below. -/

/-- `cent d m` equals a `Fintype.piFinset` of integer intervals, so it is
finite with exactly `(2m+1)^d` points: `abs_le` identifies `cent d m` with
`↑(Fintype.piFinset fun _ : Fin d => Finset.Icc (-(m:ℤ)) m)`
(`Fintype.coe_piFinset`), whose card is `Fintype.card_piFinset_const` composed
with `Int.card_Icc : #(Icc a b) = (b+1-a).toNat`. -/
theorem aux_finite_exploding_cent_card (d m : ℕ) :
    (cent d m : Set (Site d)).Finite ∧ (cent d m : Set (Site d)).ncard = (2 * m + 1) ^ d := by
  have h_fin : (cent d m : Set (Site d)).Finite := by
    have h_each (i : Fin d) : {x : ℤ | |x| ≤ (m : ℤ)}.Finite := by
      have h_eq : {x : ℤ | |x| ≤ (m : ℤ)} = (Finset.Icc (-(m : ℤ)) (m : ℤ) : Set ℤ) := by
        ext x; simp [abs_le]
      rw [h_eq]
      exact Finset.finite_toSet _
    have h_eq : (cent d m : Set (Site d)) =
        Set.pi Set.univ (fun (_ : Fin d) => {x : ℤ | |x| ≤ (m : ℤ)}) := by
      ext f; simp [cent, Set.mem_pi, Set.mem_setOf_eq]
    rw [h_eq]
    exact Set.Finite.pi h_each
  have h_card : (cent d m : Set (Site d)).ncard = (2 * m + 1) ^ d := by
    have h_finset_eq : (cent d m : Set (Site d)) =
        (Fintype.piFinset (fun (_ : Fin d) => Finset.Icc (-(m : ℤ)) (m : ℤ)) : Set (Site d)) := by
      ext f
      simp [cent, abs_le, Pi.le_def, forall_and]
    have h_card_Icc : (Finset.Icc (-(m : ℤ)) (m : ℤ)).card = 2 * m + 1 := by
      rw [Int.card_Icc]
      have h : (m : ℤ) + 1 - (-(m : ℤ)) = 2 * (m : ℤ) + 1 := by ring
      rw [h]
      have hpos : 0 ≤ 2 * (m : ℤ) + 1 := by omega
      apply (Nat.cast_inj (R := ℤ)).mp
      simpa using Int.toNat_of_nonneg hpos
    rw [h_finset_eq]
    rw [Set.ncard_coe_finset]
    rw [Fintype.card_piFinset_const]
    rw [h_card_Icc]
  exact And.intro h_fin h_card

/-- `cent d m` is connected under the lattice graph of any `S ⊇ cent d m`: two
points of `cent d m` are joined, staying inside `cent d m` throughout, by a
path that fixes coordinates one at a time to match the target (change
coordinate `0` from `x 0` to `y 0` one unit at a time, then coordinate `1`,
…): every intermediate point still has every coordinate between the two
sup-norm bounds `m`, hence sup-norm `≤ m`. Induction on `d` (or on
`Finset.univ : Finset (Fin d)`) building the walk explicitly, then
`SimpleGraph.Walk.reachable` and `hsub` to land the walk inside `S`. -/
theorem aux_finite_exploding_box_connected {d : ℕ} (S : Set (Site d)) (m : ℕ)
    (hsub : (cent d m : Set (Site d)) ⊆ S) (x y : Site d)
    (hx : x ∈ (cent d m : Set (Site d))) (hy : y ∈ (cent d m : Set (Site d))) :
    y ∈ componentIn S x :=
  cent_connected_in S m hsub x y hx hy

theorem aux_finite_exploding_meets_cluster (d : ℕ) (Cinf : Set (Site d)) (m : ℕ)
    (hcomp : ∀ x ∈ (cent d m : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log m ^ ((5 : ℝ) / 2))
    (hbig : Real.log m ^ ((5 : ℝ) / 2) ≤ ((2 * m + 1 : ℕ) ^ d : ℝ)) :
    ∃ i ∈ (cent d m : Set (Site d)), i ∈ Cinf := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hsub : (cent d m : Set (Site d)) ⊆ Cinfᶜ := hcon
  have h0 : (0 : Site d) ∈ (cent d m : Set (Site d)) := fun i => by
    simp only [Pi.zero_apply, abs_zero]
    exact_mod_cast Nat.zero_le m
  obtain ⟨hfin, hcard⟩ := hcomp 0 h0 (hsub h0)
  have hconn : (cent d m : Set (Site d)) ⊆ componentIn Cinfᶜ (0 : Site d) :=
    fun x hx => aux_finite_exploding_box_connected Cinfᶜ m hsub 0 x h0 hx
  have hcc := aux_finite_exploding_cent_card d m
  have hle : (cent d m : Set (Site d)).ncard ≤ (componentIn Cinfᶜ (0 : Site d)).ncard :=
    Set.ncard_le_ncard hconn hfin
  rw [hcc.2] at hle
  have hleR : ((2 * m + 1 : ℕ) ^ d : ℝ) ≤ (componentIn Cinfᶜ (0 : Site d)).ncard := by
    exact_mod_cast hle
  linarith [hbig, hcard, hleR]

/-! ### `aux_finite_exploding_covers` itself -/

/-- Polynomial beats polylog: for `d ≥ 1`, `Real.log m ^ (5/2) ≤ (2m+1)^d`
once `m` is large enough.  `Real.log` is `o(m^{1/(2d)})` as `m → ∞`
(`Real.isLittleO_log_rpow_atTop`-style growth facts, or directly bounding
`Real.log m ≤ m` for `m ≥ 1` (`Real.log_le_sub_one_of_pos`) and comparing the
resulting polynomial powers), so eventually `Real.log m ^ (5/2) ≤ m^{5/2} ≤
(2m+1)^d` once `d ≥ 3` (`5/2 < d`); a direct `atTop` comparison covers `d = 2`
too. -/
theorem aux_finite_exploding_growth (d : ℕ) (hd : 2 ≤ d) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → Real.log m ^ ((5 : ℝ) / 2) ≤ ((2 * m + 1 : ℕ) ^ d : ℝ) := by
  have hlog : Filter.Tendsto (fun m : ℕ => Real.log m ^ ((5 : ℝ) / 2) / (m : ℝ) ^ ((d : ℝ) / 2))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℕ => Real.log m / (m : ℝ) ^ ((d : ℝ) / (5 : ℝ)))
        Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun x : ℝ => Real.log x / x ^ ((d : ℝ) / (5 : ℝ)))
          Filter.atTop (nhds 0) := by
        have hpos : (0 : ℝ) < (d : ℝ) / (5 : ℝ) := by
          have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
          positivity
        have h3 := (isLittleO_log_rpow_atTop hpos).tendsto_div_nhds_zero
        simpa [div_eq_mul_inv, mul_comm] using h3
      exact h2.comp tendsto_natCast_atTop_atTop
    have h4 : Filter.Tendsto (fun m : ℕ => (Real.log m / (m : ℝ) ^ ((d : ℝ) / (5 : ℝ))) ^
        ((5 : ℝ) / 2)) Filter.atTop (nhds 0) := by
      have := h1.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ (5 : ℝ) / 2))
      simpa using this
    refine h4.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with m hm
    rw [Real.div_rpow (Real.log_nonneg (by exact_mod_cast hm)) (by positivity)]
    congr 1
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (m : ℝ))]
    ring_nf
  have hbound : ∀ᶠ m : ℕ in Filter.atTop,
      Real.log m ^ ((5 : ℝ) / 2) ≤ ((2 * m + 1 : ℕ) ^ d : ℝ) := by
    have h5 : ∀ᶠ m : ℕ in Filter.atTop,
        Real.log m ^ ((5 : ℝ) / 2) / (m : ℝ) ^ ((d : ℝ) / 2) < 1 :=
      (tendsto_order.1 hlog).2 1 zero_lt_one
    filter_upwards [h5, Filter.eventually_gt_atTop 0] with m hm hmpos
    have h6 : Real.log m ^ ((5 : ℝ) / 2) ≤ (m : ℝ) ^ ((d : ℝ) / 2) := by
      have h7 : (0 : ℝ) < (m : ℝ) ^ ((d : ℝ) / 2) := by positivity
      rw [div_lt_one h7] at hm
      exact le_of_lt hm
    have h8 : (m : ℝ) ^ ((d : ℝ) / 2) ≤ ((2 * m + 1 : ℕ) ^ d : ℝ) := by
      have h9 : (m : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
        have : (m : ℕ) ≤ 2 * m + 1 := by omega
        exact_mod_cast this
      have h10 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
      have h11 : (m : ℝ) ^ ((d : ℝ) / 2) ≤ (m : ℝ) ^ (d : ℕ) := by
        have h12 : ((d : ℕ) : ℝ) = (d : ℝ) := by norm_num
        have h13 : (m : ℝ) ^ ((d : ℝ) / 2) ≤ (m : ℝ) ^ ((d : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h10 (by rw [h12]; linarith)
        rw [Real.rpow_natCast] at h13
        exact h13
      calc (m : ℝ) ^ ((d : ℝ) / 2) ≤ (m : ℝ) ^ (d : ℕ) := h11
        _ ≤ (((2 * m + 1 : ℕ) : ℝ)) ^ d := pow_le_pow_left₀ (by positivity) h9 d
        _ = ((2 * m + 1 : ℕ) ^ d : ℝ) := by push_cast; ring
    linarith
  obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.1 hbound
  exact ⟨m0, hm0⟩

/-- `cube d k` is finite: the same `Fintype.piFinset`-coercion argument as
`aux_finite_exploding_cent_card`, now for `Finset.Icc 1 (k:ℤ)`. -/
theorem aux_finite_exploding_cube_finite (d k : ℕ) : (cube d k : Set (Site d)).Finite := by
  have h_eq : (cube d k : Set (Site d)) =
      (Fintype.piFinset (fun (_ : Fin d) => Finset.Icc (1 : ℤ) (k : ℤ)) : Set (Site d)) := by
    ext x; simp only [cube, Set.mem_setOf_eq, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc, forall_and]
  rw [h_eq]
  exact Finset.finite_toSet _

/-- Finitely many per-point time witnesses to a monotone-in-time wave
property combine into one shared time: choose a witness `t x` for each
`x ∈ S` (`Classical.choice`/`hex`), take the max over `S.toFinset`
(`Set.Finite.toFinset`, `Finset.sup'` or `Finset.exists_le`), and propagate
every individual witness up to that shared bound by `wave_mono_time`
(`Support/Wave.lean`). -/
theorem aux_finite_exploding_uniform_time {d : ℕ} (w : Site d → ℤ) (hw : ∀ y, 0 ≤ w y)
    (hd0 : (0 : ℤ) < 2 * (d : ℤ)) (M : ℕ) (z : Site d) (S : Set (Site d)) (hS : S.Finite)
    (f : Site d → Site d) (hex : ∀ x ∈ S, ∃ t : ℕ, 0 < wave w M z t (f x)) :
    ∃ t : ℕ, ∀ x ∈ S, 0 < wave w M z t (f x) := by
  by_cases hSempty : S.Nonempty
  · -- S is nonempty; pick witnesses, take max, propagate via wave_mono_time
    let fs := hS.toFinset
    have hfs_nonempty : fs.Nonempty := by
      rcases hSempty with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simpa [fs, hS.mem_toFinset] using hx
    have h_choice (x : Site d) (hx : x ∈ fs) : ∃ t : ℕ, 0 < wave w M z t (f x) := by
      apply hex x
      simpa [fs, hS.mem_toFinset] using hx
    let t_fn : Site d → ℕ := fun x =>
      if h : x ∈ fs then Classical.choose (h_choice x h) else 0
    have h_t_fn (x : Site d) (hx : x ∈ fs) : 0 < wave w M z (t_fn x) (f x) := by
      dsimp [t_fn]
      rw [dif_pos hx]
      exact Classical.choose_spec (h_choice x hx)
    let T := fs.sup' hfs_nonempty t_fn
    have hT_le (x : Site d) (hx : x ∈ fs) : t_fn x ≤ T :=
      Finset.le_sup' t_fn hx
    refine ⟨T, ?_⟩
    intro x hx
    have hx_fs : x ∈ fs := by
      simpa [fs, hS.mem_toFinset] using hx
    have hle : t_fn x ≤ T := hT_le x hx_fs
    have hpos : 0 < wave w M z (t_fn x) (f x) := h_t_fn x hx_fs
    have hmono := wave_mono_time w hw hd0 M z hle (f x)
    linarith
  · -- S is empty; conclusion holds vacuously
    have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSempty
    refine ⟨0, ?_⟩
    intro x hx
    rw [hS_empty] at hx
    simp at hx

/-- **`aux_finite_exploding_covers`**, assembled from steps (i)-(iii) above.
`renormalization_properties` gives `k0`, `Cinf`, and the hole bound; `k0`
itself (rather than some larger `k ≥ k0`) is used directly, since the
statement only needs *some* good scale. `aux_finite_exploding_growth` supplies
`m` large enough to invoke `aux_finite_exploding_meets_cluster` and get a
macroscopic site `i ∈ Cinf`.  `square_lower_bound` always covers a box
`cent d n` centred at the origin, matching the goal's centre exactly (no
translation needed): `n1 := k0 * (m + 2) + 1` is chosen generously so that
`cube d k0 + k0 • i ⊆ cent d n1` (`|x j + k0 * i j| ≤ k0 + k0 * m ≤ n1` using
`x ∈ cube d k0` and `i ∈ cent d m`), and `n1 ≥ 1` unconditionally (even if
`k0 = 0`, in which case `cube d k0 = ∅` and the covering goal is vacuous
anyway). `aux_finite_exploding_uniform_time` turns `square_lower_bound`'s
per-`x` time witness (over the finite set `cube d k0`,
`aux_finite_exploding_cube_finite`) into the single shared time the goal
asks for.

FIDELITY NOTE: the design's original conclusion asserted only `1 ≤ N` (not
`1 ≤ k`); `renormalization_properties`'s own `k0` could in principle be `0`
(its statement is `∃ k0, ∀ k ≥ k0, …`, so nothing stops `k0 = 0`), and a
`k = 0` cube gives `aux_finite_exploding_propagate` (below, whose FIDELITY
NOTE has the matching counterexample) nothing to work with. Not a falsity in
`aux_finite_exploding_covers` itself, but a strengthening: the scale actually
picked is `max k0 1` rather than `k0`, valid for the same reason
(`renormalization_properties` holds for every `k ≥ k0`), and the added
conjunct `1 ≤ k` is threaded through so `propagate` has what it needs. -/
theorem aux_finite_exploding_covers (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree) (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ N t k : ℕ, 1 ≤ N ∧ 1 ≤ k ∧ ∃ (Cinf : Set (Site d)) (i : Site d),
      IsInfiniteConnectedGoodSet η k Cinf ∧ i ∈ Cinf ∧
        ∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t (x + (k : ℤ) • i) := by
  obtain ⟨kb, hkb⟩ := Exploding.Frozen.renormalization_properties d hd p hp hp1 hLSSB hHole hChem
  set k0 : ℕ := max kb 1 with hk0def
  obtain ⟨c, Cr, hc, hCr, hae⟩ := hkb k0 (le_max_left kb 1)
  obtain ⟨m0, hm0⟩ := aux_finite_exploding_growth d hd
  filter_upwards [hae, aux_finite_exploding_bounds d p hp hp1] with η hη hηbd
  obtain ⟨Cinf, hCinf, ⟨n0, hn0⟩, -⟩ := hη
  set m := max n0 m0 with hmdef
  obtain ⟨i, hicent, hiCinf⟩ := aux_finite_exploding_meets_cluster d Cinf m
    (fun x hx hnotin => hn0 m (le_max_left _ _) x hx hnotin) (hm0 m (le_max_right _ _))
  set n1 : ℕ := k0 * (m + 2) + 1 with hn1def
  set N : ℕ := (2 * d) ^ (d * n1) with hNdef
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hηnn : ∀ y : Site d, 0 ≤ η y := fun y => by linarith [(hηbd y).1]
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hxcent : ∀ x ∈ cube d k0, x + (k0 : ℤ) • i ∈ (cent d n1 : Set (Site d)) := by
    intro x hx j
    have h1 := hx j
    have h2 := hicent j
    simp only [Pi.add_apply]
    have hxj : |x j| ≤ (k0 : ℤ) := by
      rw [abs_of_pos (by linarith [h1.1] : (0 : ℤ) < x j)]; linarith [h1.2]
    have hprod : |(k0 : ℤ) * i j| ≤ (k0 : ℤ) * (m : ℤ) := by
      rw [abs_mul, abs_of_nonneg (by exact_mod_cast Nat.zero_le k0 : (0 : ℤ) ≤ (k0 : ℤ))]
      exact mul_le_mul_of_nonneg_left h2 (by exact_mod_cast Nat.zero_le k0)
    calc |x j + (k0 : ℤ) * i j| ≤ |x j| + |(k0 : ℤ) * i j| := abs_add_le _ _
      _ ≤ (k0 : ℤ) + (k0 : ℤ) * (m : ℤ) := by linarith
      _ ≤ (n1 : ℤ) := by rw [hn1def]; push_cast; nlinarith [Nat.zero_le k0, Nat.zero_le m]
  have hpt : ∀ x ∈ cube d k0, ∃ t : ℕ, 0 < wave η N (0 : Site d) t (x + (k0 : ℤ) • i) :=
    fun x hx => Exploding.Frozen.square_lower_bound d hd η hηnn n1 (by omega) N (le_refl N)
      (x + (k0 : ℤ) • i) (hxcent x hx)
  obtain ⟨t, ht⟩ := aux_finite_exploding_uniform_time η hηnn hd0
    N (0 : Site d) (cube d k0) (aux_finite_exploding_cube_finite d k0)
    (fun x => x + (k0 : ℤ) • i) hpt
  exact ⟨N, t, k0, Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by positivity)),
    le_max_right kb 1, Cinf, i, hCinf, hiCinf, ht⟩

/-! ### Two elementary facts used by the propagation step -/

theorem aux_finite_exploding_mnorm_add_le {d : ℕ} (a b : Site d) :
    mnorm (a + b) ≤ mnorm a + mnorm b := by
  simp only [mnorm, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le _ _

theorem aux_finite_exploding_mnorm_neg {d : ℕ} (a : Site d) : mnorm (-a) = mnorm a := by
  simp only [mnorm, Pi.neg_apply, abs_neg]

theorem aux_finite_exploding_mnorm_unit {d : ℕ} (i : Fin d) : mnorm (unit i : Site d) = 1 := by
  simp only [mnorm, unit]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- `aux_finite_exploding_speed`: the `n`-wave has finite propagation speed one
lattice step per unit time: `wave η N z t x` can only be positive once `t` has
reached the (Manhattan) distance from `x` to `z`.  This is the standard finite
speed of propagation of a nearest-neighbour update rule, proved here by
induction on `t`: away from `z`, `wave η N z (t+1) x` reads only the values of
`wave η N z t` at the `2d` neighbours of `x`, each at distance `≥ mnorm(x-z)-1`
from `z`; once `mnorm(x-z) > t+1` those neighbours are all still `0` by the
induction hypothesis, so the neighbour sum is `0`, and
`⌊η(x)/2d⌋ = 0` since `0 ≤ η(x) ≤ 2d-1`.  Fully proved: no gap. -/
theorem aux_finite_exploding_speed {d : ℕ} (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N : ℕ) (z : Site d) :
    ∀ t : ℕ, ∀ x : Site d, (t : ℤ) < mnorm (x - z) → wave η N z t x = 0 := by
  intro t
  induction t with
  | zero =>
    intro x hx
    have hxz : x ≠ z := by
      intro h; subst h; simp [mnorm] at hx
    simp [wave_zero, hxz]
  | succ t ih =>
    intro x hx
    have hxz : x ≠ z := by
      intro h; subst h; simp [mnorm] at hx; omega
    rw [wave_of_ne η N z x t hxz]
    have hnbr : nbrSumZ (wave η N z t) x = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hb1 : mnorm (x - z) ≤ mnorm ((x + unit i) - z) + mnorm (unit i : Site d) := by
        have heq : (x - z) = ((x + unit i) - z) + (-(unit i)) := by abel
        calc mnorm (x - z) = mnorm (((x + unit i) - z) + (-(unit i))) := by rw [← heq]
          _ ≤ mnorm ((x + unit i) - z) + mnorm (-(unit i) : Site d) :=
                aux_finite_exploding_mnorm_add_le _ _
          _ = mnorm ((x + unit i) - z) + mnorm (unit i : Site d) := by
                rw [aux_finite_exploding_mnorm_neg]
      have hb2 : mnorm (x - z) ≤ mnorm ((x - unit i) - z) + mnorm (unit i : Site d) := by
        have heq : (x - z) = ((x - unit i) - z) + (unit i) := by abel
        calc mnorm (x - z) = mnorm (((x - unit i) - z) + (unit i)) := by rw [← heq]
          _ ≤ mnorm ((x - unit i) - z) + mnorm (unit i : Site d) :=
                aux_finite_exploding_mnorm_add_le _ _
      rw [aux_finite_exploding_mnorm_unit] at hb1 hb2
      have h1 : wave η N z t (x + unit i) = 0 := ih (x + unit i) (by omega)
      have h2 : wave η N z t (x - unit i) = 0 := ih (x - unit i) (by omega)
      rw [h1, h2]; ring
    rw [hnbr, zero_add]
    exact Int.ediv_eq_zero_of_lt (hlow x) (by linarith [hhigh x])

/-- **General wave-dominates-`S`-frozen-odometer comparison, time-shifted from
`t0`.** Generalizes `aux_square_lower_bound_compare`
(`lem-square-lower-bound-dec/node.lean`, PROVEN there for `S = ∅`, `t0 = 0`) to
an arbitrary frozen set `S` and a process started at `t0` rather than `0`
(needed since `S`'s seed is typically only known dominated by the wave from
*some* later time on, not from `t0 = 0`). Same induction on `s` as that
lemma's proof: at `x ∈ S`, `fodo S η w0 (s+1) x = w0 x ≤ wave η N z (t0+s+1)
x` directly from `hSdom` (quantified over every `s`, so it covers `s+1` too,
including the case `s=0` via `hw0`); off `S`, compare via `nbrSumZ_mono` on
the induction hypothesis and `Int.ediv_le_ediv`, exactly as in the cited
lemma's own proof — `fodo` and `podo` share the identical "increment by
`1{config ≥ 2d}`" recursion (`fodo_succ`/`podo_succ`), so the same
"floor dominates the capped increment" algebra applies with `wave η N z
(t0+s+1)`'s direct floor formula (`wave_of_ne`) in place of `podo`'s target.
Addresses the "genuine multi-node foundational gap" flagged in
`lem-square-lower-bound-dec/node.lean`'s `aux_square_lower_bound_compare`;
restated here (not there, since only this node's `-dec/` file may be edited),
and usable by any future node that needs it. -/
theorem aux_finite_exploding_wave_dominates_fodo {d : ℕ} (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (S : Set (Site d)) (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y) (N : ℕ) (z : Site d)
    (hz : z ∈ S)
    (t0 : ℕ) (w0 : Site d → ℤ) (hw0nn : ∀ x, 0 ≤ w0 x)
    (hw0 : ∀ x, w0 x ≤ wave η N z t0 x)
    (hSdom : ∀ s : ℕ, ∀ x ∈ S, w0 x ≤ wave η N z (t0 + s) x) :
    ∀ s x, fodo S η w0 s x ≤ wave η N z (t0 + s) x :=
  wave_dom_fodo hd0 S η hη N z t0 w0 hw0nn hz hw0 hSdom

/-- An infinite subset of `Site d` is not contained in any centred box: if it
were `⊆ cent d n`, it would be finite (`aux_finite_exploding_cent_card`,
`Set.Finite.subset`), contradicting `Set.Infinite`. -/
theorem aux_finite_exploding_infinite_meets_box {d : ℕ} (C : Set (Site d)) (hC : C.Infinite)
    (n : ℕ) : ∃ y ∈ C, (n : ℤ) < mnorm y := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  refine hC (Set.Finite.subset (aux_finite_exploding_cent_card d n).1 ?_)
  intro y hy i
  have hle : (∑ j, |y j|) ≤ (n : ℤ) := hcon y hy
  have hterm : |y i| ≤ ∑ j, |y j| :=
    Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  linarith


/-- Unwinding a walk of good macroscopic sites into a chain of propagation
steps: if `i` and `y` lie in the same component of `S ⊆ goodSites η k`
(`componentIn`/`Reachable`, unfolded via `Classical.choice` on the
`Nonempty (Walk …)` witness and structural induction — `SimpleGraph.Walk.rec`
or `SimpleGraph.Walk.ind` — on that walk, applying `aux_finite_exploding_step`
once per edge, i.e. once per `Walk.cons`, and `GoodAt` from `hS` at each
visited vertex) and `Q_k(i)` is covered by time `t`, then `Q_k(y)` is covered
by *some* finite time. -/
theorem aux_finite_exploding_walk_prop {d : ℕ} (η : Site d → ℤ) (_hlow : ∀ x, 0 ≤ η x)
    (_hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N k : ℕ) (S : Set (Site d)) (hS : S ⊆ goodSites η k)
    (hstep : ∀ (i j : Site d), GoodAt η k j → (lattice d).Adj i j → ∀ t : ℕ,
      (∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t (x + (k : ℤ) • i)) →
      ∃ t' : ℕ, t ≤ t' ∧ ∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t' (x + (k : ℤ) • j))
    (a b : S) (p0 : ((lattice d).induce S).Walk a b) :
    ∀ t : ℕ, (∀ z ∈ cube d k, 0 < wave η N (0 : Site d) t (z + (k : ℤ) • (a : Site d))) →
      ∃ t' : ℕ, ∀ z ∈ cube d k, 0 < wave η N (0 : Site d) t' (z + (k : ℤ) • (b : Site d)) := by
  refine p0.recOn ?_ ?_
  · intro u t ht
    exact ⟨t, ht⟩
  · intro u v w h p ih t ht
    have hvgood : GoodAt η k (v : Site d) := hS v.2
    have hadj : (lattice d).Adj (u : Site d) (v : Site d) := SimpleGraph.induce_adj.mp h
    obtain ⟨t', -, hcov'⟩ := hstep (u : Site d) (v : Site d) hvgood hadj t ht
    exact ih t' hcov'

theorem aux_finite_exploding_propagate_walk {d : ℕ} (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N k : ℕ) (S : Set (Site d)) (hS : S ⊆ goodSites η k)
    (hstep : ∀ (i j : Site d), GoodAt η k j → (lattice d).Adj i j → ∀ t : ℕ,
      (∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t (x + (k : ℤ) • i)) →
      ∃ t' : ℕ, t ≤ t' ∧ ∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t' (x + (k : ℤ) • j))
    (i y : Site d) (hreach : y ∈ componentIn S i) (t : ℕ)
    (hcover : ∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t (x + (k : ℤ) • i)) :
    ∃ t' : ℕ, ∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t' (x + (k : ℤ) • y) := by
  unfold componentIn at hreach
  obtain ⟨hiS, hyS, hreach'⟩ := hreach
  obtain ⟨p0⟩ := hreach'
  exact aux_finite_exploding_walk_prop η hlow hhigh N k S hS hstep ⟨i, hiS⟩ ⟨y, hyS⟩ p0 t hcover


/-- `aux_finite_exploding_propagate`: once the `N`-wave's support entirely
covers a good macroscopic cube `Q_k(i)` lying in the infinite cluster of good
cubes, the `N`-wave never stabilizes.

The correct contradiction (sharper than "growing support outruns propagation
speed", which is false: a wave covering distance `r` by macroscopic time
`~r·k^d` is well inside its own light cone, since `k ≥ 1`) is instead: suppose
`WaveStabilizable η N 0` held, witnessed by `T`.  `Cinf` is an *infinite*
subset of `ℤ^d`, so it is not contained in any bounded box
(`aux_finite_exploding_infinite_meets_box`), hence (choosing the box radius
past `T`, with enough room for a whole `Q_k`) contains a site `y` with
`mnorm y` large enough that every point of `Q_k(y)` is farther than `T` from
the origin.  Since `i, y ∈ Cinf` (`hCinf`'s third clause gives
`y ∈ componentIn (goodSites η k) i`), `aux_finite_exploding_propagate_walk`
covers `Q_k(y)` by some finite time `t_y`; by monotonicity of the wave in
time (`wave_mono_time`), `Q_k(y)` is then also covered at time
`max T t_y ≥ T`. But `aux_finite_exploding_speed` forces the wave to be `0`
at time `T` at every point of `Q_k(y)` (all farther than `T` from the
origin). Stabilization at `T` would force these two to agree, contradiction.

FIDELITY NOTE: the design's original statement had no lower bound on `k`.
That is FALSE at `k = 0`: `cube d 0 = ∅` makes `hcover` vacuous, so take
`η ≡ 0` (satisfies `hlow`/`hhigh`) and `Cinf := Set.univ \ {0, unit 0}` (as in
`aux_close_long_path`'s counterexample, `k = 0` makes `GoodCube` vacuous for
every `η`, so `hCinf` holds); the `N`-wave for the zero background carries
only its initial finite mass `N` and dissipates it via a strictly decreasing
"unstable-site" potential exactly as in a finite sandpile, so it stabilizes,
i.e. `WaveStabilizable η N 0` holds, contradicting the claimed conclusion.
Restored here as `hk : 1 ≤ k`, so `cube d k` is nonempty
(the all-`1`s point `fun _ => (1:ℤ)`, or any point of it, witnesses this in
the proof) and `hcover`/`aux_finite_exploding_speed` carry real content. -/
theorem aux_finite_exploding_propagate (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N t k : ℕ) (hk : 1 ≤ k)
    (hstep : ∀ (i j : Site d), GoodAt η k j → (lattice d).Adj i j → ∀ t : ℕ,
      (∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t (x + (k : ℤ) • i)) →
      ∃ t' : ℕ, t ≤ t' ∧ ∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t' (x + (k : ℤ) • j))
    (Cinf : Set (Site d)) (i : Site d) (hCinf : IsInfiniteConnectedGoodSet η k Cinf) (hi : i ∈ Cinf)
    (hcover : ∀ x ∈ cube d k, 0 < wave η N (0 : Site d) t (x + (k : ℤ) • i)) :
    ¬ WaveStabilizable η N (0 : Site d) := by
  rintro ⟨T, hT⟩
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  set x0 : Site d := fun _ : Fin d => (1 : ℤ) with hx0def
  have hx0 : x0 ∈ cube d k := fun l => ⟨le_refl 1, by
    show (1 : ℤ) ≤ (k : ℤ); exact_mod_cast hk⟩
  obtain ⟨y, hyCinf, hybig⟩ := aux_finite_exploding_infinite_meets_box Cinf hCinf.1 (T + d + 1)
  obtain ⟨t', ht'⟩ := aux_finite_exploding_propagate_walk η hlow hhigh N k Cinf hCinf.2.1 hstep
    i y (hCinf.2.2 i hi y hyCinf) t hcover
  have hfar : ∀ x ∈ cube d k, (T : ℤ) < mnorm (x + (k : ℤ) • y) := by
    intro x hx
    have heq : (-x) + (x + (k : ℤ) • y) = (k : ℤ) • y := by abel
    have h1 : mnorm ((k : ℤ) • y) - mnorm x ≤ mnorm (x + (k : ℤ) • y) := by
      have hle := aux_finite_exploding_mnorm_add_le (-x) (x + (k : ℤ) • y)
      rw [heq] at hle
      have h2 := aux_finite_exploding_mnorm_neg x
      linarith
    have hkY : mnorm ((k : ℤ) • y) = (k : ℤ) * mnorm y := by
      unfold mnorm
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg (show (0 : ℤ) ≤ (k : ℤ) by exact_mod_cast Nat.zero_le k)]
      rw [Finset.mul_sum]
    have hxbd : mnorm x ≤ (d : ℤ) * (k : ℤ) := by
      unfold mnorm
      calc ∑ l, |x l| ≤ ∑ _l : Fin d, (k : ℤ) := Finset.sum_le_sum fun l _ => by
            rw [abs_of_pos (by linarith [(hx l).1] : (0 : ℤ) < x l)]; exact (hx l).2
        _ = (d : ℤ) * (k : ℤ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    have hkpos : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    have hcast : (T : ℤ) + (d : ℤ) + 1 < mnorm y := by
      have hcast' : ((T + d + 1 : ℕ) : ℤ) < mnorm y := hybig
      push_cast at hcast'; linarith
    have hdlt : (d : ℤ) < mnorm y := by linarith
    have hstep : mnorm y - (d : ℤ) ≤ (k : ℤ) * (mnorm y - (d : ℤ)) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (k : ℤ) - 1)
        (by linarith : (0 : ℤ) ≤ mnorm y - (d : ℤ))]
    nlinarith [h1, hkY, hxbd, hstep, hcast]
  have heq := congrFun (hT (max T t') (le_max_left T t')) (x0 + (k : ℤ) • y)
  have hzero : wave η N 0 T (x0 + (k : ℤ) • y) = 0 := by
    apply aux_finite_exploding_speed η hlow hhigh N 0 T (x0 + (k : ℤ) • y)
    rw [sub_zero]
    exact hfar x0 hx0
  have hpos : 0 < wave η N 0 (max T t') (x0 + (k : ℤ) • y) := by
    have hmono := wave_mono_time η hlow hd0 N (0 : Site d) (le_max_right T t') (x0 + (k : ℤ) • y)
    linarith [ht' x0 hx0]
  rw [heq, hzero] at hpos
  exact lt_irrefl 0 hpos

