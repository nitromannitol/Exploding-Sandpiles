/-
Events of site percolation behind Proposition 2.2: measurability of the events "there is an infinite
open cluster" and "there is an infinite open cluster whose holes are small", their monotonicity, and
the almost sure existence of the infinite cluster at high density, given the positivity of the
percolation probability of bond percolation at some density below one.
-/
import Exploding.Support.Percolation
import Exploding.Support.RNProofGraph
import Exploding.Support.RNProofStrassen
import LatticeProb.Prob.Translation
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open MeasureTheory ProbabilityTheory Exploding LatticeProb

namespace Exploding

/-- Reachability in `n` steps along a relation, prepending steps. -/
def rn_reachN {V : Type*} (R : V → V → Prop) : ℕ → V → V → Prop
  | 0 => fun u v => u = v
  | n + 1 => fun u v => ∃ z, R u z ∧ rn_reachN R n z v

theorem rn_measurableSet_reachN {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    (R : Ω → V → V → Prop) (hR : ∀ u v, MeasurableSet {ω | R ω u v}) (n : ℕ) :
    ∀ u v : V, MeasurableSet {ω | rn_reachN (R ω) n u v} := by
  induction n with
  | zero =>
    intro u v
    by_cases h : u = v
    · simp only [rn_reachN, h]; exact MeasurableSet.univ
    · simp only [rn_reachN, h]; exact MeasurableSet.empty
  | succ n ih =>
    intro u v
    have : {ω | rn_reachN (R ω) (n + 1) u v} = ⋃ z, ({ω | R ω u z} ∩ {ω | rn_reachN (R ω) n z v}) := by
      ext ω; simp [rn_reachN]
    rw [this]
    exact MeasurableSet.iUnion fun z => (hR u z).inter (ih z v)

theorem rn_mem_componentIn_iff {d : ℕ} (S : Set (Site d)) (x y : Site d) :
    y ∈ componentIn S x ↔
      x ∈ S ∧ ∃ n, rn_reachN (fun u v => (lattice d).Adj u v ∧ v ∈ S) n x y := by
  constructor
  · rintro ⟨hx, hy, hr⟩
    refine ⟨hx, ?_⟩
    obtain ⟨p⟩ := hr
    have key : ∀ (u v : S) (p : ((lattice d).induce S).Walk u v),
        rn_reachN (fun u v => (lattice d).Adj u v ∧ v ∈ S) p.length u.1 v.1 := by
      intro u v p
      induction p with
      | nil => exact rfl
      | cons h p ih => exact ⟨_, ⟨h, Subtype.property _⟩, ih⟩
    exact ⟨p.length, key _ _ p⟩
  · rintro ⟨hx, n, hn⟩
    have key : ∀ (n : ℕ) (x : Site d), x ∈ S →
        rn_reachN (fun u v => (lattice d).Adj u v ∧ v ∈ S) n x y → y ∈ componentIn S x := by
      intro n
      induction n with
      | zero =>
        intro x hx h
        have : x = y := h
        subst this
        exact ⟨hx, hx, SimpleGraph.Reachable.refl _⟩
      | succ n ih =>
        intro x hx h
        obtain ⟨z, ⟨hadj, hz⟩, hzy⟩ := h
        obtain ⟨_, hy, hr⟩ := ih z hz hzy
        exact ⟨hx, hy, (SimpleGraph.Adj.reachable (G := (lattice d).induce S)
          (u := ⟨x, hx⟩) (v := ⟨z, hz⟩) hadj).trans hr⟩
    exact key n x hx hn

theorem rn_measurableSet_mem_componentIn {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (S : Ω → Set (Site d)) (hS : ∀ z, MeasurableSet {ω | z ∈ S ω}) (x y : Site d) :
    MeasurableSet {ω | y ∈ componentIn (S ω) x} := by
  have : {ω | y ∈ componentIn (S ω) x} =
      {ω | x ∈ S ω} ∩ ⋃ n, {ω | rn_reachN (fun u v => (lattice d).Adj u v ∧ v ∈ S ω) n x y} := by
    ext ω; simp [rn_mem_componentIn_iff]
  rw [this]
  refine (hS x).inter (MeasurableSet.iUnion fun n => ?_)
  refine rn_measurableSet_reachN (fun ω u v => (lattice d).Adj u v ∧ v ∈ S ω) (fun u v => ?_) n x y
  by_cases h : (lattice d).Adj u v
  · simp only [h, true_and]; exact hS v
  · simp only [h, false_and]; exact MeasurableSet.empty

theorem rn_finite_ncard_le_iff {V : Type*} (A : Set V) (m : ℕ) :
    (A.Finite ∧ A.ncard ≤ m) ↔ ∀ F : Finset V, (↑F : Set V) ⊆ A → F.card ≤ m := by
  constructor
  · rintro ⟨hfin, hcard⟩ F hF
    calc F.card = (↑F : Set V).ncard := (Set.ncard_coe_finset F).symm
      _ ≤ A.ncard := Set.ncard_le_ncard hF hfin
      _ ≤ m := hcard
  · intro h
    have hfin : A.Finite := by
      by_contra hinf
      obtain ⟨t, htA, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (m + 1)
      have := h t htA
      omega
    refine ⟨hfin, ?_⟩
    have := h hfin.toFinset (by simp)
    rw [Set.ncard_eq_toFinset_card A hfin]
    exact this

theorem rn_measurableSet_finite_ncard_le {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    (A : Ω → Set V) (hA : ∀ v, MeasurableSet {ω | v ∈ A ω}) (m : ℕ) :
    MeasurableSet {ω | (A ω).Finite ∧ (A ω).ncard ≤ m} := by
  have : {ω | (A ω).Finite ∧ (A ω).ncard ≤ m} =
      ⋂ F : Finset V, {ω | (↑F : Set V) ⊆ A ω → F.card ≤ m} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact rn_finite_ncard_le_iff (A ω) m
  rw [this]
  refine MeasurableSet.iInter fun F => ?_
  by_cases hF : F.card ≤ m
  · simp only [hF, implies_true, Set.setOf_true]; exact MeasurableSet.univ
  · simp only [hF, imp_false]
    have : {ω | ¬ (↑F : Set V) ⊆ A ω} = (⋂ v ∈ F, {ω | v ∈ A ω})ᶜ := by
      ext ω; simp [Set.subset_def]
    rw [this]
    exact (Finset.measurableSet_biInter F fun v _ => hA v).compl

/-- The conclusion of Lemma 5.2 of Mathieu for the set `C`: the holes of `C` are small. -/
def RnHoleProp (d : ℕ) (C : Set (Site d)) : Prop :=
  ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ C →
    (componentIn Cᶜ x).Finite ∧ ((componentIn Cᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)

/-- The configurations having an infinite open cluster. -/
def RnClusterEvent (d : ℕ) : Set (Site d → Bool) :=
  {s | ∃ i : Site d, (componentIn (openSites s) i).Infinite}

/-- The configurations having an infinite open cluster with small holes. -/
def RnHoleEvent (d : ℕ) : Set (Site d → Bool) :=
  {s | ∃ i : Site d, (componentIn (openSites s) i).Infinite ∧
    RnHoleProp d (componentIn (openSites s) i)}

theorem rn_measurableSet_open {d : ℕ} (z : Site d) :
    MeasurableSet {s : Site d → Bool | z ∈ openSites s} :=
  measurableSet_eq_fun (measurable_pi_apply z) measurable_const

theorem rn_measurableSet_cluster_mem {d : ℕ} (i y : Site d) :
    MeasurableSet {s : Site d → Bool | y ∈ componentIn (openSites s) i} :=
  rn_measurableSet_mem_componentIn (fun s => openSites s) rn_measurableSet_open i y

theorem rn_measurableSet_cluster_infinite {d : ℕ} (i : Site d) :
    MeasurableSet {s : Site d → Bool | (componentIn (openSites s) i).Infinite} := by
  have : {s : Site d → Bool | (componentIn (openSites s) i).Infinite} =
      (⋃ m : ℕ, {s : Site d → Bool | (componentIn (openSites s) i).Finite ∧
        (componentIn (openSites s) i).ncard ≤ m})ᶜ := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists, not_and]
    constructor
    · intro h m hfin
      exact absurd hfin h
    · intro h hfin
      exact h _ hfin le_rfl
  rw [this]
  exact (MeasurableSet.iUnion fun m => rn_measurableSet_finite_ncard_le
    (fun s => componentIn (openSites s) i) (fun v => rn_measurableSet_cluster_mem i v) m).compl

theorem rn_measurableSet_clusterEvent (d : ℕ) : MeasurableSet (RnClusterEvent d) := by
  have : RnClusterEvent d = ⋃ i : Site d, {s : Site d → Bool |
      (componentIn (openSites s) i).Infinite} := by
    ext s; simp [RnClusterEvent]
  rw [this]
  exact MeasurableSet.iUnion fun i => rn_measurableSet_cluster_infinite i

theorem rn_measurableSet_holeProp {d : ℕ} (i : Site d) :
    MeasurableSet {s : Site d → Bool | RnHoleProp d (componentIn (openSites s) i)} := by
  set C : (Site d → Bool) → Set (Site d) := fun s => componentIn (openSites s) i with hC
  have hCm : ∀ z, MeasurableSet {s : Site d → Bool | z ∈ (C s)ᶜ} := fun z => by
    exact (rn_measurableSet_cluster_mem (d := d) i z).compl
  have hfin : ∀ (x : Site d) (b : ℝ), MeasurableSet {s : Site d → Bool |
      (componentIn (C s)ᶜ x).Finite ∧ ((componentIn (C s)ᶜ x).ncard : ℝ) < b} := by
    intro x b
    have : {s : Site d → Bool | (componentIn (C s)ᶜ x).Finite ∧
        ((componentIn (C s)ᶜ x).ncard : ℝ) < b} =
        ⋃ m : ℕ, ({s : Site d → Bool | (componentIn (C s)ᶜ x).Finite ∧
          (componentIn (C s)ᶜ x).ncard ≤ m} ∩ {_s | (m : ℝ) < b}) := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨hf, hb⟩
        exact ⟨(componentIn (C s)ᶜ x).ncard, ⟨hf, le_rfl⟩, hb⟩
      · rintro ⟨m, ⟨hf, hm⟩, hb⟩
        exact ⟨hf, lt_of_le_of_lt (by exact_mod_cast hm) hb⟩
    rw [this]
    refine MeasurableSet.iUnion fun m => ?_
    refine (rn_measurableSet_finite_ncard_le (fun s => componentIn (C s)ᶜ x)
      (fun v => rn_measurableSet_mem_componentIn (fun s => (C s)ᶜ) hCm x v) m).inter ?_
    by_cases h : (m : ℝ) < b
    · simp only [h, Set.setOf_true]; exact MeasurableSet.univ
    · simp only [h, Set.setOf_false]; exact MeasurableSet.empty
  have : {s : Site d → Bool | RnHoleProp d (C s)} = ⋃ n0 : ℕ, ⋂ n : ℕ, ⋂ x : Site d,
      ({s : Site d → Bool | n0 ≤ n → x ∈ (cent d n : Set (Site d)) → x ∉ C s →
        ((componentIn (C s)ᶜ x).Finite ∧
          ((componentIn (C s)ᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))}) := by
    ext s
    simp only [RnHoleProp, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · rintro ⟨n0, h⟩
      exact ⟨n0, fun n x hn hx hxC => h n hn x hx hxC⟩
    · rintro ⟨n0, h⟩
      exact ⟨n0, fun n hn x hx hxC => h n x hn hx hxC⟩
  rw [this]
  refine MeasurableSet.iUnion fun n0 => MeasurableSet.iInter fun n => MeasurableSet.iInter fun x => ?_
  by_cases h1 : n0 ≤ n
  · by_cases h2 : x ∈ (cent d n : Set (Site d))
    · simp only [h1, h2, true_implies]
      have hh : {s : Site d → Bool | x ∉ C s → ((componentIn (C s)ᶜ x).Finite ∧
          ((componentIn (C s)ᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))} =
          {s : Site d → Bool | x ∈ C s} ∪ {s : Site d → Bool | (componentIn (C s)ᶜ x).Finite ∧
          ((componentIn (C s)ᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)} := by
        ext s
        simp only [Set.mem_setOf_eq, Set.mem_union]
        by_cases hx : x ∈ C s <;> simp [hx]
      rw [hh]
      exact (rn_measurableSet_cluster_mem (d := d) i x).union (hfin x _)
    · simp [h2]
  · simp [h1]

theorem rn_measurableSet_holeEvent (d : ℕ) : MeasurableSet (RnHoleEvent d) := by
  have : RnHoleEvent d = ⋃ i : Site d, ({s : Site d → Bool |
      (componentIn (openSites s) i).Infinite} ∩
        {s : Site d → Bool | RnHoleProp d (componentIn (openSites s) i)}) := by
    ext s; simp [RnHoleEvent]
  rw [this]
  exact MeasurableSet.iUnion fun i =>
    (rn_measurableSet_cluster_infinite i).inter (rn_measurableSet_holeProp i)

theorem rn_componentIn_mono {d : ℕ} {S S' : Set (Site d)} (h : S ⊆ S') (x : Site d) :
    componentIn S x ⊆ componentIn S' x := by
  rintro y ⟨hx, hy, hr⟩
  have := hr.map ((lattice d).induceHomOfLE h).toHom
  exact ⟨h hx, h hy, this⟩

theorem rn_holeProp_mono {d : ℕ} {C C' : Set (Site d)} (h : C ⊆ C') (hC : RnHoleProp d C) :
    RnHoleProp d C' := by
  obtain ⟨n0, hn0⟩ := hC
  refine ⟨n0, fun n hn x hx hxC' => ?_⟩
  have hxC : x ∉ C := fun hc => hxC' (h hc)
  obtain ⟨hfin, hlt⟩ := hn0 n hn x hx hxC
  have hsub : componentIn C'ᶜ x ⊆ componentIn Cᶜ x :=
    rn_componentIn_mono (Set.compl_subset_compl.mpr h) x
  refine ⟨hfin.subset hsub, lt_of_le_of_lt ?_ hlt⟩
  exact_mod_cast Set.ncard_le_ncard hsub hfin

theorem rn_openSites_mono {d : ℕ} {s s' : Site d → Bool} (h : ∀ z, s z = true → s' z = true) :
    openSites s ⊆ openSites s' := fun z hz => h z hz

theorem rn_clusterEvent_increasing (d : ℕ) : IsIncreasingSet (RnClusterEvent d) := by
  intro s s' ⟨i, hi⟩ h
  exact ⟨i, hi.mono (rn_componentIn_mono (rn_openSites_mono h) i)⟩

theorem rn_holeEvent_increasing (d : ℕ) : IsIncreasingSet (RnHoleEvent d) := by
  intro s s' ⟨i, hi, hh⟩ h
  have hsub := rn_componentIn_mono (rn_openSites_mono h) i
  exact ⟨i, hi.mono hsub, rn_holeProp_mono hsub hh⟩

/-- The sites having an open incident bond. -/
def rn_nonIso {d : ℕ} (ζ : RnBond d → Bool) : Site d → Bool :=
  fun x => decide (∃ b ∈ rn_incident d x, ζ b = true)

theorem rn_nonIso_measurable (d : ℕ) : Measurable (rn_nonIso (d := d)) := by
  refine measurable_pi_lambda _ fun x => measurable_to_bool ?_
  have : (fun ζ : RnBond d → Bool => rn_nonIso ζ x) ⁻¹' {true} =
      ⋃ b ∈ rn_incident d x, {ζ : RnBond d → Bool | ζ b = true} := by
    ext ζ; simp [rn_nonIso]
  rw [this]
  exact Finset.measurableSet_biUnion _ fun b _ => measurableSet_eq_fun (measurable_pi_apply b) measurable_const

theorem rn_openBond_adj {d : ℕ} {ζ : RnBond d → Bool} {u v : Site d}
    (h : (openBondGraph ζ).Adj u v) :
    (lattice d).Adj u v ∧ rn_nonIso ζ u = true ∧ rn_nonIso ζ v = true := by
  rw [openBondGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨hne, h | h⟩ := h
  · obtain ⟨i, hv, hζ⟩ := h
    refine ⟨⟨i, Or.inl hv⟩, ?_, ?_⟩
    · simp only [rn_nonIso, decide_eq_true_eq]
      exact ⟨(u, i), by simp [rn_incident], hζ⟩
    · simp only [rn_nonIso, decide_eq_true_eq]
      exact ⟨(u, i), by simp only [rn_incident, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and]; exact Or.inr ⟨i, by rw [hv]; simp⟩, hζ⟩
  · obtain ⟨i, hu, hζ⟩ := h
    refine ⟨⟨i, Or.inr hu⟩, ?_, ?_⟩
    · simp only [rn_nonIso, decide_eq_true_eq]
      exact ⟨(v, i), by simp only [rn_incident, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and]; exact Or.inr ⟨i, by rw [hu]; simp⟩, hζ⟩
    · simp only [rn_nonIso, decide_eq_true_eq]
      exact ⟨(v, i), by simp [rn_incident], hζ⟩

theorem rn_transGen_subset {d : ℕ} (ζ : RnBond d → Bool) {u y : Site d}
    (h : Relation.TransGen (openBondGraph ζ).Adj u y) :
    y ∈ componentIn (openSites (rn_nonIso ζ)) u := by
  induction h using Relation.TransGen.head_induction_on with
  | single hadj =>
    obtain ⟨hl, h1, h2⟩ := rn_openBond_adj hadj
    exact ⟨h1, h2, (SimpleGraph.Adj.reachable (G := (lattice d).induce (openSites (rn_nonIso ζ)))
      (u := ⟨_, h1⟩) (v := ⟨_, h2⟩) hl)⟩
  | head hadj _ ih =>
    obtain ⟨hl, h1, h2⟩ := rn_openBond_adj hadj
    obtain ⟨_, hy, hr⟩ := ih
    exact ⟨h1, hy, (SimpleGraph.Adj.reachable (G := (lattice d).induce (openSites (rn_nonIso ζ)))
      (u := ⟨_, h1⟩) (v := ⟨_, h2⟩) hl).trans hr⟩

theorem rn_nonIso_mono {d : ℕ} {ζ ζ' : RnBond d → Bool} (h : ∀ b, ζ b = true → ζ' b = true) :
    ∀ z, rn_nonIso ζ z = true → rn_nonIso ζ' z = true := by
  intro z hz
  simp only [rn_nonIso, decide_eq_true_eq] at hz ⊢
  obtain ⟨b, hb, hζ⟩ := hz
  exact ⟨b, hb, h b hζ⟩

/-- The configurations of bonds whose set of non-isolated sites has an infinite cluster. -/
def RnBondClusterEvent (d : ℕ) : Set (RnBond d → Bool) := rn_nonIso ⁻¹' RnClusterEvent d

theorem rn_bondClusterEvent_measurable (d : ℕ) : MeasurableSet (RnBondClusterEvent d) :=
  (rn_nonIso_measurable d) (rn_measurableSet_clusterEvent d)

theorem rn_bondClusterEvent_increasing (d : ℕ) : IsIncreasingSet (RnBondClusterEvent d) := by
  intro ζ ζ' hζ h
  exact rn_clusterEvent_increasing d _ _ hζ (rn_nonIso_mono h)

theorem rn_theta_le (d : ℕ) (q : ℝ) :
    bondTheta d q ≤ bondPercolation d q (RnBondClusterEvent d) := by
  unfold bondTheta
  refine measure_mono (fun ζ hζ => ?_)
  simp only [Set.mem_setOf_eq] at hζ
  simp only [RnBondClusterEvent, RnClusterEvent, Set.mem_preimage, Set.mem_setOf_eq]
  refine ⟨0, (hζ.sdiff (Set.finite_singleton 0)).mono ?_⟩
  rintro y ⟨hy, hy0⟩
  have hy0' : y ≠ 0 := hy0
  obtain ⟨hr⟩ := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hy |> fun h => (⟨h⟩ : Nonempty _)
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hr with h | h
  · exact absurd h hy0'
  · exact rn_transGen_subset ζ h

theorem rn_lattice_adj_add {d : ℕ} (a : Site d) {u v : Site d} (h : (lattice d).Adj u v) :
    (lattice d).Adj (u + a) (v + a) := by
  obtain ⟨i, hi | hi⟩ := h
  · exact ⟨i, Or.inl (by rw [hi]; abel)⟩
  · exact ⟨i, Or.inr (by rw [hi]; abel)⟩

theorem rn_componentIn_translate {d : ℕ} {S S' : Set (Site d)} (a : Site d)
    (hS : ∀ u ∈ S, u + a ∈ S') (x : Site d) :
    (fun u => u + a) '' componentIn S x ⊆ componentIn S' (x + a) := by
  rintro _ ⟨y, ⟨hx, hy, hr⟩, rfl⟩
  let φ : lattice d →g lattice d := ⟨fun u => u + a, fun h => rn_lattice_adj_add a h⟩
  let ψ := SimpleGraph.induceHom φ (show Set.MapsTo φ S S' from fun u hu => hS u hu)
  exact ⟨hS x hx, hS y hy, hr.map ψ⟩

theorem rn_cluster_shift {d : ℕ} (w : Site d) {s : Site d → Bool} (hs : s ∈ RnClusterEvent d) :
    coordShift (fun x : Site d => x + w) s ∈ RnClusterEvent d := by
  obtain ⟨i, hi⟩ := hs
  refine ⟨i + -w, ?_⟩
  have hsub := rn_componentIn_translate (S := openSites s) (S' := openSites (coordShift (fun x : Site d => x + w) s))
    (-w) (fun u hu => by
      show coordShift (fun x : Site d => x + w) s (u + -w) = true
      simp only [coordShift_apply]
      rw [show u + -w + w = u by abel]; exact hu) i
  exact (hi.image (fun a _ b _ h => add_right_cancel h)).mono hsub

theorem rn_clusterEvent_shift_invariant {d : ℕ} (w : Site d) :
    coordShift (fun x : Site d => x + w) ⁻¹' RnClusterEvent d = RnClusterEvent d := by
  ext s
  simp only [Set.mem_preimage]
  constructor
  · intro h
    have := rn_cluster_shift (-w) h
    have e : coordShift (fun x : Site d => x + -w) (coordShift (fun x : Site d => x + w) s) = s := by
      funext x; simp only [coordShift_apply]; rw [show x + -w + w = x by abel]
    rwa [e] at this
  · exact rn_cluster_shift w

theorem rn_nonIso_edge_le {d : ℕ} (ω : Site d → Bool) (z : Site d)
    (hz : rn_nonIso (fun e : RnBond d => ω e.1 && ω (e.1 + unit e.2)) z = true) : ω z = true := by
  simp only [rn_nonIso, decide_eq_true_eq] at hz
  obtain ⟨b, hb, hb2⟩ := hz
  simp only [Bool.and_eq_true] at hb2
  simp only [rn_incident, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hb
  rcases hb with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact hb2.1
  · have : z - unit j + unit j = z := by abel
    simpa [this] using hb2.2

theorem rn_cluster_ae (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (d : ℕ) (hd : 1 ≤ d) (qP : ℝ) (hq0 : 0 ≤ qP) (hq1 : qP < 1) (hθ : bondTheta d qP ≠ 0) :
    ∃ q : ℝ, q < 1 ∧ ∀ ρ₂ : ℝ, q ≤ ρ₂ → ρ₂ ≤ 1 → sitePercolation d ρ₂ (RnClusterEvent d)ᶜ = 0 := by
  obtain ⟨q, hq1', hdom⟩ := rn_edge_dom hLSSB d qP hq0 hq1
  refine ⟨max q 0, max_lt hq1' zero_lt_one, fun ρ₂ hρ hρ1 => ?_⟩
  have hρ0 : 0 ≤ ρ₂ := (le_max_right _ _).trans hρ
  have hρq : q ≤ ρ₂ := (le_max_left _ _).trans hρ
  haveI := rn_infinitePi_isProb (ι := Site d) hρ0 hρ1
  set P : Measure (Site d → Bool) := sitePercolation d ρ₂ with hP
  haveI : IsProbabilityMeasure P := rn_infinitePi_isProb (ι := Site d) hρ0 hρ1
  have hind : iIndepFun (fun (x : Site d) (ω : Site d → Bool) => ω x) P :=
    rn_bernoulli_iIndep hρ0 hρ1
  have hmarg : ∀ x : Site d, ENNReal.ofReal q ≤ P {ω | (fun (x : Site d) (ω : Site d → Bool) => ω x) x ω = true} := by
    intro x
    show ENNReal.ofReal q ≤ P {ω | ω x = true}
    rw [hP, sitePercolation, rn_bernoulli_marg hρ0 hρ1]
    exact ENNReal.ofReal_le_ofReal hρq
  have h1 := hdom P (fun (x : Site d) (ω : Site d → Bool) => ω x) (fun x => measurable_pi_apply x)
    hind hmarg (RnBondClusterEvent d) (rn_bondClusterEvent_measurable d)
    (rn_bondClusterEvent_increasing d)
  have h2 : bondTheta d qP ≤ P (RnClusterEvent d) := by
    refine (rn_theta_le d qP).trans (h1.trans' le_rfl |>.trans ?_)
    refine measure_mono (fun ω hω => ?_)
    simp only [Set.mem_setOf_eq, RnBondClusterEvent, Set.mem_preimage] at hω
    exact rn_clusterEvent_increasing d _ _ hω (fun z hz => rn_nonIso_edge_le ω z hz)
  have hpos : P (RnClusterEvent d) ≠ 0 := by
    intro h0
    rw [h0] at h2
    exact hθ (nonpos_iff_eq_zero.mp h2)
  haveI : IsProbabilityMeasure (bitLaw ρ₂) := rn_bitLaw_isProb hρ0 hρ1
  have h01 := LatticeProb.measure_zero_or_one_of_allTranslationInvariant (bitLaw ρ₂)
    (v := unit ⟨0, by omega⟩) (unit_ne_zero _) (rn_measurableSet_clusterEvent d)
    (fun w => rn_clusterEvent_shift_invariant w)
  have hone : P (RnClusterEvent d) = 1 := by
    rcases h01 with h | h
    · exact absurd h hpos
    · exact h
  exact (prob_compl_eq_zero_iff (rn_measurableSet_clusterEvent d)).mpr hone

theorem rn_holeEvent_ae (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (d : ℕ) (hd : 2 ≤ d) (qP : ℝ) (hq0 : 0 ≤ qP) (hq1 : qP < 1) (hθ : bondTheta d qP ≠ 0) :
    ∃ q : ℝ, q < 1 ∧ ∀ ρ₂ : ℝ, q ≤ ρ₂ → ρ₂ ≤ 1 → sitePercolation d ρ₂ (RnHoleEvent d)ᶜ = 0 := by
  obtain ⟨qc, hqc1, hclus⟩ := rn_cluster_ae hLSSB d (by omega) qP hq0 hq1 hθ
  obtain ⟨q₀, hq₀1, hq₀⟩ := hHole d hd
  refine ⟨max (max qc 0) ((q₀ + 1) / 2), max_lt (max_lt hqc1 zero_lt_one) (by linarith), ?_⟩
  intro ρ₂ hρ hρ1
  have hρqc : qc ≤ ρ₂ := (le_max_left _ _).trans ((le_max_left _ _).trans hρ)
  have hρ₀ : q₀ < ρ₂ := lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans hρ)
  have h1 := hclus ρ₂ hρqc hρ1
  have h2 := hq₀ ρ₂ hρ₀ hρ1
  rw [MeasureTheory.ae_iff] at h2
  refine measure_mono_null (fun s hs => ?_) (measure_union_null h1 h2)
  by_contra hcon
  simp only [Set.mem_union, not_or, Set.mem_compl_iff, not_not, Set.mem_setOf_eq] at hcon hs
  obtain ⟨hclu, hall⟩ := hcon
  obtain ⟨i, hi⟩ := hclu
  apply hs
  refine ⟨i, hi, ?_⟩
  have hiC : i ∈ componentIn (openSites s) i := by
    obtain ⟨y, hy⟩ := hi.nonempty
    obtain ⟨hx, _, _⟩ := hy
    exact ⟨hx, hx, SimpleGraph.Reachable.refl _⟩
  exact hall _ ⟨hi, i, hiC, rfl⟩

/-- The field of sites all of whose incident bonds are open. -/
def rn_siteField {d : ℕ} (ζ : RnBond d → Bool) : Site d → Bool :=
  fun x => decide (∀ b ∈ rn_incident d x, ζ b = true)

theorem rn_siteField_measurable (d : ℕ) : Measurable (rn_siteField (d := d)) := by
  refine measurable_pi_lambda _ fun x => measurable_to_bool ?_
  have : (fun ζ : RnBond d → Bool => rn_siteField ζ x) ⁻¹' {true} =
      ⋂ b ∈ rn_incident d x, {ζ : RnBond d → Bool | ζ b = true} := by
    ext ζ; simp [rn_siteField]
  rw [this]
  exact Finset.measurableSet_biInter _ fun b _ =>
    measurableSet_eq_fun (measurable_pi_apply b) measurable_const

theorem rn_lattice_adj_openBond {d : ℕ} {ζ : RnBond d → Bool} {u v : Site d}
    (hu : rn_siteField ζ u = true) (hv : rn_siteField ζ v = true) (h : (lattice d).Adj u v) :
    (openBondGraph ζ).Adj u v := by
  simp only [rn_siteField, decide_eq_true_eq] at hu hv
  rw [openBondGraph, SimpleGraph.fromRel_adj]
  refine ⟨(lattice d).ne_of_adj h, ?_⟩
  obtain ⟨i, hi | hi⟩ := h
  · exact Or.inl ⟨i, hi, hu (u, i) (by simp [rn_incident])⟩
  · refine Or.inr ⟨i, hi, hv (v, i) ?_⟩
    simp [rn_incident]

theorem rn_hole_of_siteField {d : ℕ} {ζ : RnBond d → Bool} (h : rn_siteField ζ ∈ RnHoleEvent d) :
    ∃ i, {y | (openBondGraph ζ).Reachable i y}.Infinite ∧
      RnHoleProp d {y | (openBondGraph ζ).Reachable i y} := by
  obtain ⟨j, hinf, hhole⟩ := h
  have hsub : componentIn (openSites (rn_siteField ζ)) j ⊆ {y | (openBondGraph ζ).Reachable j y} := by
    rintro y ⟨hj, hy, hr⟩
    let hom : (lattice d).induce (openSites (rn_siteField ζ)) →g openBondGraph ζ :=
      ⟨Subtype.val, fun {a b} hab => rn_lattice_adj_openBond a.2 b.2 hab⟩
    exact hr.map hom
  exact ⟨j, hinf.mono hsub, rn_holeProp_mono hsub hhole⟩

theorem rn_siteField_ae (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (d : ℕ) (hd : 2 ≤ d) (qP : ℝ) (hq0 : 0 ≤ qP) (hq1 : qP < 1) (hθ : bondTheta d qP ≠ 0) :
    ∃ r : ℝ, r < 1 ∧ ∀ ρ₁ : ℝ, r ≤ ρ₁ → ρ₁ ≤ 1 →
      bondPercolation d ρ₁ {ζ | ¬ ∃ i, {y | (openBondGraph ζ).Reachable i y}.Infinite ∧
        RnHoleProp d {y | (openBondGraph ζ).Reachable i y}} = 0 := by
  obtain ⟨q, hq1, hhole⟩ := rn_holeEvent_ae hLSSB hHole d hd qP hq0 hq1 hθ
  have hq0' : 0 ≤ max q 0 := le_max_right _ _
  set ρ₂ : ℝ := (max q 0 + 1) / 2 with hρ₂
  have hρ₂1 : ρ₂ < 1 := by rw [hρ₂]; linarith [max_lt hq1 zero_lt_one]
  have hρ₂q : q ≤ ρ₂ := by rw [hρ₂]; linarith [le_max_left q 0, max_lt hq1 zero_lt_one]
  have hρ₂0 : 0 ≤ ρ₂ := by rw [hρ₂]; linarith
  obtain ⟨r, hr0, hr1, hr⟩ := rn_site_dom hLSSB d (by omega) ρ₂ hρ₂0 hρ₂1
  refine ⟨r, hr1, fun ρ₁ hrρ hρ₁1 => ?_⟩
  have hρ₁0 : 0 ≤ ρ₁ := hr0.trans hrρ
  haveI : IsProbabilityMeasure (bondPercolation d ρ₁) := rn_infinitePi_isProb hρ₁0 hρ₁1
  have h1 := hr ρ₁ hrρ hρ₁1 (RnHoleEvent d) (rn_measurableSet_holeEvent d) (rn_holeEvent_increasing d)
  have h2 : sitePercolation d ρ₂ (RnHoleEvent d) = 1 := by
    haveI : IsProbabilityMeasure (sitePercolation d ρ₂) := rn_infinitePi_isProb hρ₂0 hρ₂1.le
    exact (prob_compl_eq_zero_iff (rn_measurableSet_holeEvent d)).mp (hhole ρ₂ hρ₂q hρ₂1.le)
  have h3 : bondPercolation d ρ₁ (rn_siteField ⁻¹' RnHoleEvent d) = 1 := by
    refine le_antisymm prob_le_one ?_
    have : bernoulliProduct (Site d) ρ₂ (RnHoleEvent d) = 1 := h2
    rw [this] at h1
    exact h1
  have h4 := (prob_compl_eq_zero_iff ((rn_siteField_measurable d) (rn_measurableSet_holeEvent d))).mpr h3
  refine measure_mono_null (fun ζ hζ => ?_) h4
  simp only [Set.mem_setOf_eq] at hζ
  simp only [Set.mem_compl_iff, Set.mem_preimage]
  intro hh
  exact hζ (rn_hole_of_siteField hh)

end Exploding
