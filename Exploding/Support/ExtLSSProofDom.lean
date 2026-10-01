/-
The finite-coordinate form of the product law: on a finite set of coordinates the
product measure of a finite set is the sum of the weights of its elements.  This
is the building block for the finite-coordinate domination step of the
bounded-degree theorem.
-/
import Exploding.Support.ExtLSSProofThin

open MeasureTheory ProbabilityTheory

namespace Exploding

variable {S : Type}

/-- The finite product of probability measures on `ι → Bool`, evaluated on a finite set, as the
sum of the weights of its elements. -/
theorem xlss_pi_eq_sum {ι : Type*} [Fintype ι] (μ : ι → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] (B : Finset (ι → Bool)) :
    Measure.pi μ ((B : Set (ι → Bool))) = ∑ x ∈ B, ∏ i, μ i {x i} := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert a B ha ih =>
    rw [Finset.coe_insert, Finset.sum_insert ha]
    have hins : (insert a (↑B : Set (ι → Bool))) = ({a} : Set (ι → Bool)) ∪ (↑B : Set _) :=
      Set.insert_eq a (↑B : Set (ι → Bool))
    rw [hins, measure_union (by rw [Set.disjoint_singleton_left]; exact ha)
      B.finite_toSet.measurableSet, Measure.pi_singleton, ih]

/-- The `ENNReal` form of the thinning's normalisation. -/
theorem xlss_thin_norm_ofReal [DecidableEq S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ γ : ℝ) (T : Finset S) (w : S → Bool → Finset S → ℝ) (hw : XlssThin μ ρ γ T w)
    (x : S → Bool) :
    ∑ V ∈ T.powerset, ENNReal.ofReal (∏ l ∈ T, w l (x l) V) = 1 := by
  rw [← ENNReal.ofReal_one, ← hw.norm x]
  rw [ENNReal.ofReal_sum_of_nonneg]
  exact fun V hV => Finset.prod_nonneg fun l hl => (hw.bd l hl V (Finset.mem_powerset.mp hV) _).1

/-- The `ENNReal` form of the thinning's marginal law. -/
theorem xlss_thin_marg_ofReal [DecidableEq S] (μ : Measure (S → Bool)) [IsProbabilityMeasure μ]
    (ρ γ : ℝ) (T : Finset S) (w : S → Bool → Finset S → ℝ) (hw : XlssThin μ ρ γ T w)
    (V : Finset S) (hV : V ⊆ T) :
    ∫⁻ x, ENNReal.ofReal (∏ l ∈ T, w l (x l) V) ∂μ =
      ENNReal.ofReal (ρ ^ V.card * (1 - ρ) ^ (T.card - V.card)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (xlss_integrable_prod μ T (fun l b => w l b V) (fun l hl => hw.bd l hl V hV))
    (Filter.Eventually.of_forall fun x =>
      Finset.prod_nonneg fun l hl => (hw.bd l hl V hV _).1)]
  rw [hw.marg V hV]

/-- The subset of `T` carved out by a `T`-indexed bit configuration. -/
def xlss_Vof (T : Finset S) (v : T → Bool) : Finset S :=
  (Finset.univ.filter (fun t : T => v t = true)).map
    (Function.Embedding.subtype (fun s : S => s ∈ T))

theorem xlss_Vof_subset (T : Finset S) (v : T → Bool) : xlss_Vof T v ⊆ T := by
  intro s hs
  obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hs
  exact t.2

theorem xlss_mem_Vof (T : Finset S) (v : T → Bool) (s : S) :
    s ∈ xlss_Vof T v ↔ ∃ hs : s ∈ T, v ⟨s, hs⟩ = true := by
  rw [xlss_Vof, Finset.mem_map]
  constructor
  · rintro ⟨t, ht, hts⟩
    rw [Finset.mem_filter] at ht
    refine ⟨hts ▸ t.2, ?_⟩
    have ht' : (⟨s, hts ▸ t.2⟩ : T) = t := Subtype.ext hts.symm
    rw [ht']
    exact ht.2
  · rintro ⟨hs, hv⟩
    exact ⟨⟨s, hs⟩, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hv⟩, rfl⟩

theorem xlss_Vof_injective (T : Finset S) : Function.Injective (xlss_Vof T) := by
  intro v v' h
  funext t
  have h1 : v t = true ↔ (t : S) ∈ xlss_Vof T v := by
    rw [xlss_mem_Vof]
    exact ⟨fun hv => ⟨t.2, hv⟩, fun ⟨hs, hv⟩ => by
      have : (⟨(t : S), hs⟩ : T) = t := Subtype.ext rfl
      rwa [this] at hv⟩
  have h2 : v' t = true ↔ (t : S) ∈ xlss_Vof T v' := by
    rw [xlss_mem_Vof]
    exact ⟨fun hv => ⟨t.2, hv⟩, fun ⟨hs, hv⟩ => by
      have : (⟨(t : S), hs⟩ : T) = t := Subtype.ext rfl
      rwa [this] at hv⟩
  have hmem : (t : S) ∈ xlss_Vof T v ↔ (t : S) ∈ xlss_Vof T v' := by rw [h]
  have hiff : (v t = true) ↔ (v' t = true) := h1.trans (hmem.trans h2.symm)
  cases hvt : v t <;> cases hv't : v' t <;> simp_all

theorem xlss_Vof_surjective (T : Finset S) :
    ∀ V ∈ T.powerset, ∃ v : T → Bool, xlss_Vof T v = V := by
  classical
  intro V hV
  refine ⟨fun t => decide ((t : S) ∈ V), ?_⟩
  ext s
  rw [xlss_mem_Vof]
  constructor
  · rintro ⟨_, hv⟩
    simpa using hv
  · intro hsV
    exact ⟨Finset.mem_powerset.mp hV hsV, by rw [decide_eq_true_iff]; exact hsV⟩

/-- A bit configuration on `T` is equivalent to the subset of `T` that it occupies. -/
noncomputable def xlss_VofEquiv (T : Finset S) :
    (T → Bool) ≃ {V : Finset S // V ∈ T.powerset} where
  toFun v := ⟨xlss_Vof T v, Finset.mem_powerset.mpr (xlss_Vof_subset T v)⟩
  invFun V := Classical.choose (xlss_Vof_surjective T V.1 V.2)
  left_inv v := xlss_Vof_injective T (Classical.choose_spec
    (xlss_Vof_surjective T (xlss_Vof T v) (Finset.mem_powerset.mpr (xlss_Vof_subset T v))))
  right_inv V := Subtype.ext (Classical.choose_spec (xlss_Vof_surjective T V.1 V.2))

/-- Reindexing a sum over the powerset of `T` as a sum over `T`-bit configurations. -/
theorem xlss_sum_Vof [DecidableEq S] (T : Finset S) (g : Finset S → ENNReal) :
    ∑ v : T → Bool, g (xlss_Vof T v) = ∑ V ∈ T.powerset, g V := by
  classical
  rw [← Finset.sum_attach T.powerset g]
  exact (xlss_VofEquiv T).sum_comp (fun V : {V : Finset S // V ∈ T.powerset} => g V.1)

/-- The cardinality of the occupied subset. -/
theorem xlss_card_Vof [DecidableEq S] (T : Finset S) (v : T → Bool) :
    (xlss_Vof T v).card = (Finset.univ.filter (fun t : T => v t = true)).card := by
  rw [xlss_Vof, Finset.card_map]

/-- The product of one-site Bernoulli masses of a bit configuration. -/
theorem xlss_bitLaw_prod [DecidableEq S] (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (T : Finset S) (v : T → Bool) :
    ∏ t : T, bitLaw ρ {v t} =
      ENNReal.ofReal (ρ ^ (xlss_Vof T v).card *
        (1 - ρ) ^ (T.card - (xlss_Vof T v).card)) := by
  classical
  have hbit : ∀ b : Bool,
      bitLaw ρ {b} = if b then ENNReal.ofReal ρ else ENNReal.ofReal (1 - ρ) := by
    intro b
    cases b <;> simp [bitLaw]
  simp only [hbit]
  have hite : ∀ t : T, (if v t then ENNReal.ofReal ρ else ENNReal.ofReal (1 - ρ)) =
      ENNReal.ofReal (if v t then ρ else 1 - ρ) := by
    intro t
    split_ifs <;> rfl
  simp_rw [hite]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    rw [xlss_card_Vof, Finset.prod_ite,
      Finset.prod_eq_pow_card (fun _ _ => rfl),
      Finset.prod_eq_pow_card (fun _ _ => rfl)]
    have hcard : (Finset.univ.filter (fun t : T => v t = true)).card +
        (Finset.univ.filter (fun t : T => ¬ (v t = true))).card = T.card := by
      rw [Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun t : T => v t = true), Finset.card_univ, Fintype.card_coe]
    have hsub : (Finset.univ.filter (fun t : T => ¬ (v t = true))).card =
        T.card - (Finset.univ.filter (fun t : T => v t = true)).card := by omega
    rw [hsub]
  · intro t _
    split_ifs
    · exact hρ0
    · linarith

end Exploding
