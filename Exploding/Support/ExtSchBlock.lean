/-
A block is spanned with probability bounded below.  A block of size `s` along `J` is spanned
if its seed, a box of size `L` inside it, is fully occupied and every layer of the growth schedule
from the seed to the block is spanned along the other directions.  The seed and the layers lie on
disjoint sets of sites, so the two events are independent, and the layers fail with probability
at most `|J|` times the sum of the bounds for one dimension less.
-/
import Exploding.Support.ExtSchGrow
import Exploding.Support.ExtSchGrowProb
import Exploding.Support.ExtSchSeed

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

section BlockGood
variable {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (P : xss_Plan d) {s : ℕ}

/-- **A block is spanned with probability bounded below.** -/
theorem xsr_block_good (hd : 1 ≤ d) (hP : xss_Valid P s) (hL : 1 ≤ P.L)
    (hseed : ∀ i ∈ P.J, P.hi0 i - P.lo0 i + 1 = (P.L : ℤ)) {g : ℕ → ℝ}
    (hg0 : ∀ a, 0 ≤ g a)
    (hg : ∀ (J' : Finset (Fin d)) (lo hi : Site d) (a : ℕ), J'.card = P.J.card - 1 → 1 ≤ a →
      xsb_Near J' a lo hi →
        (xsch_mu d p).real {η | ¬ xsch_Sp J' (xsb_box lo hi) η} ≤ g a) :
    p ^ (P.L ^ P.J.card) * (1 - (P.J.card : ℝ) * ∑ a ∈ Finset.Icc P.L s, g a)
      ≤ (xsch_mu d p).real {η | xsch_Sp P.J (xsb_box P.LO P.HI) η} := by
  have hp0 : 0 ≤ p := (Fact.out : 0 ≤ p ∧ p ≤ 1).1
  set S : Set (Site d → ℤ) := {η | ∀ x ∈ xsb_box P.lo0 P.hi0, η x = 2 * (d : ℤ)} with hS
  set F : Set (Site d → ℤ) := {η | ∀ t < xss_steps P s,
    xsch_Sp (P.J.erase (xss_dir P hP.1 t)) (xss_layer P t) η} with hF
  set W : Set (Site d) := xsb_box P.LO P.HI \ xsb_box P.lo0 P.hi0 with hW
  have hWfin : W.Finite := (xsb_box_finite P.LO P.HI).subset Set.sdiff_subset
  have hlayerW : ∀ t, xss_layer P t ⊆ W := fun t x hx =>
    ⟨xss_layer_subset_target P hP t hx, fun hx' =>
      Set.disjoint_left.mp (xss_layer_disjoint_seed P hP t) hx hx'⟩
  have hFdet : xsch_Det W F := fun η η' hag =>
    ⟨fun h t ht => (xsch_det_Sp _ _ η η' fun x hx => hag x (hlayerW t hx)).1 (h t ht),
     fun h t ht => (xsch_det_Sp _ _ η η' fun x hx => hag x (hlayerW t hx)).2 (h t ht)⟩
  have hSdet : xsch_Det (xsb_box P.lo0 P.hi0) S := xsch_det_occ _
  have hdisj : Disjoint (xsb_box P.lo0 P.hi0) W := Set.disjoint_sdiff_right
  have hSprob : (xsch_mu d p).real S = p ^ (P.L ^ P.J.card) :=
    xsp_seed_prob hd hseed hP.2.2.1.2
  have hFmeas : MeasurableSet F := hFdet.measurableSet hWfin
  have hFprob : 1 - (P.J.card : ℝ) * ∑ a ∈ Finset.Icc P.L s, g a ≤ (xsch_mu d p).real F := by
    have h1 := xsr_layers_fail_le (p := p) P hP hL hg0 hg
    have h2 : {η : Site d → ℤ | ¬ ∀ t < xss_steps P s,
        xsch_Sp (P.J.erase (xss_dir P hP.1 t)) (xss_layer P t) η} = Fᶜ := rfl
    rw [h2, measureReal_compl hFmeas, probReal_univ] at h1
    linarith
  have hinter : (xsch_mu d p).real (S ∩ F) = (xsch_mu d p).real S * (xsch_mu d p).real F :=
    xsch_indep_two (xsb_box_finite _ _) hWfin hdisj hSdet hFdet
  have hsub : S ∩ F ⊆ {η | xsch_Sp P.J (xsb_box P.LO P.HI) η} := by
    rintro η ⟨hSη, hFη⟩
    have hseedbox : xsb_box P.lo0 P.hi0 ⊆ xsb_box P.LO P.HI :=
      xsb_box_mono (fun i => (hP.2.2.2.1 i).1) fun i => (hP.2.2.2.1 i).2
    exact xsr_top_of_layers P hP hL subset_rfl
      (fun x hx => xsch_Top.occ (hseedbox hx) (hSη x hx)) hFη
  calc p ^ (P.L ^ P.J.card) * (1 - (P.J.card : ℝ) * ∑ a ∈ Finset.Icc P.L s, g a)
      ≤ (xsch_mu d p).real S * (xsch_mu d p).real F := by
        rw [hSprob]
        exact mul_le_mul_of_nonneg_left hFprob (pow_nonneg hp0 _)
    _ = (xsch_mu d p).real (S ∩ F) := hinter.symm
    _ ≤ (xsch_mu d p).real {η | xsch_Sp P.J (xsb_box P.LO P.HI) η} := measureReal_mono hsub

end BlockGood

end Exploding
