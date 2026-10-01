/-
The high-density Peierls estimate for the good cluster of the origin: if the
good cluster misses `y`, a `*`-connected set of bad sites separates `0` from `y`;
each cube of such a set has a closed bond, and a `3`-spaced subpacking of the set
is independent, so the chance of a bad set of size `s` is at most `(1 - δ)^{s/3^d}`.
Counting the `*`-connected sets against the geometric size of a separating set
gives the exponential bound.
-/
import Exploding.Support.ExtAPProof2
import Exploding.Support.RNProofGraph

open Exploding LatticeProb MeasureTheory ProbabilityTheory

namespace Exploding

variable {d : ℕ}

/-! ### The good cluster and its separating sets -/

/-- `0` is joined to `y` by a walk of good sites. -/
def xap3_GoodConnected (ω : Site d × Fin d → Bool) (y : Site d) : Prop :=
  ∃ p : (xap2_kingGraph d).Walk (0 : Site d) y, ∀ z ∈ p.support, xap_Good ω z

/-- Every star-walk from `0` to `y` meets the set `Γ`. -/
def xap3_Separates (Γ : Set (Site d)) (y : Site d) : Prop :=
  ∀ p : (xap2_kingGraph d).Walk (0 : Site d) y, ∃ z ∈ p.support, z ∈ Γ

/-- A set of bad sites separating `0` from `y` prevents a good connection. -/
theorem xap3_not_goodConnected_of_badSeparates {ω : Site d × Fin d → Bool} {y : Site d}
    {Γ : Set (Site d)} (hbad : ∀ z ∈ Γ, ¬ xap_Good ω z) (hsep : xap3_Separates Γ y) :
    ¬ xap3_GoodConnected ω y := by
  rintro ⟨p, hp⟩
  obtain ⟨z, hzp, hzΓ⟩ := hsep p
  exact hbad z hzΓ (hp z hzp)

/-! ### A `3`-spaced subpacking of a finite set -/

/-- The coarse colour of a site: its coordinates modulo three. -/
def xap3_color (z : Site d) : Fin d → Fin 3 :=
  fun i => ⟨(z i % 3).toNat, by
    have h1 : 0 ≤ z i % 3 := Int.emod_nonneg _ (by norm_num)
    have h2 : z i % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega⟩

/-- Sites of the same colour are either equal or at sup-distance at least `3`. -/
theorem xap3_same_color_far {z w : Site d} (hc : xap3_color z = xap3_color w) (hne : z ≠ w) :
    ∃ i, 3 ≤ |z i - w i| := by
  by_contra hcon
  push Not at hcon
  apply hne
  funext i
  have hi : z i % 3 = w i % 3 := by
    have := congrFun hc i
    simp only [xap3_color, Fin.mk.injEq] at this
    have h1 : 0 ≤ z i % 3 := Int.emod_nonneg _ (by norm_num)
    have h2 : z i % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have h3 : 0 ≤ w i % 3 := Int.emod_nonneg _ (by norm_num)
    have h4 : w i % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  have hdvd : (3 : ℤ) ∣ z i - w i := by
    rw [Int.dvd_iff_emod_eq_zero]
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hi
  have hle : |z i - w i| < 3 := hcon i
  have h1 : z i - w i < 3 := (abs_lt.mp hle).2
  have h2 : -(3 : ℤ) < z i - w i := (abs_lt.mp hle).1
  obtain ⟨k, hk⟩ := hdvd
  omega

/-- Every finite set has a subpacking of pairwise `3`-spaced sites covering at
least a `3^{-d}` fraction of it. -/
theorem xap3_exists_packing (Γ : Finset (Site d)) :
    ∃ Γ' ⊆ Γ, (∀ z ∈ Γ', ∀ w ∈ Γ', z ≠ w → ∃ i, 3 ≤ |z i - w i|) ∧
      Γ.card ≤ 3 ^ d * Γ'.card := by
  classical
  let fib : (Fin d → Fin 3) → Finset (Site d) := fun c => Γ.filter fun z => xap3_color z = c
  have hdisj : ∀ c ∈ (Finset.univ : Finset (Fin d → Fin 3)),
      ∀ c' ∈ Finset.univ, c ≠ c' → Disjoint (fib c) (fib c') := by
    intro c _ c' _ hcc
    rw [Finset.disjoint_left]
    intro z hzc hzc'
    exact hcc ((Finset.mem_filter.1 hzc).2.symm.trans (Finset.mem_filter.1 hzc').2)
  have hUnion : Γ = Finset.univ.biUnion fib := by
    ext z
    constructor
    · intro hz
      exact Finset.mem_biUnion.2 ⟨xap3_color z, Finset.mem_univ _, Finset.mem_filter.2 ⟨hz, rfl⟩⟩
    · intro hz
      rcases Finset.mem_biUnion.1 hz with ⟨c, _, hzc⟩
      exact (Finset.mem_filter.1 hzc).1
  have hsum : Γ.card = ∑ c : Fin d → Fin 3, (fib c).card := by
    rw [hUnion, Finset.card_biUnion hdisj]
  obtain ⟨c₀, _, hc₀⟩ := Finset.exists_max_image Finset.univ (fun c => (fib c).card)
    Finset.univ_nonempty
  refine ⟨fib c₀, Finset.filter_subset _ _, ?_, ?_⟩
  · intro z hz w hw hne
    exact xap3_same_color_far
      ((Finset.mem_filter.1 hz).2.trans (Finset.mem_filter.1 hw).2.symm) hne
  · calc Γ.card = ∑ c : Fin d → Fin 3, (fib c).card := hsum
      _ ≤ ∑ _c : Fin d → Fin 3, (fib c₀).card := Finset.sum_le_sum fun c _ => hc₀ c (Finset.mem_univ c)
      _ = 3 ^ d * (fib c₀).card := by
          rw [Finset.sum_const, smul_eq_mul]
          congr 1
          simp

end Exploding
