/-
The setting and the five hypotheses of Section 5 of `paper/exploding.tex`, and
the box-crossing vocabulary of Section 7.

`B_k` is the rectangular box of side lengths `k : Fin d → ℕ`; `rboxShift k j` is
the tile `B_k + j·k` of the tiling of `ℤ^d` by translates of `B_k`.
-/
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb MeasureTheory Filter

variable {d : ℕ}

/-! ### Rectangular boxes and their faces -/

/-- The rectangular box `B_k = {x : 1 ≤ x_i ≤ k_i}`. -/
def rbox (k : Fin d → ℕ) : Set (Site d) := {x | ∀ i, 1 ≤ x i ∧ x i ≤ (k i : ℤ)}

/-- The tile `B_k + j·k` of the tiling of `ℤ^d` by translates of `B_k`. -/
def rboxShift (k : Fin d → ℕ) (j : Site d) : Set (Site d) :=
  {x | ∀ i, 1 + (k i : ℤ) * j i ≤ x i ∧ x i ≤ (k i : ℤ) * j i + (k i : ℤ)}

/-- The external face of `B_k + j·k` in direction `i`: the low face when
`hi = false` and the high face when `hi = true`. -/
def faceOut (k : Fin d → ℕ) (j : Site d) (i : Fin d) (hi : Bool) : Set (Site d) :=
  closureN (rboxShift k j) ∩
    {x | x i = if hi then (k i : ℤ) * j i + (k i : ℤ) + 1 else (k i : ℤ) * j i}

/-- The line `L_k^{(i,z)}` across the tile `B_k + j·k` through `z`. -/
def rline (k : Fin d → ℕ) (j : Site d) (i : Fin d) (z : Site d) : Set (Site d) :=
  {x | (1 + (k i : ℤ) * j i ≤ x i ∧ x i ≤ (k i : ℤ) * j i + (k i : ℤ)) ∧ ∀ l, l ≠ i → x l = z l}

/-- `B_k + j·k` can be *crossed* in the direction of the face
`faceOut k j i hi`: firing that face makes the whole tile topple by time
`|B_k|`. -/
def CrossedInDirection (η : Site d → ℤ) (k : Fin d → ℕ) (j : Site d)
    (i : Fin d) (hi : Bool) : Prop :=
  ∀ t : ℕ, (∏ l, k l) ≤ t → ∀ x ∈ rboxShift k j,
    1 ≤ fodo (rboxShift k j)ᶜ η (Set.indicator (faceOut k j i hi) 1) t x

/-- `B_k + j·k` can be crossed in each of the `2d` directions. -/
def BoxCrossed (η : Site d → ℤ) (k : Fin d → ℕ) (j : Site d) : Prop :=
  ∀ (i : Fin d) (hi : Bool), CrossedInDirection η k j i hi

/-- `B_k + j·k` is *strongly box-crossing*: firing any line across it makes the
whole tile topple by time `|B_k|`. -/
def StronglyBoxCrossed (η : Site d → ℤ) (k : Fin d → ℕ) (j : Site d) : Prop :=
  ∀ (i : Fin d) (z : Site d), z ∈ closureN (rboxShift k j) →
    ∀ x ∈ rboxShift k j,
      1 ≤ fodo ((rboxShift k j)ᶜ ∪ rline k j i z) η
        (Set.indicator (rline k j i z) 1) (∏ l, k l) x

/-! ### The five hypotheses of Section 5 -/

/-- **Hypothesis 5.1** (finite range of dependence): the families of coordinates
on two finite sets of sites, every site of one further than `K` from every site
of the other, are independent. -/
def FiniteRangeOfDependence (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∃ K : ℕ, ∀ I J : Finset (Site d), (∀ a ∈ I, ∀ b ∈ J, (K : ℤ) < mnorm (a - b)) →
    ProbabilityTheory.IndepFun (fun η : Site d → ℤ => fun i : I => η i)
      (fun η : Site d → ℤ => fun j : J => η j) P

/-- **Hypothesis 5.2** (box-crossing). -/
def BoxCrossingHyp (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ k : Fin d → ℕ, (∀ i, 0 < k i) ∧
    ∀ j : Site d, ENNReal.ofReal (1 - δ) < P {η | BoxCrossed η k j}

/-- **Hypothesis 5.3** (path-filling): a long path of topplings fills its
bounding rectangle. -/
def PathFillingHyp (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ᵐ η ∂P, ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∀ (m : ℕ) (z : ℕ → Site d),
      Real.log n ^ γ ≤ (m : ℝ) →
      (∀ i, i < m → z i ∈ cent d n) →
      (∀ i j, i < m → j < m → z i = z j → i = j) →
      (∀ i, i + 1 < m → (lattice d).Adj (z i) (z (i + 1))) →
      ∀ t : ℕ, m ^ d ≤ t → ∀ x ∈ br (z '' {i : ℕ | i < m}),
        1 ≤ fodo (z '' {i : ℕ | i < m}) η (Set.indicator (z '' {i : ℕ | i < m}) 1) t x

/-- **Hypothesis 5.4** (strongly box-crossing). -/
def StronglyBoxCrossingHyp (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ k : Fin d → ℕ, (∀ i, 0 < k i) ∧
    ∀ j : Site d, ENNReal.ofReal (1 - δ) < P {η | StronglyBoxCrossed η k j}

/-- **Hypothesis 5.5** (wave-approximation): the last-wave and the exploding
sandpile have arrival times differing by `o(n)` on `[-n,n]^d`. -/
def WaveApproximationHyp (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ᵐ η ∂P, Explosive η →
    (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x ∈ cent d n,
        |((lastArrival η (0 : Site d) x).toNat : ℝ) - ((arrival η x).toNat : ℝ)| ≤ ε * n

/-! ### The setting of Section 5 -/

/-- The state space `Ω` of Section 5: backgrounds with `η_min ≤ η ≤ 2d - 1`.  The
statements that use it take `0 ≤ η_min`, as Section 5 does. -/
def InOmega (d : ℕ) (ηmin : ℤ) (η : Site d → ℤ) : Prop :=
  ∀ x, ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1

/-- `P` is *stationary* with respect to the sublattice `L`. -/
def StationaryOn (d : ℕ) (L : AddSubgroup (Site d)) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ y ∈ L, P.map (fun η : Site d → ℤ => fun z => η (y + z)) = P

/-- `P` is *ergodic* with respect to the sublattice `L`. -/
def ErgodicOn (d : ℕ) (L : AddSubgroup (Site d)) (P : Measure (Site d → ℤ)) : Prop :=
  ∀ E : Set (Site d → ℤ),
    E = ⋂ y ∈ (L : Set (Site d)), (fun η : Site d → ℤ => fun z => η (y + z)) '' E →
      P E = 0 ∨ P E = 1

/-- `P` is *explosive*: almost every background is. -/
def ExplosiveLaw (d : ℕ) (P : Measure (Site d → ℤ)) : Prop := ∀ᵐ η ∂P, Explosive η

/-- `P` is *recurrent*: almost every background is. -/
def RecurrentLaw (d : ℕ) (P : Measure (Site d → ℤ)) : Prop := ∀ᵐ η ∂P, Recurrent η

end Exploding
