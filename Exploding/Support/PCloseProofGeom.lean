/-
Lattice geometry for the second inequality of Lemma 3.7: boxes with given sides
have the expected cardinality, a set with many points has a long bounding side,
and a path stays within its length of its endpoint.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubBox
import Exploding.Support.PCloseProofPath

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The box `{y : m ≤ y ≤ M}` with prescribed corners. -/
def pcloseBox (m M : Site d) : Set (Site d) := {y | ∀ i, m i ≤ y i ∧ y i ≤ M i}

/-- The box of sup-radius `r` about `c`. -/
def pcloseBall (c : Site d) (r : ℕ) : Set (Site d) := {y | ∀ l, |y l - c l| ≤ (r : ℤ)}

theorem pclose_box_eq_finset (m M : Site d) :
    (pcloseBox m M : Set (Site d)) =
      ↑(Fintype.piFinset fun i => Finset.Icc (m i) (M i)) := by
  ext y
  simp only [pcloseBox, Set.mem_setOf_eq, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]

/-- A box with all sides at most `S` has at most `S^d` points. -/
theorem pclose_box_ncard_le (m M : Site d) (S : ℕ) (h : ∀ i, M i - m i + 1 ≤ (S : ℤ)) :
    (pcloseBox m M).Finite ∧ (pcloseBox m M).ncard ≤ S ^ d := by
  rw [pclose_box_eq_finset]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset, Fintype.card_piFinset]
  calc ∏ i, (Finset.Icc (m i) (M i)).card ≤ ∏ _i : Fin d, S := by
        refine Finset.prod_le_prod' fun i _ => ?_
        rw [Int.card_Icc]
        have := h i
        omega
    _ = S ^ d := by simp

theorem pclose_ball_eq_box (c : Site d) (r : ℕ) :
    pcloseBall c r = pcloseBox (fun l => c l - r) (fun l => c l + r) := by
  ext y
  simp only [pcloseBall, pcloseBox, Set.mem_setOf_eq, abs_le]
  constructor
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]

theorem pclose_ball_ncard_le (c : Site d) (r : ℕ) :
    (pcloseBall c r).Finite ∧ (pcloseBall c r).ncard ≤ (2 * r + 1) ^ d := by
  rw [pclose_ball_eq_box]
  refine pclose_box_ncard_le _ _ _ fun i => ?_
  push_cast
  omega

/-- The bounding rectangle of a subset of a box lies in the box. -/
theorem pclose_br_subset_box (A : Set (Site d)) (m M : Site d)
    (h : A ⊆ pcloseBox m M) : br A ⊆ pcloseBox m M := by
  intro y hy i
  obtain ⟨⟨a, ha, hay⟩, ⟨b, hb, hyb⟩⟩ := hy i
  exact ⟨le_trans (h ha i).1 hay, le_trans hyb (h hb i).2⟩

/-- The bounding rectangle of a subset of a ball lies in the ball. -/
theorem pclose_br_subset_ball (A : Set (Site d)) (c : Site d) (r : ℕ)
    (h : A ⊆ pcloseBall c r) : br A ⊆ pcloseBall c r := by
  rw [pclose_ball_eq_box] at h ⊢
  exact pclose_br_subset_box A _ _ h

/-- A finite set with `S^d` points, `S ≥ 1`, has a bounding side of length at least `S`,
and through every point of the bounding rectangle the segment along that side lies in
the bounding rectangle. -/
theorem pclose_long_side (hd : 1 ≤ d) (A : Set (Site d)) (hA : A.Finite) (hne : A.Nonempty)
    (S : ℕ) (hS : 1 ≤ S) (hcard : S ^ d ≤ A.ncard) :
    ∃ (i : Fin d) (a b : ℤ), (S : ℤ) ≤ b - a + 1 ∧
      ∀ x ∈ br A, ∀ v : ℤ, a ≤ v → v ≤ b → Function.update x i v ∈ br A := by
  obtain ⟨m, M, _, _, hbr⟩ := br_eq_box A hA hne
  have hex : ∃ i, (S : ℤ) ≤ M i - m i + 1 := by
    by_contra hcon
    push Not at hcon
    have hside : ∀ i, M i - m i + 1 ≤ ((S - 1 : ℕ) : ℤ) := by
      intro i
      have := hcon i
      omega
    obtain ⟨hfin, hcardbox⟩ := pclose_box_ncard_le m M (S - 1) hside
    have h1 : A ⊆ pcloseBox m M := by
      intro y hy
      have : y ∈ br A := mem_br_of_mem A hy
      rw [hbr] at this
      exact this
    have h2 : A.ncard ≤ (pcloseBox m M).ncard := Set.ncard_le_ncard h1 hfin
    have h3 : (S - 1) ^ d < S ^ d := Nat.pow_lt_pow_left (by omega) (by omega)
    omega
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, m i, M i, hi, ?_⟩
  intro x hx v hv1 hv2
  rw [hbr] at hx ⊢
  intro l
  by_cases hl : l = i
  · subst hl
    simp only [Function.update_self]
    exact ⟨hv1, hv2⟩
  · simp only [Function.update_of_ne hl]
    exact hx l

/-- Adjacent sites differ by a unit step. -/
theorem pclose_mnorm_of_adj {x y : Site d} (h : (lattice d).Adj x y) : mnorm (y - x) = 1 := by
  obtain ⟨l, hl | hl⟩ := h
  · rw [hl]
    have : x + unit l - x = unit l := by abel
    rw [this, pclose_mnorm_unit]
  · have : y - x = -unit l := by rw [hl]; abel
    rw [this, pclose_mnorm_neg, pclose_mnorm_unit]

/-- Along a path, the Manhattan distance is at most the number of steps. -/
theorem pclose_path_dist (m : ℕ) (z : ℕ → Site d)
    (hadj : ∀ i, i < m → (lattice d).Adj (z i) (z (i + 1))) :
    ∀ a b, a ≤ b → b ≤ m → mnorm (z b - z a) ≤ ((b - a : ℕ) : ℤ) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base =>
    intro _
    simp [mnorm]
  | succ b hab ih =>
    intro hb
    have h1 := ih (by omega)
    have h2 := pclose_mnorm_of_adj (hadj b (by omega))
    have h3 : z (b + 1) - z a = (z (b + 1) - z b) + (z b - z a) := by abel
    have h4 := pclose_mnorm_add_le (z (b + 1) - z b) (z b - z a)
    rw [← h3] at h4
    have h5 : ((b + 1 - a : ℕ) : ℤ) = ((b - a : ℕ) : ℤ) + 1 := by omega
    rw [h5]
    linarith

/-- The last `L + 1` points of a path ending at `x` lie in the ball of radius `L` about `x`. -/
theorem pclose_path_tail_ball (m : ℕ) (z : ℕ → Site d)
    (hadj : ∀ i, i < m → (lattice d).Adj (z i) (z (i + 1))) (L : ℕ) (hL : L ≤ m) :
    (fun j => z (m - L + j)) '' {j : ℕ | j ≤ L} ⊆ pcloseBall (z m) L := by
  rintro y ⟨j, hj, rfl⟩ l
  have h1 := pclose_path_dist m z hadj (m - L + j) m (by simp at hj; omega) le_rfl
  have h2 := pclose_abs_coord_le (z m - z (m - L + j)) l
  have h3 : |z (m - L + j) l - z m l| = |(z m - z (m - L + j)) l| := by
    rw [Pi.sub_apply, abs_sub_comm]
  rw [h3]
  have h4 : ((m - (m - L + j) : ℕ) : ℤ) ≤ (L : ℤ) := by simp at hj; omega
  linarith

/-- The tail of an injective path has `L + 1` points. -/
theorem pclose_path_tail_ncard (m : ℕ) (z : ℕ → Site d)
    (hinj : ∀ i j, i ≤ m → j ≤ m → z i = z j → i = j) (L : ℕ) (hL : L ≤ m) :
    ((fun j => z (m - L + j)) '' {j : ℕ | j ≤ L}).ncard = L + 1 := by
  have hinjOn : Set.InjOn (fun j => z (m - L + j)) {j : ℕ | j ≤ L} := by
    intro i hi j hj hij
    have := hinj (m - L + i) (m - L + j) (by simp at hi; omega) (by simp at hj; omega) hij
    omega
  rw [Set.ncard_image_of_injOn hinjOn]
  have : {j : ℕ | j ≤ L} = ↑(Finset.range (L + 1)) := by
    ext j; simp [Nat.lt_succ_iff]
  rw [this, Set.ncard_coe_finset, Finset.card_range]

end Exploding
