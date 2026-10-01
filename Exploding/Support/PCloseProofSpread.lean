/-
The spreading step of the second inequality of Lemma 3.7: once a good cube of the
infinite cluster near `x` has fired, the wave is positive on every site within a
prescribed distance of `x` after polynomially many further steps.  The wave reaches,
through the infinite cluster, two far cubes on either side of `x`, and the path through
their corners fills the bounding rectangle, which contains the prescribed box by local
convexity.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubPub
import Exploding.Support.PCloseProofPath
import Exploding.Support.PCloseProofGeom
import Exploding.Support.PCloseProofCube
import Exploding.Support.PCloseProofWalk
import Exploding.Support.PCloseProofMacro

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The bound on the length of a chemical walk from `Q` to a far point. -/
def pcloseW (d Cc Z Δ : ℕ) : ℕ := Cc * (d * ((Δ + Z) + Z) + Δ)

/-- The radius of the box containing the path through the corners. -/
def pcloseR2 (d k Cc Z Δ : ℕ) : ℕ := k * (pcloseW d Cc Z Δ + Δ) + 2 * k

/-- **The spreading step.**  If the good cube `Q_k(Q)`, `Q` in the infinite cluster and
within macroscopic distance `Δ` of the macroscopic index of `x`, has fired by time `T2`,
then the wave is positive on the box of radius `R ≤ Z` about `x` by time
`T2 + W k^d + (2 R2 + 1)^d`. -/
theorem pclose_spread (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : 1 ≤ k) (Cinf : Set (Site d))
    (hgood : ∀ j ∈ Cinf, GoodAt η k j)
    (Z n1 Cc R : ℕ) (hRZ : R ≤ Z)
    (hhole : ∀ y ∈ (cent d n1 : Set (Site d)), y ∉ Cinf →
      (componentIn Cinfᶜ y).Finite ∧ (componentIn Cinfᶜ y).ncard < Z)
    (hchem : ∀ y ∈ Cinf, ∀ y' ∈ Cinf, mnorm y ≤ (n1 : ℤ) → (Z : ℤ) ≤ mnorm (y - y') →
      ∃ m : ℕ, chemDist Cinf y y' = (m : ℕ∞) ∧ (m : ℤ) ≤ (Cc : ℤ) * mnorm (y - y'))
    (x Q : Site d) (hQ : Q ∈ Cinf) (Δ : ℕ) (hΔ1 : 1 ≤ Δ)
    (hΔ : mnorm (Q - macroIdx k x) ≤ (Δ : ℤ))
    (T2 : ℕ) (hfired : PCloseFired η N k 0 T2 Q)
    (hn1 : mnorm x + (((Δ + Z) + Z + d + 1 : ℕ) : ℤ) ≤ (n1 : ℤ)) :
    ∀ w : Site d, (∀ l, |w l - x l| ≤ (R : ℤ)) →
      0 < wave η N 0 (T2 + pcloseW d Cc Z Δ * k ^ d + (2 * pcloseR2 d k Cc Z Δ + 1) ^ d) w := by
  intro w hw
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  have hη0 : ∀ y, 0 ≤ η y := fun y => by linarith [hlow y]
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  set mac := macroIdx k x with hmac
  set ρ : ℕ := Δ + Z with hρ
  set W := pcloseW d Cc Z Δ with hW
  have hZ0 : (0 : ℤ) ≤ (Z : ℤ) := Int.natCast_nonneg Z
  have hΔ0 : (1 : ℤ) ≤ (Δ : ℤ) := by exact_mod_cast hΔ1
  -- the two far points
  have hcent : ∀ l, |mac l| + ρ + Z ≤ (n1 : ℤ) := by
    intro l
    have h1 := pclose_macro_abs k hk x l
    have h2 := pclose_abs_coord_le x l
    have h3 : (ρ : ℤ) = Δ + Z := by rw [hρ]; push_cast; ring
    push_cast at hn1
    linarith
  obtain ⟨⟨Mp, hMp, hMpc⟩, ⟨Mm, hMm, hMmc⟩⟩ := pclose_two_ends hd1 Cinf Z n1 hhole mac ρ hcent
  have hQn : mnorm Q ≤ (n1 : ℤ) := by
    have h1 : Q = (Q - mac) + mac := by abel
    have h2 := pclose_mnorm_add_le (Q - mac) mac
    rw [← h1] at h2
    have h3 := pclose_mnorm_macro_le k hk x
    push_cast at hn1
    have h4 : (0 : ℤ) ≤ ρ := Int.natCast_nonneg ρ
    have h5 : (ρ : ℤ) = Δ + Z := by rw [hρ]; push_cast; ring
    linarith
  obtain ⟨hZp, hupp⟩ := pclose_far_norm hd1 Q mac Mp Δ Z ρ hρ hΔ (Or.inl hMpc)
  obtain ⟨hZm, hupm⟩ := pclose_far_norm hd1 Q mac Mm Δ Z ρ hρ hΔ (Or.inr hMmc)
  -- the two chemical walks
  have hWdef : ((W : ℕ) : ℤ) = (Cc : ℤ) * ((d : ℤ) * ((ρ : ℤ) + Z) + Δ) := by
    rw [hW, pcloseW, hρ]; push_cast; ring
  obtain ⟨m₁, hm₁, hm₁le⟩ := hchem Q hQ Mp hMp hQn hZp
  obtain ⟨m₂, hm₂, hm₂le⟩ := hchem Q hQ Mm hMm hQn hZm
  have hm₁W : m₁ ≤ W := by
    have h1 : (m₁ : ℤ) ≤ (W : ℤ) := by
      rw [hWdef]
      have hCc : (0 : ℤ) ≤ Cc := Int.natCast_nonneg Cc
      calc (m₁ : ℤ) ≤ (Cc : ℤ) * mnorm (Q - Mp) := hm₁le
        _ ≤ (Cc : ℤ) * ((d : ℤ) * ((ρ : ℤ) + Z) + Δ) := mul_le_mul_of_nonneg_left hupp hCc
    exact_mod_cast h1
  have hm₂W : m₂ ≤ W := by
    have h1 : (m₂ : ℤ) ≤ (W : ℤ) := by
      rw [hWdef]
      have hCc : (0 : ℤ) ≤ Cc := Int.natCast_nonneg Cc
      calc (m₂ : ℤ) ≤ (Cc : ℤ) * mnorm (Q - Mm) := hm₂le
        _ ≤ (Cc : ℤ) * ((d : ℤ) * ((ρ : ℤ) + Z) + Δ) := mul_le_mul_of_nonneg_left hupm hCc
    exact_mod_cast h1
  obtain ⟨c₁, hc₁0, hc₁m, hc₁S, hc₁adj⟩ := pclose_chem_walk Cinf Q Mp m₁ hm₁
  obtain ⟨c₂, hc₂0, hc₂m, hc₂S, hc₂adj⟩ := pclose_chem_walk Cinf Q Mm m₂ hm₂
  -- the cubes along the walks fire
  have hfire₁ := pclose_walk_fires hd η hη0 hhigh N k hN hk 0 m₁ c₁
    (fun s hs => hgood _ (hc₁S s hs)) hc₁adj T2 (by rw [hc₁0]; exact hfired)
  have hfire₂ := pclose_walk_fires hd η hη0 hhigh N k hN hk 0 m₂ c₂
    (fun s hs => hgood _ (hc₂S s hs)) hc₂adj T2 (by rw [hc₂0]; exact hfired)
  set T3 := T2 + W * k ^ d with hT3
  have hfired₁ : ∀ s, s ≤ m₁ → PCloseFired η N k 0 T3 (c₁ s) := fun s hs =>
    pclose_fired_mono hd0 η hη0 N k 0
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (le_trans hs hm₁W)) T2) (hfire₁ s hs)
  have hfired₂ : ∀ s, s ≤ m₂ → PCloseFired η N k 0 T3 (c₂ s) := fun s hs =>
    pclose_fired_mono hd0 η hη0 N k 0
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (le_trans hs hm₂W)) T2) (hfire₂ s hs)
  -- the distance of the walks from `Q`
  have hdist₁ : ∀ s, s ≤ m₁ → mnorm (c₁ s - Q) ≤ (W : ℤ) := by
    intro s hs
    have := pclose_path_dist m₁ c₁ hc₁adj 0 s (Nat.zero_le s) hs
    rw [hc₁0] at this
    have h2 : ((s - 0 : ℕ) : ℤ) ≤ (W : ℤ) := by
      have : s ≤ W := le_trans hs hm₁W
      simp only [Nat.sub_zero]; exact_mod_cast this
    linarith
  have hdist₂ : ∀ s, s ≤ m₂ → mnorm (c₂ s - Q) ≤ (W : ℤ) := by
    intro s hs
    have := pclose_path_dist m₂ c₂ hc₂adj 0 s (Nat.zero_le s) hs
    rw [hc₂0] at this
    have h2 : ((s - 0 : ℕ) : ℤ) ≤ (W : ℤ) := by
      have : s ≤ W := le_trans hs hm₂W
      simp only [Nat.sub_zero]; exact_mod_cast this
    linarith
  -- the concatenated walk from `Mp` to `Mm`
  obtain ⟨c, hc0, hcend, hcadj, hcmem⟩ :=
    pclose_concat_walk m₁ m₂ c₁ c₂ (by rw [hc₁0, hc₂0]) hc₁adj hc₂adj
  have hcfired : ∀ s, s ≤ m₁ + m₂ → PCloseFired η N k 0 T3 (c s) ∧
      mnorm (c s - Q) ≤ (W : ℤ) := by
    intro s hs
    rcases hcmem s hs with ⟨s', hs', he⟩ | ⟨s', hs', he⟩
    · rw [he]; exact ⟨hfired₁ s' hs', hdist₁ s' hs'⟩
    · rw [he]; exact ⟨hfired₂ s' hs', hdist₂ s' hs'⟩
  -- the microscopic path through the corners
  obtain ⟨L2, z, hL2, hz0, hzL, hzadj, hzmem⟩ := pclose_corner_path k hk c (m₁ + m₂) hcadj
  have hzpos : ∀ q, q ≤ L2 → 0 < wave η N 0 T3 (z q) := by
    intro q hq
    obtain ⟨s, hs, hmem⟩ := hzmem q hq
    have h := (hcfired s hs).1 _ hmem
    have he : z q - (k : ℤ) • c s + (k : ℤ) • c s = z q := by abel
    rwa [he] at h
  -- the path lies in a box about `x`
  set R2 := pcloseR2 d k Cc Z Δ with hR2
  have hball : (z '' {q : ℕ | q ≤ L2}) ⊆ pcloseBall x R2 := by
    rintro y ⟨q, hq, rfl⟩ l
    obtain ⟨s, hs, hmem⟩ := hzmem q hq
    obtain ⟨hcs, hcd⟩ := hcfired s hs
    have hy0 := hmem l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hy0
    have hxm := pclose_macro_bounds k hk x l
    have hcl : |c s l - mac l| ≤ (W : ℤ) + Δ := by
      have h1 : c s - mac = (c s - Q) + (Q - mac) := by abel
      have h2 := pclose_mnorm_add_le (c s - Q) (Q - mac)
      rw [← h1] at h2
      have h3 := pclose_abs_coord_le (c s - mac) l
      simp only [Pi.sub_apply] at h3
      linarith
    have hbd : |(k : ℤ) * (c s l - mac l)| ≤ (k : ℤ) * ((W : ℤ) + Δ) := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℤ) ≤ k)]
      exact mul_le_mul_of_nonneg_left hcl (by linarith)
    have hR2def : (R2 : ℤ) = (k : ℤ) * ((W : ℤ) + Δ) + 2 * k := by
      rw [hR2, pcloseR2]; push_cast; ring
    rw [abs_le] at hbd ⊢
    constructor <;> linarith [hbd.1, hbd.2, hy0.1, hy0.2, hxm.1, hxm.2]
  have hfin : (br (z '' {q : ℕ | q ≤ L2})).Finite :=
    br_finite _ (Set.Finite.image _ (Set.finite_Iic L2))
  have hcardbr : hfin.toFinset.card ≤ (2 * R2 + 1) ^ d := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    have hsub := pclose_br_subset_ball _ x R2 hball
    obtain ⟨hbf, hbc⟩ := pclose_ball_ncard_le x R2
    exact le_trans (Set.ncard_le_ncard hsub hbf) hbc
  have hfill := pclose_fill hd η hlow hhigh N hN 0 L2 z hzadj T3 hzpos hfin _ hcardbr
  -- the box about `x` lies in the bounding rectangle of the path
  have hwmem : w ∈ br (z '' {q : ℕ | q ≤ L2}) := by
    have hzmemA : pcloseCorner k Mp ∈ z '' {q : ℕ | q ≤ L2} := by
      refine ⟨0, show 0 ≤ L2 from Nat.zero_le _, ?_⟩
      rw [hz0, hc0, hc₁m]
    have hzmemB : pcloseCorner k Mm ∈ z '' {q : ℕ | q ≤ L2} := by
      refine ⟨L2, show L2 ≤ L2 from le_rfl, ?_⟩
      rw [hzL, hcend, hc₂m]
    intro l
    have hxm := pclose_macro_bounds k hk x l
    have hwl := hw l
    rw [abs_le] at hwl
    have hp := hMpc l
    have hm := hMmc l
    have hkρ : (k : ℤ) * (ρ : ℤ) ≥ (R : ℤ) + k := by
      have h1 : (ρ : ℤ) ≥ (R : ℤ) + 1 := by
        have : (R : ℤ) ≤ Z := by exact_mod_cast hRZ
        rw [hρ]; push_cast; linarith
      have h2 : (R : ℤ) ≥ 0 := Int.natCast_nonneg R
      have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℤ) ≤ k)
      have h4 : (k : ℤ) * R ≥ R := by
        have := mul_le_mul_of_nonneg_right hk1 h2
        linarith
      linarith
    have hp' := mul_le_mul_of_nonneg_left hp.1 (by linarith : (0 : ℤ) ≤ k)
    have hm' := mul_le_mul_of_nonneg_left hm.2 (by linarith : (0 : ℤ) ≤ k)
    constructor
    · refine ⟨pcloseCorner k Mm, hzmemB, ?_⟩
      show (k : ℤ) * Mm l + 1 ≤ w l
      linarith [hm', hxm.1, hwl.1, hkρ]
    · refine ⟨pcloseCorner k Mp, hzmemA, ?_⟩
      show w l ≤ (k : ℤ) * Mp l + 1
      linarith [hp', hxm.2, hwl.2, hkρ]
  exact hfill w hwmem

end Exploding
