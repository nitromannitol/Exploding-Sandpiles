/-
Further discharge of the remaining claims of
`Exploding.Frozen.approximate_subadditive`.  Sorry-free support file.

The first claim settled here is the finiteness of the touched set `P̃ = as_tildeP`
under the standing bound `η ≤ 2d - 1` off the origin.  The point is that the
terminal odometer `as_tildeV η = as_podoTerminal (η + (M-1) δ_0)` is a *podo*
value at a finite time, and off the origin the background is at most `2d - 1`, so
the only initially unstable site is the origin.  A first toppling at a site can
therefore only be triggered by a toppled neighbour, so the support of the
odometer at time `t` is contained in the ball of radius `t`; at the finite
stabilization time that ball is finite, and hence so is the neighbourhood set
`as_tildeP`.  This does not need the frozen `last_penultimate_cluster`.
-/
import Exploding.Support.ASProof
import Exploding.Support.PUBProofF
import Exploding.Support.ASSpecial
import Exploding.Support.PUBProofB
import Exploding.Support.PUBProofC

open Exploding LatticeProb MeasureTheory

set_option linter.unusedVariables false

/-- Topplings cannot outrun the lattice: if off the origin the background is at
most `2d - 1`, then only the origin can be initially unstable, so at time `t`
the odometer is supported in the ball of radius `t`. -/
theorem as3_podo_support_le_time {d : ℕ} (s0 : Site d → ℤ)
    (hhigh : ∀ x, x ≠ 0 → s0 x ≤ 2 * (d : ℤ) - 1) :
    ∀ t : ℕ, ∀ x : Site d, 0 < podo s0 t x → mnorm x ≤ (t : ℤ) := by
  intro t
  induction t with
  | zero => intro x h; simp [podo_zero] at h
  | succ t ih =>
    intro x hx
    by_cases hprev : 0 < podo s0 t x
    · exact le_trans (ih x hprev) (by omega)
    · by_cases hx0 : x = 0
      · subst hx0
        simp [mnorm]
        omega
      · have hxzero : podo s0 t x = 0 := by
          have := as_podo_nonneg s0 t x; omega
        rw [podo_succ] at hx
        by_cases hc : 2 * (d : ℤ) ≤ pconf s0 t x
        · have hnbr : 0 < nbrSumZ (podo s0 t) x := by
            simp only [pconf, lap, hxzero, mul_zero, sub_zero] at hc
            have hs := hhigh x hx0
            omega
          obtain ⟨y, hyx, hypos⟩ := exists_adj_pos_of_nbrSumZ_pos (podo s0 t)
            (fun y => as_podo_nonneg s0 t y) x hnbr
          have hmy : mnorm y ≤ (t : ℤ) := ih y hypos
          have hdist : mnorm x ≤ mnorm y + 1 := by
            have h1 := pub_mnorm_sub_le x y (0 : Site d)
            have h2 := pub_adj_mnorm hyx
            simp only [sub_zero] at h1
            rw [h2] at h1
            linarith
          push_cast
          linarith
        · rw [if_neg hc] at hx
          rw [hxzero] at hx
          simp at hx

/-- The set touched by `as_tildeV` is finite whenever the background is at most
`2d - 1` off the origin. -/
theorem as3_tildeP_finite {d : ℕ} (η : Site d → ℤ)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) : (as_tildeP η).Finite := by
  classical
  set s0 : Site d → ℤ :=
    fun x => η x + ((explosionThreshold η : ℤ) - 1) * dirac (0 : Site d) x with hs0
  have hhigh' : ∀ x, x ≠ 0 → s0 x ≤ 2 * (d : ℤ) - 1 := by
    intro x hx
    rw [hs0]
    simp only [dirac_of_ne hx, mul_zero, add_zero]
    exact hhigh x
  have htilV : as_tildeV η = as_podoTerminal s0 := by
    unfold as_tildeV
    rw [← hs0]
  have hsupp : {y : Site d | 0 < as_tildeV η y}.Finite := by
    by_cases hstab : Stabilizable s0
    · set T : ℕ := sInf {T : ℕ | ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T} with hT
      have hmem : T ∈ {T : ℕ | ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T} :=
        Nat.sInf_mem hstab
      have hterm : as_podoTerminal s0 = podo s0 T := by
        unfold as_podoTerminal
        rw [← hT]
      have hsub : {y : Site d | 0 < as_tildeV η y} ⊆ {y : Site d | mnorm y ≤ (T : ℤ)} := by
        intro y hy
        rw [htilV, hterm] at hy
        exact as3_podo_support_le_time s0 hhigh' T y hy
      refine (as_coord_bdd_finite (0 : Site d) (T : ℝ) _ ?_).subset hsub
      intro y hy i
      have h1 : |y i| ≤ mnorm y := abs_coord_le_mnorm y i
      have h2 : mnorm y ≤ (T : ℤ) := hy
      simp only [Pi.zero_apply, sub_zero]
      exact_mod_cast le_trans h1 h2
    · have hterm : as_podoTerminal s0 = 0 := by
        unfold as_podoTerminal
        have hempty : {T : ℕ | ∀ t : ℕ, T ≤ t → podo s0 t = podo s0 T} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro T hT
          exact hstab ⟨T, hT⟩
        rw [hempty, Nat.sInf_empty]
        rfl
      have heq : as_tildeV η = 0 := by rw [htilV, hterm]
      rw [heq]
      simp
  have hfin2 : ({x : Site d | ∃ y, (lattice d).Adj y x ∧ 0 < as_tildeV η y}).Finite := by
    have hxmem : ∀ {x y : Site d}, (lattice d).Adj y x → x ∈ nbrFinset y := by
      intro x y hyx
      obtain ⟨i, hi | hi⟩ := hyx
      · simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, by simp [hi]⟩
      · have hx : x = y - unit i := by rw [hi]; abel
        simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, by simp [hx]⟩
    have hsub : {x : Site d | ∃ y, (lattice d).Adj y x ∧ 0 < as_tildeV η y} ⊆
        (⋃ y ∈ {y : Site d | 0 < as_tildeV η y}, (↑(nbrFinset y) : Set (Site d))) := by
      rintro x ⟨y, hyx, hypos⟩
      exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hypos, hxmem hyx⟩⟩
    exact (hsupp.biUnion (fun y _ => (nbrFinset y).finite_toSet)).subset hsub
  exact (Set.finite_singleton (0 : Site d)).union hfin2

/-! ### The last wave reaches the touched set -/

open scoped Classical in
/-- For almost every `η`, the last wave reaches every site, hence in particular
the finite set `as_tildeP η` at one common time.  The reach is the quantitative
lemma `pub_penultimate_upper_bound` (Lemma 3.6), and the common time exists
because `as_tildeP η` is finite and bounded. -/
theorem as3_hlastreach (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ c : ℕ, ∀ x ∈ as_tildeP η, 1 ≤ lastWave η (0 : Site d) c x := by
  obtain ⟨γ, C, _hγ, _hC, hae⟩ :=
    pub_penultimate_upper_bound d hd p hp hp1 hLSSB hHole hChem
  filter_upwards [hae, as_eta_bounds d hd p hp hp1] with η hreach hb
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hb x).2
  have hlow0 : ∀ x, 0 ≤ η x := fun x => by linarith [(hb x).1]
  have hfin : (as_tildeP η).Finite := as3_tildeP_finite η hhigh
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have h1 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  obtain ⟨n0, hn0⟩ := hreach
  set B : ℕ := hfin.toFinset.sup (fun x => (mnorm x).toNat) with hB
  set n : ℕ := max n0 B with hn
  have hn0n : n0 ≤ n := le_max_left _ _
  have hmem_bound : ∀ x ∈ as_tildeP η, mnorm x ≤ (n : ℤ) := by
    intro x hx
    have hxB : mnorm x ≤ (B : ℤ) := by
      have h1 : (mnorm x).toNat ≤ B :=
        Finset.le_sup (f := fun x => (mnorm x).toNat) (hfin.mem_toFinset.mpr hx)
      have h2 := pub_mnorm_nonneg x
      rw [← Int.toNat_of_nonneg h2]
      exact_mod_cast h1
    have hBle : (B : ℤ) ≤ (n : ℤ) := by exact_mod_cast le_max_right n0 B
    linarith
  have hex : ∀ x : Site d, x ∈ as_tildeP η →
      ∃ m : ℕ, 1 ≤ m ∧ 0 < lastWave η (0 : Site d) m x := by
    intro x hx
    obtain ⟨m, hm, _⟩ := hn0 n hn0n x (hmem_bound x hx)
    have hla : lastArrival η (0 : Site d) x = (m : ℕ∞) := hm
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have htop : lastArrival η (0 : Site d) x = ⊤ := by
      unfold lastArrival
      exact sInf_coe_top (by rintro ⟨m', hm'⟩; exact hcon m' hm'.1 hm'.2)
    rw [htop] at hla
    exact (by simp : (m : ℕ∞) ≠ ⊤) hla.symm
  let mOf : Site d → ℕ := fun x =>
    if hx : x ∈ as_tildeP η then Classical.choose (hex x hx) else 0
  have hmOf : ∀ x (hx : x ∈ as_tildeP η),
      1 ≤ mOf x ∧ 0 < lastWave η (0 : Site d) (mOf x) x := by
    intro x hx
    simp only [mOf, dif_pos hx]
    exact Classical.choose_spec (hex x hx)
  refine ⟨hfin.toFinset.sup mOf, fun x hx => ?_⟩
  have h1 : mOf x ≤ hfin.toFinset.sup mOf :=
    Finset.le_sup (f := mOf) (hfin.mem_toFinset.mpr hx)
  have h2 : (1 : ℤ) ≤ lastWave η (0 : Site d) (mOf x) x := by
    have hpos := (hmOf x hx).2
    omega
  have h3 : lastWave η (0 : Site d) (mOf x) x ≤
      lastWave η (0 : Site d) (hfin.toFinset.sup mOf) x :=
    wave_mono_time η hlow0 hd0 (waveThreshold η (0 : Site d)) (0 : Site d) h1 x
  linarith

