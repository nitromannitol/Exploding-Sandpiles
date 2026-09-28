/-
Support for Lemma 3.6 of `paper/exploding.tex`: the probability bounds on the
toy law, the macroscopic cube index, and the wave's own mass bound.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubPen

open Exploding LatticeProb MeasureTheory

namespace Exploding

theorem aux_chipLaw_prob (a b : ℤ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (chipLaw a b p) := by
  rw [isProbabilityMeasure_iff, chipLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [Measure.dirac_apply_of_mem (Set.mem_univ a), Measure.dirac_apply_of_mem (Set.mem_univ b)]
  simp only [smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp (by linarith)]
  simp

theorem aux_chipLaw_ae (a b : ℤ) (p : ℝ) : ∀ᵐ v ∂(chipLaw a b p), v = a ∨ v = b := by
  rw [ae_iff]
  have hset : {v : ℤ | ¬(v = a ∨ v = b)} = ({a, b} : Set ℤ)ᶜ := by ext v; simp
  rw [hset, chipLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp [Set.indicator_of_notMem]

theorem aux_toyLaw_eval_ae (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (x : Site d) :
    ∀ᵐ η ∂(toyLaw d p), 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
  haveI : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) :=
    aux_chipLaw_prob _ _ _ (le_of_lt hp) (le_of_lt hp1)
  have hmap : Measure.map (fun η : Site d → ℤ => η x) (toyLaw d p)
      = chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p := by
    rw [toyLaw, productLaw]
    exact Measure.infinitePi_map_eval _ x
  have hf : AEMeasurable (fun η : Site d → ℤ => η x) (toyLaw d p) :=
    (measurable_pi_apply x).aemeasurable
  have hmeas : MeasurableSet {v : ℤ | 2 * (d : ℤ) - 2 ≤ v ∧ v ≤ 2 * (d : ℤ) - 1} := by
    measurability
  rw [← ae_map_iff hf hmeas, hmap]
  filter_upwards [aux_chipLaw_ae (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p] with v hv
  rcases hv with h | h <;> rw [h] <;> omega

theorem aux_pub_reach_eta_bounds (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
  exact ae_all_iff.2 (fun x => aux_toyLaw_eval_ae d p hp hp1 x)


/-! ### (a) the explosion reaches a good cube of the infinite cluster -/

-- Re-examined: `Exploding.Frozen.square_lower_bound` IS fully proven in this
-- repo (`Exploding/Frozen/SquareLowerBound.lean`, 0 `sorry`), so the earlier
-- "not transcribed anywhere" assessment was wrong.  It does not, however,
-- transfer directly: it needs mass `m ≥ (2d)^(dn)` to guarantee reaching
-- `[-n,n]^d`, and `wave_mono_n` (`Exploding/Support/Toppling.lean`) shows the
-- wave is monotone INCREASING in mass, so `Exploding.Frozen.finite_exploding`'s
-- witness `N` (found by making the mass large) says nothing about whether the
-- true last wave — mass `waveThreshold η 0`, which may be far smaller than
-- `N` — also reaches a good cube.  The argument below is mass-independent: it
-- shows any wave that fails to stabilize (in particular the one at
-- `waveThreshold η 0`, which qualifies for free via `Nat.sInf_mem`) cannot
-- have its whole macroscopic footprint confined forever to one finite hole of
-- `C_∞`, since a wave confined to a fixed finite set and bounded above by its
-- own mass must eventually stabilize (elementary: nondecreasing bounded
-- integer sequences on a finite index set become simultaneously constant).

/-- The macroscopic cube index containing the microscopic site `x` at scale
`k ≥ 1`: the unique `i` with `x - k•i ∈ cube d k`. -/
noncomputable def macroIdx {d : ℕ} (k : ℕ) (x : Site d) : Site d :=
  fun i => (x i - 1) / (k : ℤ)

/-- **New.** `x` lies in the cube named by its own macro index: unfolds to
`1 ≤ (x i - 1) % k + 1 ≤ k`, from `Int.ediv_add_emod`, `Int.emod_nonneg` and
`Int.emod_lt_of_pos`. -/
theorem aux_mem_cube_of_macroIdx {d : ℕ} (k : ℕ) (hk : 1 ≤ k) (x : Site d) :
    x - (k : ℤ) • macroIdx k x ∈ cube d k := by
  have hk' : (0 : ℤ) < (k : ℤ) := Nat.cast_pos.mpr hk
  have hne : (k : ℤ) ≠ 0 := ne_of_gt hk'
  simp only [cube, Set.mem_setOf_eq]
  intro i
  have h1 : 0 ≤ (x i - 1) % (k : ℤ) := Int.emod_nonneg _ hne
  have h2 : (x i - 1) % (k : ℤ) < (k : ℤ) := Int.emod_lt_of_pos _ hk'
  have hval : (x - (k : ℤ) • macroIdx k x) i = (x i - 1) % (k : ℤ) + 1 := by
    have h3 := Int.emod_add_ediv_mul (x i - 1) (k : ℤ)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, macroIdx]
    linarith
  rw [hval]
  omega

theorem mem_cube_of_macroIdx {d : ℕ} (k : ℕ) (hk : 1 ≤ k) (x : Site d) :
    x - (k : ℤ) • macroIdx k x ∈ cube d k := by
  exact aux_mem_cube_of_macroIdx k hk x


theorem aux_ediv_le_of_lt_mul (A B n : ℤ) (hB : 0 < B) (h : A < (n + 1) * B) :
    A / B ≤ n := by
  refine Int.le_of_lt_add_one ?_
  rwa [Int.ediv_lt_iff_lt_mul hB]

theorem aux_nbrSumZ_const (d : ℕ) (n : ℤ) (x : Site d) :
    nbrSumZ (fun _ : Site d => n) x = 2 * (d : ℤ) * n := by
  simp only [nbrSumZ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem aux_pub_reach_wave_le_n {d : ℕ} (η : Site d → ℤ)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (n : ℕ) (z : Site d) (t : ℕ) (x : Site d) :
    wave η n z t x ≤ (n : ℤ) := by
  induction t generalizing x with
  | zero =>
    rw [wave_zero]
    by_cases h : x = z
    · rw [if_pos h]
    · rw [if_neg h]
      exact Int.natCast_nonneg n
  | succ t ih =>
    rw [wave_succ]
    by_cases h : x = z
    · rw [if_pos h]
    · rw [if_neg h]
      by_cases hdpos : (0 : ℤ) < 2 * (d : ℤ)
      · refine aux_ediv_le_of_lt_mul (nbrSumZ (wave η n z t) x + η x) (2 * (d : ℤ)) n hdpos ?_
        have h1 := nbrSumZ_mono (fun y => ih y) x
        have h3 := aux_nbrSumZ_const d (n : ℤ) x
        have h2 := hhigh x
        nlinarith [h1, h2, h3]
      · rw [not_lt] at hdpos
        have hd0 : 2 * (d : ℤ) = 0 := le_antisymm hdpos (by positivity)
        rw [hd0, Int.ediv_zero]
        exact Int.natCast_nonneg n


/-- **The backward chase.**  If the wave (mass `n`, centre `0`) is never positive
at a micro site whose macro index lies in `Cinf`, then every micro site it is ever
positive at has its macro index inside `componentIn Cinfᶜ (macroIdx k 0)`. -/
theorem aux_pub_reach_macro_reach {d : ℕ} (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n) (Cinf : Set (Site d))
    (havoid : ∀ t x, 0 < wave η n (0 : Site d) t x → macroIdx k x ∉ Cinf) :
    ∀ t x, 0 < wave η n (0 : Site d) t x →
      macroIdx k x ∈ componentIn Cinfᶜ (macroIdx k (0 : Site d)) := by
  intro t
  induction t with
  | zero =>
    intro x hx
    -- at time `0` only the centre is positive
    have hx0 : x = 0 := by
      by_contra hne
      rw [wave_zero] at hx
      simp [hne] at hx
    subst hx0
    -- `macroIdx k 0 ∈ Cinfᶜ` by `havoid` at time `1`
    have hpos : 0 < wave η n (0 : Site d) 1 (0 : Site d) := by
      rw [wave_at_centre]
      exact_mod_cast hn
    have hnotin : macroIdx k (0 : Site d) ∉ Cinf := havoid 1 _ hpos
    exact ⟨hnotin, hnotin,
      SimpleGraph.Reachable.refl (G := (lattice d).induce Cinfᶜ) ⟨_, hnotin⟩⟩
  | succ t ih =>
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      have hpos : 0 < wave η n (0 : Site d) (t + 1) (0 : Site d) := by
        rw [wave_at_centre]
        exact_mod_cast hn
      have hnotin : macroIdx k (0 : Site d) ∉ Cinf := havoid (t + 1) _ hpos
      exact ⟨hnotin, hnotin,
        SimpleGraph.Reachable.refl (G := (lattice d).induce Cinfᶜ) ⟨_, hnotin⟩⟩
    · -- `x ≠ 0`: either the wave was already positive at `t`, or a neighbour was
      by_cases hprev : 0 < wave η n (0 : Site d) t x
      · exact ih x hprev
      · -- the wave is `0` at `t` and positive at `t+1`, so a neighbour was positive
        have hxnn : 0 ≤ wave η n (0 : Site d) t x := wave_nonneg η hlow n 0 t x
        have hxzero : wave η n (0 : Site d) t x = 0 := by omega
        have hxpos : 0 < wave η n (0 : Site d) (t + 1) x := hx
        rw [wave_of_ne η n (0 : Site d) x t hx0] at hx
        have hsum : 0 < nbrSumZ (wave η n (0 : Site d) t) x := by
          -- `0 < (nbrSumZ + η) / (2d)` gives `2d ≤ nbrSumZ + η`
          have h3 : 2 * (d : ℤ) ≤ nbrSumZ (wave η n (0 : Site d) t) x + η x := by
            -- `0 < (nbrSumZ + η) / (2d)` means the quotient is at least `1`,
            -- so `2d ≤ nbrSumZ + η`
            have h4 : 1 ≤ (nbrSumZ (wave η n (0 : Site d) t) x + η x) / (2 * (d : ℤ)) := by
              omega
            rw [Int.le_ediv_iff_mul_le (by positivity)] at h4
            linarith
          have h1 := hhigh x
          linarith
        obtain ⟨y, hyadj, hypos⟩ := exists_adj_pos_of_nbrSumZ_pos _ (fun y => wave_nonneg η hlow n 0 t y) x hsum
        have hyreach := ih y hypos
        -- `macroIdx k x` is adjacent to `macroIdx k y` or equal to it
        have hxnotin : macroIdx k x ∉ Cinf := havoid (t + 1) x hxpos
        have hynot : macroIdx k y ∉ Cinf := havoid t y hypos
        -- `macroIdx k x` and `macroIdx k y` differ by at most one step
        have hadj : macroIdx k x = macroIdx k y ∨ (lattice d).Adj (macroIdx k x) (macroIdx k y) := by
          -- `y` is `x ± unit i` for some `i`
          obtain ⟨i, hi | hi⟩ := hyadj
          · -- `x = y + unit i`
            have h1 := (macroIdx_adj k hk y i).1
            rw [← hi] at h1
            exact h1
          · -- `y = x + unit i`
            have h1 := (macroIdx_adj k hk x i).1
            rw [← hi] at h1
            exact h1.imp (fun h => h.symm) (fun h => h.symm)
        rcases hadj with heq | hadj'
        · rw [heq]; exact hyreach
        · -- extend the reachability by one edge
          obtain ⟨h0C, hyC, hreach⟩ := hyreach
          have hadj_induce : ((lattice d).induce Cinfᶜ).Adj ⟨macroIdx k y, hyC⟩
              ⟨macroIdx k x, hxnotin⟩ := by
            simpa [SimpleGraph.induce_adj] using hadj'.symm
          exact ⟨h0C, hxnotin, hreach.trans ⟨SimpleGraph.Walk.cons hadj_induce SimpleGraph.Walk.nil⟩⟩

theorem aux_pub_nearest_ray_aux {d : ℕ} (S : Set (Site d)) (x : Site d) (i0 : Fin d) (N : ℕ)
    (hray : ∀ j : ℕ, j ≤ N → x + (j : ℤ) • unit i0 ∈ S) :
    ∀ j : ℕ, ∀ _hj : j ≤ N, ∃ (hx : x ∈ S) (hy : x + (j : ℤ) • unit i0 ∈ S),
      (SimpleGraph.induce S (lattice d)).Reachable ⟨x, hx⟩ ⟨x + (j : ℤ) • unit i0, hy⟩ := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : x + ((0 : ℕ) : ℤ) • unit i0 = x := by simp
    refine ⟨by simpa [h0] using hray 0 (Nat.zero_le N),
      by simpa [h0] using hray 0 (Nat.zero_le N), ?_⟩
    have h1 : (⟨x + ((0 : ℕ) : ℤ) • unit i0, hray 0 (Nat.zero_le N)⟩ : S) =
        ⟨x, by simpa [h0] using hray 0 (Nat.zero_le N)⟩ := Subtype.ext h0
    rw [h1]
  | succ j ih =>
    intro hj
    have hj' : j ≤ N := Nat.le_of_succ_le hj
    obtain ⟨hx', hy', hr⟩ := ih hj'
    have hv : (⟨x + (j : ℤ) • unit i0, hy'⟩ : S) = ⟨x + (j : ℤ) • unit i0, hray j hj'⟩ :=
      Subtype.ext rfl
    rw [hv] at hr
    have hstep : x + ((j + 1 : ℕ) : ℤ) • unit i0 = (x + (j : ℤ) • unit i0) + unit i0 := by
      rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_assoc]
    have hadj : (SimpleGraph.induce S (lattice d)).Adj
        ⟨x + ((j + 1 : ℕ) : ℤ) • unit i0, hray (j + 1) hj⟩
        ⟨x + (j : ℤ) • unit i0, hray j hj'⟩ := by
      rw [SimpleGraph.induce_adj]
      show (lattice d).Adj (x + ((j + 1 : ℕ) : ℤ) • unit i0) (x + (j : ℤ) • unit i0)
      rw [hstep]
      exact adj_add_unit _ _
    exact ⟨hx', hray (j + 1) hj, hr.trans hadj.symm.reachable⟩

theorem aux_pub_nearest_ray {d : ℕ} (S : Set (Site d)) (x : Site d) (i0 : Fin d)
    (N : ℕ) (hray : ∀ j : ℕ, j ≤ N → x + (j : ℤ) • unit i0 ∈ S) :
    ∀ j : ℕ, j ≤ N → x + (j : ℤ) • unit i0 ∈ componentIn S x := by
  intro j hj
  simp only [componentIn]
  exact aux_pub_nearest_ray_aux S x i0 N hray j hj


/-- **New, real (the isoperimetric pigeonhole step).** `N'+1` pairwise distinct
points of a finite set force `N'+1 ≤` its cardinality: the ray map
`j ↦ x + j•unit i0` is injective (`unit_ne_zero`, cancellation in the additive
group `Site d`), so `Finset.image` of `Finset.range (N'+1)` under it has card
`N'+1` (`Finset.card_image_of_injective`, `Finset.card_range`) and is a subset
of `hfin.toFinset` (every ray point lies in `componentIn S x`, whose `hfin`
witnesses finiteness); `Finset.card_le_card` finishes. -/
theorem aux_pub_nearest_pigeonhole {d : ℕ} (S : Set (Site d)) (x : Site d) (i0 : Fin d)
    (hfin : (componentIn S x).Finite) (N' : ℕ)
    (hray : ∀ j : ℕ, j ≤ N' → x + (j : ℤ) • unit i0 ∈ componentIn S x) :
    N' + 1 ≤ hfin.toFinset.card := by
  have huinj : Function.Injective (fun j : ℕ => x + (j : ℤ) • unit i0) := (by
    intro a b hab
    have h' : (a : ℤ) • unit i0 = (b : ℤ) • unit i0 :=
      add_left_cancel (show x + (a : ℤ) • unit i0 = x + (b : ℤ) • unit i0 from hab)
    have h : ((a : ℤ) - (b : ℤ)) • unit i0 = 0 := (by rw [sub_smul, h', sub_self])
    have h2 : (a : ℤ) - (b : ℤ) = 0 := (by
      rcases smul_eq_zero.mp h with hh | hh
      · exact hh
      · exact absurd hh (unit_ne_zero i0))
    have hz : (a : ℤ) = (b : ℤ) := sub_eq_zero.mp h2
    exact_mod_cast hz)
  have hcard : (Finset.image (fun j : ℕ => x + (j : ℤ) • unit i0) (Finset.range (N' + 1))).card
      = N' + 1 := (by
    rw [Finset.card_image_of_injective _ huinj, Finset.card_range])
  have hsub : Finset.image (fun j : ℕ => x + (j : ℤ) • unit i0) (Finset.range (N' + 1))
      ⊆ hfin.toFinset := (by
    intro y hy
    rw [Set.Finite.mem_toFinset]
    obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hy
    rw [← hjy]
    exact hray j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  calc N' + 1 = (Finset.image (fun j : ℕ => x + (j : ℤ) • unit i0) (Finset.range (N' + 1))).card := hcard.symm
    _ ≤ hfin.toFinset.card := Finset.card_le_card hsub


-- GAP (closed by the three lemmas above): turning "the component of `Cinfᶜ`
-- containing `x` (if any) is finite of cardinality `< (log n)^{5/2}`" into
-- "there is `y ∈ Cinf` with `mnorm (x - y)` bounded by the same quantity" is
-- an isoperimetric-type step (a finite subset of `ℤ^d` of cardinality `< V`
end Exploding
