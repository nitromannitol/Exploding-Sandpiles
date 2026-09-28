/-
Support for Lemma 3.6 of `paper/exploding.tex`: the probability bounds on the
toy law, the macroscopic cube index, and the wave's own mass bound.
-/
import Exploding.Support.Vocab
import LatticeProb.Prob.Blocks
import Exploding.Support.SubPen
import Exploding.Frozen.FiniteExploding
import Exploding.Frozen.Renormalization

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
theorem aux_pub_reach_confined_stabilizable {d : ℕ} (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (hd0 : (0 : ℤ) < 2 * (d : ℤ))
    (n : ℕ) (z : Site d) (V : Set (Site d)) (hV : V.Finite)
    (hconf : ∀ t x, x ∉ V → wave η n z t x = 0) :
    WaveStabilizable η n z := by
  have hper : ∀ x : Site d, ∃ Tx : ℕ, ∀ t : ℕ, Tx ≤ t → wave η n z t x = wave η n z Tx x := fun x => by
    obtain ⟨ub, hub, hmax⟩ := Int.exists_greatest_of_bdd
      (P := fun k : ℤ => ∃ t : ℕ, wave η n z t x = k)
      ⟨(n : ℤ), fun k hk => by
        obtain ⟨t, ht⟩ := hk
        rw [← ht]
        exact aux_pub_reach_wave_le_n η hhigh n z t x⟩
      ⟨wave η n z 0 x, 0, rfl⟩
    obtain ⟨Ts, hsT⟩ := hub
    exact ⟨Ts, fun t ht => le_antisymm
      (calc wave η n z t x ≤ ub := hmax _ ⟨t, rfl⟩
        _ = wave η n z Ts x := hsT.symm)
      (wave_mono_time η hlow hd0 n z ht x)⟩
  let T : Site d → ℕ := fun x => Classical.choose (hper x)
  have hT : ∀ x : Site d, ∀ t : ℕ, T x ≤ t → wave η n z t x = wave η n z (T x) x :=
    fun x => Classical.choose_spec (hper x)
  have hsup : ∀ x ∈ hV.toFinset, T x ≤ hV.toFinset.sup T :=
    fun x hx => Finset.le_sup (f := T) hx
  refine ⟨hV.toFinset.sup T, fun t ht => ?_⟩
  funext x
  by_cases hx : x ∈ V
  · have hxfin : x ∈ hV.toFinset := hV.mem_toFinset.mpr hx
    have h1 : T x ≤ t := le_trans (hsup x hxfin) ht
    refine le_antisymm ?_ (wave_mono_time η hlow hd0 n z ht x)
    rw [hT x t h1]
    exact wave_mono_time η hlow hd0 n z (hsup x hxfin) x
  · rw [hconf t x hx, hconf (hV.toFinset.sup T) x hx]


/-- **New, the backward chase.** If the wave (mass `n`, centre `0`) is never
positive at a micro site whose macro index lies in `Cinf`, then every micro
site it is ever positive at has its macro index inside `componentIn Cinfᶜ
(macroIdx k 0)`. Proof: induction on `t`. At `t = 0` only `x = 0` is positive
(`wave_zero`), and `macroIdx k 0 ∈ componentIn Cinfᶜ (macroIdx k 0)` by
reflexivity of `Reachable`, once `macroIdx k 0 ∈ Cinfᶜ` is known from `havoid`
applied at `t := 1`, `x := 0` (`wave_at_centre` gives `wave _ n 0 1 0 = n > 0`).
At `t + 1`: for `x = 0` the same argument applies at every `t`; for `x ≠ 0`
with `wave η n 0 (t+1) x > 0`, either `wave η n 0 t x > 0` already (use the
inductive hypothesis directly) or it is `0`, and unfolding `wave_of_ne` plus
`Int.le_ediv_iff_mul_le` and `hhigh` forces `0 < nbrSumZ (wave η n 0 t) x`,
so `exists_adj_pos_of_nbrSumZ_pos` (`Exploding/Support/Wave.lean`, needs
`wave_nonneg`) gives an adjacent `y` with `wave η n 0 t y > 0`; by the
inductive hypothesis `macroIdx k y ∈ componentIn Cinfᶜ (macroIdx k 0)`, and
`macroIdx_adj` plus `havoid` at `(t+1, x)` (giving `macroIdx k x ∈ Cinfᶜ`)
extend the reachability by one edge (`SimpleGraph.induce_adj`,
`SimpleGraph.Adj.reachable`, `SimpleGraph.Reachable.trans`, exactly the
technique named in `lem-finite-exploding-dec/node.lean`'s
`aux_finite_exploding_box_connected`) to `macroIdx k x`. -/
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

theorem aux_pub_nearest_mnorm_ray {d : ℕ} (x : Site d) (i0 : Fin d) (j : ℕ) :
    mnorm (x - (x + (j : ℤ) • unit i0)) = (j : ℤ) := by
  have hsub : x - (x + (j : ℤ) • unit i0) = -((j : ℤ) • unit i0) := by abel
  rw [hsub, mnorm]
  -- only the `i0`-coordinate is nonzero
  have hcoord : ∀ i : Fin d, |(-((j : ℤ) • unit i0)) i| = if i = i0 then (j : ℤ) else 0 := by
    intro i
    by_cases hi : i = i0
    · subst hi
      simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
        Pi.single_eq_same, if_true]
      rw [abs_neg, abs_of_nonneg (by positivity)]
      ring
    · simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, LatticeProb.unit,
        Pi.single_eq_of_ne hi, mul_zero, neg_zero, if_neg hi, abs_zero]
  rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
  rw [Finset.sum_ite_eq' Finset.univ i0 (fun _ => (j : ℤ))]
  simp

/-- **New, real.** If every point of the ray `x, x+unit i0, …, x+N•unit i0`
lies in `S`, every one of them lies in `LatticeProb.componentIn S x`: induction
on `j` chaining single-step adjacencies (`lattice d`'s `Adj` holds between
`x+j•unit i0` and `x+(j+1)•unit i0` by definition, `⟨i0, Or.inl rfl⟩` up to the
translation) via `SimpleGraph.induce_adj` (`(G.induce s).Adj u v ↔ G.Adj u v`,
`.rfl`), `SimpleGraph.Adj.reachable` and `SimpleGraph.Reachable.trans`, and
unfolding `componentIn`'s existential membership. -/
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
theorem aux_pub_nearest (d : ℕ) (hd : 2 ≤ d) (k0 : ℕ) (η : Site d → ℤ) (Cinf : Set (Site d))
    (_hCinf : IsInfiniteConnectedGoodSet η k0 Cinf) (n0 : ℕ)
    (hhole : ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (n : ℕ) (hn : n0 ≤ n) (x : Site d) (hx : mnorm x ≤ (n : ℤ)) :
    ∃ y : Site d, y ∈ Cinf ∧ (mnorm (x - y) : ℝ) ≤ Real.log n ^ ((5 : ℝ) / 2) := by
  by_cases hxC : x ∈ Cinf
  · refine ⟨x, hxC, ?_⟩
    have hxx : x - x = (0 : Site d) := sub_self x
    have hm0 : mnorm (0 : Site d) = 0 := by simp [mnorm]
    rw [hxx, hm0]
    have hln : 0 ≤ Real.log (n : ℝ) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · simp [h0]
      · exact Real.log_nonneg (by exact_mod_cast hpos)
    simpa using Real.rpow_nonneg hln ((5 : ℝ) / 2)
  · have hxcent : x ∈ (cent d n : Set (Site d)) := by
      intro i
      have h1 : |x i| ≤ mnorm x := by
        rw [mnorm]
        exact Finset.single_le_sum (fun i _ => abs_nonneg (x i)) (Finset.mem_univ i)
      omega
    obtain ⟨hfin, hcard⟩ := hhole n hn x hxcent hxC
    set N := hfin.toFinset.card with hNdef
    have hcard' : (N : ℝ) < Real.log n ^ ((5 : ℝ) / 2) := by
      rw [hNdef, ← Set.ncard_eq_toFinset_card (componentIn Cinfᶜ x) hfin]
      exact hcard
    by_contra hcon
    push Not at hcon
    have hi0 : (0 : ℕ) < d := by omega
    have hray : ∀ j : ℕ, j ≤ N → x + (j : ℤ) • unit (⟨0, hi0⟩ : Fin d) ∈ Cinfᶜ := by
      intro j hj
      by_contra hmemC
      simp only [Set.mem_compl_iff, not_not] at hmemC
      have hb := hcon _ hmemC
      rw [aux_pub_nearest_mnorm_ray x ⟨0, hi0⟩ j] at hb
      have hjR : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
      have hcast : ((j : ℤ) : ℝ) = (j : ℝ) := by push_cast; ring
      rw [hcast] at hb
      linarith [hb]
    have hraycomp := aux_pub_nearest_ray Cinfᶜ x (⟨0, hi0⟩ : Fin d) N hray
    have hpig := aux_pub_nearest_pigeonhole Cinfᶜ x (⟨0, hi0⟩ : Fin d) hfin N hraycomp
    omega


theorem aux_pub_reach_preimage_finite {d : ℕ} (k : ℕ) (hk : 1 ≤ k) (M : Set (Site d))
    (hM : M.Finite) : {x : Site d | macroIdx k x ∈ M}.Finite := by
  have hfin : (⋃ p ∈ M, {x : Site d | macroIdx k x = p}).Finite :=
    Set.Finite.biUnion (s := M) hM
      (t := fun p : Site d => {x : Site d | macroIdx k x = p})
      (fun p _ => Set.Finite.subset
        (Set.Finite.pi (t := fun j : Fin d => Set.Icc ((k : ℤ) * p j + 1) ((k : ℤ) * p j + (k : ℤ)))
          (fun j => Set.finite_Icc _ _))
        (fun x hx => by
          rw [Set.mem_pi]
          intro j _
          rw [Set.mem_Icc]
          have hq : (x j - 1) / (k : ℤ) = p j := congrFun hx j
          have hh := Int.emod_add_mul_ediv (x j - 1) (k : ℤ)
          rw [hq] at hh
          have hr0 := Int.emod_nonneg (x j - 1) (by omega : (k : ℤ) ≠ 0)
          have hr1 := Int.emod_lt_of_pos (x j - 1) (by omega : (0 : ℤ) < (k : ℤ))
          constructor <;> linarith))
  refine hfin.subset ?_
  intro x hx
  rw [Set.mem_iUnion]
  exact ⟨macroIdx k x, by rw [Set.mem_iUnion]; exact ⟨hx, rfl⟩⟩


/-- On the a.s. event of `renormalization_properties`, the last wave at the
origin reaches some site of the infinite good-cube cluster within a constant
(`η`-dependent) number of steps.  Restated (this lemma is not itself
FROZEN) to name a witness point `x0` of the good cube rather than insisting on
its scaled corner `k0•z`: getting from "some point of `Q_{k0}(z)` is touched"
to "the corner `k0•z` is touched" needs the same crossing-time/domino
machinery as `aux_pub_far` below, and `aux_pub_near`/`aux_pub_far`/
`aux_pub_core` compose just as well from this shape. -/
theorem aux_pub_reach (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree) (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ k0 : ℕ, 1 ≤ k0 ∧ ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k0 Cinf ∧
      ∃ Cη : ℕ, 1 ≤ Cη ∧ ∃ z : Site d, z ∈ Cinf ∧ ∃ x0 : Site d, x0 ∈ cube d k0 ∧
        lastArrival η (0 : Site d) (x0 + (k0 : ℤ) • z) ≤ (Cη : ℕ∞) := by
  have hd2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by linarith
  obtain ⟨kb, hkb⟩ := Exploding.Frozen.renormalization_properties d hd p hp hp1 hLSSB hHole hChem
  set k0 := max kb 1 with hk0def
  have hk0 : 1 ≤ k0 := le_max_right kb 1
  obtain ⟨c, Cr, hc, hCr, hae⟩ := hkb k0 (le_max_left kb 1)
  filter_upwards [hae, aux_pub_reach_eta_bounds d p hp hp1,
      Exploding.Frozen.finite_exploding d hd p hp hp1 hLSSB hHole hChem] with η hη hetabd hexplode
  obtain ⟨Cinf, hCinf, ⟨n0, hn0⟩, -⟩ := hη
  have hlow : ∀ x, 0 ≤ η x := fun x => by linarith [(hetabd x).1]
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hetabd x).2
  have hMmem := Nat.sInf_mem hexplode
  set n := waveThreshold η (0 : Site d) with hndef
  have hn1 : 1 ≤ n := hMmem.1
  have hnstab : ¬ WaveStabilizable η n (0 : Site d) := hMmem.2
  set i0 := macroIdx k0 (0 : Site d) with hi0def
  have hexists : ∃ t x, 0 < wave η n (0 : Site d) t x ∧ macroIdx k0 x ∈ Cinf := by
    by_contra hnone
    push Not at hnone
    have hi0pos : (0 : ℤ) < wave η n (0 : Site d) 1 (0 : Site d) := by
      rw [wave_at_centre]; exact_mod_cast hn1
    have hi0notin : i0 ∉ Cinf := hnone 1 (0 : Site d) hi0pos
    have hi0nn : 0 ≤ mnorm i0 := Finset.sum_nonneg fun l _ => abs_nonneg (i0 l)
    have hi0cast : ((mnorm i0).toNat : ℤ) = mnorm i0 := Int.toNat_of_nonneg hi0nn
    set N1 := max n0 (mnorm i0).toNat with hN1def
    have hN1n0 : n0 ≤ N1 := le_max_left _ _
    have hi0cent : i0 ∈ (cent d N1 : Set (Site d)) := by
      intro l
      have h1 : |i0 l| ≤ mnorm i0 := Finset.single_le_sum (fun j _ => abs_nonneg (i0 j)) (Finset.mem_univ l)
      have h2 : mnorm i0 ≤ (N1 : ℤ) := by
        rw [← hi0cast]; exact_mod_cast le_max_right n0 (mnorm i0).toNat
      linarith
    obtain ⟨hfin, -⟩ := hn0 N1 hN1n0 i0 hi0cent hi0notin
    apply hnstab
    apply aux_pub_reach_confined_stabilizable η hlow hhigh hd0 n (0 : Site d)
      {x : Site d | macroIdx k0 x ∈ componentIn Cinfᶜ i0}
      (aux_pub_reach_preimage_finite k0 hk0 _ hfin)
    intro t x hxV
    by_contra hxpos
    have hxpos' : 0 < wave η n (0 : Site d) t x :=
      lt_of_le_of_ne (wave_nonneg η hlow n 0 t x) (Ne.symm hxpos)
    exact hxV (aux_pub_reach_macro_reach η hlow hhigh hd0 k0 hk0 n hn1 Cinf hnone t x hxpos')
  obtain ⟨t, x, htx, hxCinf⟩ := hexists
  refine ⟨k0, hk0, Cinf, hCinf, max t 1, le_max_right t 1, macroIdx k0 x, hxCinf,
    x - (k0 : ℤ) • macroIdx k0 x, mem_cube_of_macroIdx k0 hk0 x, ?_⟩
  have heq : x - (k0 : ℤ) • macroIdx k0 x + (k0 : ℤ) • macroIdx k0 x = x := by abel
  rw [heq]
  have hmono := wave_mono_time η hlow hd0 n (0 : Site d) (le_max_left t 1) x
  have hpos : 0 < wave η n (0 : Site d) (max t 1) x := lt_of_lt_of_le htx hmono
  apply sInf_le
  refine ⟨max t 1, rfl, le_max_right t 1, ?_⟩
  show 0 < lastWave η (0 : Site d) (max t 1) x
  rw [lastWave, ← hndef]
  exact hpos

/-! ### (b) every site has a nearby good cube -/


/-- **Translation invariance of the toy law.**  Shifting the background by a
lattice vector preserves its law. -/
theorem toyLaw_shift (d : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (x : Site d) :
    (toyLaw d p).map (fun η : Site d → ℤ => fun z => η (z + x)) = toyLaw d p := by
  have hpos_p : (0 : ℝ) ≤ p := by linarith
  have hle_p : (0 : ℝ) ≤ 1 - p := by linarith
  haveI hprob : IsProbabilityMeasure (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p) := by
    constructor
    simp only [chipLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply',
      MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hpos_p hle_p]
    norm_num
  have hinj : Function.Injective (fun k : Site d => k + x) := by
    intro a b h
    funext i
    have h4 := congrFun h i
    simpa using h4
  have h2 : (Measure.infinitePi fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p).map
      (fun ω : Site d → ℤ => fun k : Site d => ω (k + x)) =
      Measure.infinitePi fun _ : Site d => chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p :=
    LatticeProb.infinitePi_map_comp' (chipLaw (2 * (d : ℤ) - 1) (2 * (d : ℤ) - 2) p)
      (fun k : Site d => k + x) hinj
  simpa only [toyLaw, productLaw] using h2


/-- **The wave is equivariant under translation.**  Shifting the background by
`x` and the starting site by `-x` shifts the wave by `-x`. -/
theorem wave_shift_eq {d : ℕ} (η : Site d → ℤ) (n : ℕ) (z x : Site d) (t : ℕ) :
    ∀ y : Site d, wave (fun w => η (w + x)) n (z - x) t (y - x) = wave η n z t y := by
  induction t with
  | zero =>
    intro y
    rw [wave_zero, wave_zero]
    by_cases h : y = z
    · subst h; simp
    · have h2 : y - x ≠ z - x := by
        intro hc
        apply h
        have h5 := congrFun hc
        exact funext fun i => by
          have h6 := h5 i
          simp only [Pi.sub_apply] at h6
          omega
      simp [h, h2]
  | succ t ih =>
    intro y
    rw [wave_succ, wave_succ]
    by_cases h : y = z
    · subst h; simp
    · have h2 : y - x ≠ z - x := by
        intro hc
        apply h
        have h5 := congrFun hc
        exact funext fun i => by
          have h6 := h5 i
          simp only [Pi.sub_apply] at h6
          omega
      rw [if_neg h, if_neg h2]
      congr 1
      have h3 : nbrSumZ (fun w => wave (fun w => η (w + x)) n (z - x) t w) (y - x) =
          nbrSumZ (fun w => wave η n z t w) y := by
        apply Finset.sum_congr rfl
        intro i _
        have h4 : y - x + unit i = (y + unit i) - x := by abel
        have h5 : y - x - unit i = (y - unit i) - x := by abel
        simp only [h4, h5]
        rw [ih (y + unit i), ih (y - unit i)]
      rw [h3]
      congr 1
      rw [show y - x + x = y by abel]


/-- **The wave is measurable in the background.** -/
theorem measurable_wave {d : ℕ} (n : ℕ) (z : Site d) (t : ℕ) :
    ∀ y : Site d, Measurable fun η : Site d → ℤ => wave η n z t y := by
  induction t with
  | zero =>
    intro y
    simp only [wave_zero]
    split <;> exact measurable_const
  | succ t ih =>
    intro y
    rw [funext fun η => wave_succ η n z y t]
    split
    · exact measurable_const
    · apply Measurable.div
      · apply Measurable.add
        · apply Finset.measurable_sum
          intro i _
          exact (ih (y + unit i)).add (ih (y - unit i))
        · exact measurable_pi_apply y
      · exact measurable_const


/-- **The set of backgrounds where the `n`-wave at `z` does not stabilize is
measurable.** -/
theorem measurableSet_not_stabilizable {d : ℕ} (n : ℕ) (z : Site d) :
    MeasurableSet {a : Site d → ℤ | ¬ WaveStabilizable a n z} := by
  have h : {a : Site d → ℤ | ¬ WaveStabilizable a n z} =
      (⋃ T : ℕ, ⋂ t : ℕ, ⋂ (_ : T ≤ t), {a : Site d → ℤ | wave a n z t = wave a n z T})ᶜ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_iInter,
      WaveStabilizable, not_exists, not_forall]
  rw [h]
  refine MeasurableSet.compl ?_
  refine MeasurableSet.iUnion fun T => ?_
  refine MeasurableSet.iInter fun t => ?_
  refine MeasurableSet.iInter fun ht => ?_
  exact measurableSet_eq_fun (measurable_pi_lambda _ fun y => measurable_wave n z t y)
    (measurable_pi_lambda _ fun y => measurable_wave n z T y)


/-- **The last wave is well defined at every site.**  The sealed node
`Exploding.Frozen.finite_exploding` gives this at the origin; the translation
invariance of the toy law and the wave's equivariance transfer it to every `x`. -/
theorem finite_exploding_at (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n x := by
  have h0 := Exploding.Frozen.finite_exploding d hd p hp hp1 hLSSB hHole hChem
  have hshift : ∀ x : Site d, ∀ᵐ η ∂(toyLaw d p),
      ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n x := by
    intro x
    have h1 : ∀ᵐ η ∂((toyLaw d p).map (fun η : Site d → ℤ => fun z => η (z + x))),
        ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d) := by
      rw [toyLaw_shift d p hp hp1 x]
      exact h0
    rw [MeasureTheory.ae_map_iff] at h1
    · rw [MeasureTheory.ae_iff] at h1
      rw [MeasureTheory.ae_iff]
      have h3 : {a : Site d → ℤ | ¬ ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable (fun z => a (z + x)) n (0 : Site d)} =
          {a : Site d → ℤ | ¬ ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable a n x} := by
        ext a
        simp only [Set.mem_setOf_eq]
        constructor
        · intro hc ⟨n, hn, hns⟩
          refine hc ⟨n, hn, fun hstab => hns ?_⟩
          obtain ⟨T, hT⟩ := hstab
          refine ⟨T, fun t ht => ?_⟩
          funext y
          have h4 := congrFun (hT t ht) (y - x)
          have h5 := wave_shift_eq a n x x t y
          have h6 := wave_shift_eq a n x x T y
          simp only [sub_self] at h5 h6
          rw [h5, h6] at h4
          simpa using h4
        · intro hc ⟨n, hn, hns⟩
          refine hc ⟨n, hn, fun hstab => hns ?_⟩
          obtain ⟨T, hT⟩ := hstab
          refine ⟨T, fun t ht => ?_⟩
          funext y
          have h4 := congrFun (hT t ht) (y + x)
          rw [← wave_shift_eq a n x x t (y + x), ← wave_shift_eq a n x x T (y + x)] at h4
          simpa using h4
      rw [h3] at h1
      exact h1
    · exact (measurable_pi_lambda _ fun z => measurable_pi_apply (z + x)).aemeasurable
    · have h : MeasurableSet (⋃ n : ℕ, {a : Site d → ℤ |
          (1 ≤ n ∧ ¬ WaveStabilizable a n (0 : Site d))}) :=
        MeasurableSet.iUnion fun n =>
          (measurableSet_le (f := fun _ : Site d → ℤ => (1 : ℕ)) measurable_const
            measurable_const).inter (measurableSet_not_stabilizable n (0 : Site d))
      rw [show {a : Site d → ℤ | ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable a n (0 : Site d)} =
          ⋃ n : ℕ, {a : Site d → ℤ | (1 ≤ n ∧ ¬ WaveStabilizable a n (0 : Site d))} from by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]]
      exact h
  exact (MeasureTheory.ae_all_iff).mpr hshift


/-- **The first inequality of Lemma 3.7.**  The last-wave arrival time is at most
the penultimate-cluster arrival time, since the penultimate cluster contains the
site. -/
theorem lastArrival_le_clusterArrival {d : ℕ} (η : Site d → ℤ) (y x : Site d) :
    lastArrival η y x ≤ clusterArrival η y x := by
  refine le_sInf ?_
  rintro t ⟨n, ht_eq, hn, ht⟩
  rw [ht_eq]
  exact lastArrival_le η y x n hn (ht x (by
    exact Set.mem_union_left _ rfl))

