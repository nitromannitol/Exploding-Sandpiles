/-
Step 4 of `theorem:counterexample` of `paper/corrected-arxiv/exploding-corrected-arxiv.tex`
(`exploding-corrected-arxiv.tex:1640-1867`): the pulsating front of the reflected-cylinder
counterexample.

This file isolates the *finite computation*.  On the cylinder with the modified
background `ζ'`, the capped last-wave odometer started from the displayed
`{0,1}` initial condition advances by `8` columns every `12` steps.  We encode a
finite time slice as a `List Bool` (the site `(x,y)` is at index `4*x+y`), give a
computable one-step map, prove that it is local — the value at column `x` at
`t+1` depends only on columns `x-1, x, x+1` at `t` — and check the `12`-step
period by kernel `decide` on the finite table.
-/
import Exploding.Support.CEProof

namespace Exploding

/-! ### The modified cylinder background `ζ'` -/

/-- The value `ζ'(x,y)` of the modified cylinder background of
`exploding-corrected-arxiv.tex:1610-1620`, indexed by the column `x : ℕ` and the row `y : ℕ`
read modulo `4`.  The first two columns are the special origin block; from `x=2`
on the background is the `4`-periodic block `ζ₁'`. -/
def ce3_zetaP (x y : ℕ) : ℕ :=
  if x = 0 then (if y % 4 = 0 then 3 else if y % 4 = 1 then 3 else if y % 4 = 2 then 2 else 4)
  else if x = 1 then (if y % 4 = 0 then 3 else if y % 4 = 1 then 3 else if y % 4 = 2 then 3 else 2)
  else if y % 4 = 0 then (if x % 4 = 0 then 3 else if x % 4 = 1 then 2 else if x % 4 = 2 then 2 else 3)
  else if y % 4 = 1 then (if x % 4 = 0 then 2 else if x % 4 = 1 then 3 else if x % 4 = 2 then 3 else 2)
  else if y % 4 = 2 then (if x % 4 = 0 then 2 else if x % 4 = 1 then 3 else if x % 4 = 2 then 3 else 2)
  else (if x % 4 = 0 then 3 else if x % 4 = 1 then 2 else if x % 4 = 2 then 2 else 3)

/-- The displayed `{0,1}` initial condition `ŵ_0` of `exploding-corrected-arxiv.tex:1653-1661`:
all of columns `0,1,2` toppled, plus the two corners `(3,0)`, `(3,3)`. -/
def ce3_w0 (x y : ℕ) : Bool :=
  if x ≤ 2 then true
  else if x = 3 then (if y % 4 = 1 then false else if y % 4 = 2 then false else true)
  else false

/-! ### The finite time slice and its step -/

/-- Coerce a Boolean odometer value to `ℕ`. -/
def ce3_b2n (b : Bool) : ℕ := b.toNat

/-- The odometer at the site of index `i` of a finite slice. -/
def ce3_get (l : List Bool) (i : ℕ) : Bool := l.getD i false

/-- The cylinder neighbour sum `∑_{z ∼ (x,y)} w(z)` on a slice.  The reflecting
boundary at `x = 0` is automatic from the truncating subtraction
`(0 - 1) * 4 + y = y`, which returns the self index. -/
def ce3_nbr (l : List Bool) (x y : ℕ) : ℕ :=
  ce3_b2n (ce3_get l ((x - 1) * 4 + y)) + ce3_b2n (ce3_get l ((x + 1) * 4 + y)) +
    ce3_b2n (ce3_get l (x * 4 + (y + 1) % 4)) + ce3_b2n (ce3_get l (x * 4 + (y + 3) % 4))

/-- One step of the capped last-wave odometer on a slice of `N` columns: a site
that has not yet toppled topples exactly when its cylinder sandpile
`ζ'(x,y) + Δw(x,y)` reaches `4`. -/
def ce3_step (N : ℕ) (l : List Bool) : List Bool :=
  (List.range (N * 4)).map (fun k =>
    let x := k / 4
    let y := k % 4
    ce3_get l k || Nat.ble 4 (ce3_zetaP x y + ce3_nbr l x y))

/-- The slice holding the displayed initial condition on `N` columns. -/
def ce3_init (N : ℕ) : List Bool :=
  (List.range (N * 4)).map (fun k => ce3_w0 (k / 4) (k % 4))

/-! ### Locality -/

/-- **Extraction.**  The entry at index `i` of one step is the local formula,
provided `i` is inside the slice. -/
theorem ce3_step_getD (N i : ℕ) (l : List Bool) (hi : i < N * 4) :
    (ce3_step N l).getD i false =
      (ce3_get l i || Nat.ble 4 (ce3_zetaP (i / 4) (i % 4) + ce3_nbr l (i / 4) (i % 4))) := by
  have hlen : i < (ce3_step N l).length := by
    simp only [ce3_step, List.length_map, List.length_range]
    omega
  rw [List.getD_eq_getElem (l := ce3_step N l) (d := false) (n := i) hlen]
  simp only [ce3_step, List.getElem_map, List.getElem_range]

/-- The neighbour sum depends only on the (at most five) neighbouring entries. -/
theorem ce3_nbr_congr {l l' : List Bool} {x y : ℕ}
    (h1 : ce3_get l ((x - 1) * 4 + y) = ce3_get l' ((x - 1) * 4 + y))
    (h2 : ce3_get l ((x + 1) * 4 + y) = ce3_get l' ((x + 1) * 4 + y))
    (h3 : ce3_get l (x * 4 + (y + 1) % 4) = ce3_get l' (x * 4 + (y + 1) % 4))
    (h4 : ce3_get l (x * 4 + (y + 3) % 4) = ce3_get l' (x * 4 + (y + 3) % 4)) :
    ce3_nbr l x y = ce3_nbr l' x y := by
  unfold ce3_nbr
  rw [h1, h2, h3, h4]

/-- **Locality.**  If two slices agree on the `(N+1)`-column window, then one
step of the `N`-column slice agrees on the `N`-column window: the state at `t+1`
is a function of the state enlarged by one column at `t`. -/
theorem ce3_step_local (N : ℕ) {l l' : List Bool}
    (h : ∀ i, i < (N + 1) * 4 → ce3_get l i = ce3_get l' i) :
    ∀ i, i < N * 4 →
      (ce3_step N l).getD i false = (ce3_step N l').getD i false := by
  intro i hi
  have hL : ce3_get l ((i / 4 - 1) * 4 + i % 4) = ce3_get l' ((i / 4 - 1) * 4 + i % 4) :=
    h _ (by omega)
  have hR : ce3_get l ((i / 4 + 1) * 4 + i % 4) = ce3_get l' ((i / 4 + 1) * 4 + i % 4) :=
    h _ (by omega)
  have hU : ce3_get l (i / 4 * 4 + (i % 4 + 1) % 4)
      = ce3_get l' (i / 4 * 4 + (i % 4 + 1) % 4) := h _ (by omega)
  have hD : ce3_get l (i / 4 * 4 + (i % 4 + 3) % 4)
      = ce3_get l' (i / 4 * 4 + (i % 4 + 3) % 4) := h _ (by omega)
  have hself : ce3_get l i = ce3_get l' i := h i (by omega)
  have hN : ce3_nbr l (i / 4) (i % 4) = ce3_nbr l' (i / 4) (i % 4) :=
    ce3_nbr_congr hL hR hU hD
  rw [ce3_step_getD N i l hi, ce3_step_getD N i l' hi, hself, hN]

/-! ### The `12`-step period -/

/-- The state of the `14`-column slice after `12` steps, expected to be the
initial pattern translated by `8` columns: columns `0..10` toppled, column `11`
toppled only in rows `0,3`, columns `12,13` empty. -/
def ce3_reset (N : ℕ) : List Bool :=
  (List.range (N * 4)).map (fun k =>
    let x := k / 4
    let y := k % 4
    if x ≤ 10 then true else if x = 11 then (y = 0 || y = 3) else false)

/-- **The `12`-period of the finite front** (`exploding-corrected-arxiv.tex:1663-1867`, checked
by kernel `decide`): after `12` steps the `14`-column slice is the initial
pattern translated by `8` columns. -/
theorem ce3_reset_spec : (ce3_step 14)^[12] (ce3_init 14) = ce3_reset 14 := by
  decide

/-- The period, restricted to the seven-column front window `7..13`: after `12`
steps the window is the initial window translated by `8` columns (with column
`-1` read by reflection as column `0`). -/
theorem ce3_reset_window (i : Fin 7) (y : Fin 4) :
    ((ce3_step 14)^[12] (ce3_init 14)).getD ((i.val + 7) * 4 + y.val) false =
      ce3_w0 (i.val - 1) y.val := by
  rw [ce3_reset_spec]
  fin_cases i <;> fin_cases y <;> decide

end Exploding
