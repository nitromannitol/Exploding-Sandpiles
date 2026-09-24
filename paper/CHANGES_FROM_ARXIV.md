# Differences from the arXiv version

The formalization follows `paper/exploding.tex`.  It is the version of
arXiv:2102.04422v2 submitted to the Annals of Applied Probability, with the corrections
below.  The arXiv source will be replaced by the corrected text.  The unmodified arXiv
source is `paper/exploding-arxiv.tex`, with its macro file and bibliography in
`paper/arxiv/`; its figures are not included.  The statements of the two versions agree
except where an entry below changes them.  Line numbers refer to the corrected
`paper/exploding.tex`.

## Journal format

The submitted version uses the `imsart` class of the journal and differs from the arXiv
source only in layout; none of these changes affects the mathematics.

- Lines 1-173 and 190-196: the `imsart` preamble and front matter, with the macros of the
  arXiv file `defs.tex` inlined, and the placement option of the first figure.
- Lines 203-224: the paragraph on the work of Pegden and Smart is moved below the first
  figures.
- Lines 257, 407-415, 773-780, 910-920 and 1566-1707: indentation of display and table
  lines.
- Lines 295-300 and 2006-2046: the acknowledgments are moved to the end, and the
  bibliography is typeset with the journal style.

## Section 2, proof of Proposition 2.1 (`prop:crossing_time`), line 447

arXiv: "Iterating shows this procedure will terminate with every site in $Q_k$ toppling in
at most $k^{d}$ steps."

Corrected: "A line in $Q_k$ topples within $k$ steps once a neighboring line has toppled:
its site with $(2d-1)$ chips topples at the next step and the toppling then spreads along
the line one site per step. Every line in $Q_k$ is joined to $\mathcal{L}_k^{(1,z)}$ by a
chain of at most $(d-1)(k-1) + 1 \leq k^{d-1}$ neighboring lines, so this procedure
terminates with every site in $Q_k$ toppling in at most $k^{d}$ steps."

The bound $k^d$ is unchanged.  The added count shows it also for a seed $z$ in the outer
boundary of $Q_k$, whose line lies outside $Q_k$ and is one line further from the far
side of the cube.

## Section 2, the paragraph before Proposition 2.2, line 478

arXiv: "For $k$ sufficiently large, Proposition 2.1 implies that the set of good cubes
dominates a high density independent site percolation process on the macroscopic
lattice. This together with large deviations bounds for supercritical percolation
[Antal and Pisztora; Garet and Marchand] imply the following. (See, for example,
Section 5 in [Mathieu] for an explicit proof.)"

Corrected: the good cubes form an independent site process; an edge of the macroscopic
lattice is good when both of its cubes are good; the good edges have a dependence graph of
degree $4d - 2$, so by Corollary 1.4 of Liggett, Schonmann and Stacey they dominate an
independent bond percolation process $\zeta$ of density close to 1.  The cubes all of whose
$\zeta$-edges are open form a site process in which cubes that are not neighbors are
independent, which by the same corollary dominates a high density independent site
percolation process.  $\mathcal{C}_\infty$ is the open cluster of $\zeta$ containing an
infinite cluster of this site percolation process.  Lemma 5.2 of Mathieu bounds its holes,
and Theorem 1.1 of Antal and Pisztora with the Borel-Cantelli lemma bounds its chemical
distance.

The chemical distance bound of Antal and Pisztora, and that of Garet and Marchand, is a
theorem about bond percolation, while the good cubes are a site process.  The corrected
argument applies it to a bond percolation process, as published, and the citation of
Garet and Marchand is dropped.

## Section 2, Proposition 2.2 (`prop:renormalization_properties`), item 1, line 486

arXiv: "There is a unique infinite cluster $\mathcal{C}_{\infty}$ of good cubes on the
macroscopic lattice $\{Q_k(i)\}_{i \in \Z^d}$."

Corrected: "There is an infinite connected set $\mathcal{C}_{\infty}$ of good cubes on the
macroscopic lattice $\{Q_k(i)\}_{i \in \Z^d}$."

The set produced by the argument above is an infinite connected set of good cubes with
properties 2 and 3; the rest of the paper uses only these properties, and uniqueness of
an infinite cluster of good cubes is neither proved nor needed.

## Section 3, before Lemma 3.1, line 704

arXiv: "The following is a consequence of Theorem 4.1 in [Fey-den Boer and Redig]."

Corrected: the sentence is deleted.

## Section 3, Lemma 3.1 (`lemma:square_lower_bound`) and its proof, lines 705-714

arXiv: "There is a constant $C := C_d$ so that for all $n \geq 1$, the support of the
$(C n^d)$-wave contains $[-n,n]^d$."  The proof takes $\tilde{v}(0) \leq C n^d$ for the
terminal odometer of $n$ chips on the background $2d - 2$ from Theorem 4.1 of Fey-den Boer
and Redig.

Corrected: "Suppose $\eta \geq 0$. For all $n \geq 1$ and $m \geq (2d)^{d n}$, the support
of the $m$-wave contains $[-n,n]^d$."  The proof is an induction on time:
$u_t(x) \geq \lfloor m (2d)^{-|x|} \rfloor$ whenever $|x| \leq t$, since $x \neq 0$ has a
neighbor $y$ with $|y| = |x| - 1$, and every $x \in [-n,n]^d$ has $|x| \leq dn$.

The cited theorem bounds the radius of the toppled cube and says nothing about the odometer
at the origin, and the arXiv statement is false in $d = 2$: the least $m$ whose $m$-wave on
the background $2$ covers $[-n,n]^2$ grows like $n^2 \log n$.  Lemma 3.2 and the proof of
Proposition 5.1 use only that some finite wave covers $[-n,n]^d$, which the corrected
statement gives.

## Section 3, proof of Lemma 3.6 (`lemma:penultimate_upper_bound`), line 815

arXiv: "the support of the odometer will overlap the infinite cluster at a good cube near
the origin, ... at most a constant times the chemical distance in the infinite cluster."

Corrected: "the infinite cluster" is replaced by $\mathcal{C}_{\infty}$ in both places, the
set of Proposition 2.2.

## Section 3, proof of Proposition 3.1 (`prop:convergence_of_the_last_wave`), lines 854-863

arXiv: "Convergence in integer directions follows from the subadditive ergodic theorem.
Everywhere convergence then follows from continuity and approximation."

Corrected: the proof first states two bounds, `eq:lastwave_lipschitz`, which hold on an
event of probability 1 for all $n$ large and $x, x' \in [-n,n]^d$:
$\tilde{T}(x) \leq C|x| + (\log n)^{\gamma}$, which is Lemmas 3.6 and 3.7, and
$\tilde{T}(x') \leq \tilde{T}(x) + C|x - x'| + (\log n)^{\gamma}$.  The second is proved
from $x$: at time $\hat{T}(x)$ the support of the last-wave contains a path of distinct
points from the origin to $x$; Lemma 2.1 fills the bounding rectangle of its last
$(\log n)^{\gamma'}$ points, which contains a line of a cube of $\mathcal{C}_\infty$ by
Proposition 2.2; from there the argument of Lemma 3.6 reaches $\mathcal{P}(x')$.  The
subadditive ergodic theorem is then applied to $\tilde{T}(0, ny)$ for $y \neq 0$ through
the transformation induced on $A = \{\tilde{T}(0,ny) \leq C'n + K \mbox{ for all } n\}$:
translation by $y$ is mixing, hence ergodic; the first term of the induced process is at
most $C' r_1 + K$, integrable by Kac's lemma; the second bound passes from the return
times $r_j$ to all $n$ on $A$, and the limits inferior and superior are invariant under
translation by $y$ by Lemma 3.4, so the convergence holds almost surely.  "Continuity" is
replaced by the second bound.

The subadditive ergodic theorem needs $\tilde{T}(0,y)$ to be integrable, and the proof
gave no moment bound: Proposition 2.2 and Lemmas 3.6 and 3.7 hold only on an event of
probability 1.  A moment bound would need tail estimates for the holes and chemical
distances of $\mathcal{C}_\infty$ and for $\hat{M}_\eta(0)$, and the only bound on
$\hat{M}_\eta(0)$ available here, from Lemma 3.1, is exponential in the distance to
$\mathcal{C}_\infty$.  The induced transformation needs only the almost sure bounds.  The
approximation step needs to compare $\tilde{T}$ at two points $x, x'$, while Lemma 3.6
bounds $\tilde{T}(x)$ only through $|x|$; the second bound gives this comparison.  The
same argument is used in the proof of Proposition 5.1, with Hypothesis 5.3 in place of
Lemma 2.1.

## Section 5, the setting, line 1114

arXiv: "Fix $\eta_{\min} \in \Z$ and let $\Omega$ denote ..."

Corrected: "Fix an integer $\eta_{\min} \geq 0$ and let $\Omega$ denote ..."

If $\eta$ takes negative values the $n$-wave need not be monotone and can decrease without
bound: on $\eta \equiv -1$ its values far from the origin are $-1, -2, \ldots$.  The
last-wave argument of Section 3 needs $\eta \geq 0$.

## Section 5, Hypothesis 5.1 (`hyp:finite_range_of_dependence`), line 1138

arXiv: "There exists a constant $K < \infty$ so that for all $x,y \in \Z^d$, $\eta(x)$ and
$\eta(y)$ are independent if $|x-y| > K$."

Corrected: "There exists a constant $K < \infty$ so that for all finite
$A, B \subset \Z^d$ with $|x-y| > K$ for every $x \in A$ and $y \in B$, the families
$\{\eta(x)\}_{x \in A}$ and $\{\eta(y)\}_{y \in B}$ are independent."

The proof of Proposition 5.1 applies Theorem 0.0 of Liggett, Schonmann and Stacey, which
needs the field of strongly box-crossing boxes to be $m$-dependent as a family.  Pairwise
independence does not give this: with $(A, B)$ uniform on $\mathbb{F}_q^2$, the indicators
$1\{A + aB \neq 0\}$ for $a \in \mathbb{F}_q$ and $1\{B \neq 0\}$ are pairwise independent with mean $1 - 1/q$ and
never all equal to 1.  The Bernoulli clouds of Section 5.2 satisfy the corrected
hypothesis.

## Section 5, proof of Proposition 5.1 (`prop:convergence_of_the_generalized_last_wave`), lines 1214-1235

arXiv: "... Therefore, for $\delta > 0$ sufficiently small, on an event of probability 1,
$\{X_j\}_{j \in \Z^d}$ contains an infinite supercritical percolation cluster
$\mathcal{C}_{\infty}$. The rest of the argument follows almost exactly the proof in
Section 3. The only minor change is in the proof of Lemma 3.1. We use
$\eta \geq \eta_{\min}$ rather than $\eta \geq (2d - 2)$ and invoke Theorem 4.1 in
[Levine and Peres] to get that the support of a $(C n^d)$-wave contains $[-n,n]^d$ (where
the constant $C$ is larger than before)."

Corrected: a first sentence says that $X_j$ depends only on $\eta$ in
$\mathcal{B}^{(j)}_k$, so Hypothesis 5.1 makes $\{X_j\}$ $m$-dependent for some
$m < \infty$.  The conclusion of the first paragraph becomes: the argument before
Proposition 2.2 applies to $\{X_j\}$ in place of the good cubes, since the good edges again
have a dependence graph of bounded degree, and gives an infinite connected set
$\mathcal{C}_\infty$ of strongly box-crossing boxes with properties 2 and 3 of
Proposition 2.2.  The last two sentences are replaced by three paragraphs, lines
1219-1235.  The first says where Section 3 uses the background: Lemma 3.1 only
$\eta \geq 0$, Lemmas 3.3 and 3.4 only $0 \leq \eta \leq 2d-1$, and $\eta \geq 2d-2$
enters only through Proposition 2.1, which Hypothesis 5.4 replaces, and Lemma 2.1, which
Hypothesis 5.3 replaces for long paths.  It gives the proof of Lemma 3.5 without the
rectangle: a long path in the support of $\tilde{u}^{(x)}$ fills its bounding rectangle by
Hypothesis 5.3, which then contains a line of a box of $\mathcal{C}_\infty$, contradicting
stability.  The second proves that $\eta$ is explosive: a stabilizable
$\eta + 2d\hat{M}_\eta(0)\delta_0$ would have a finitely supported terminal odometer
dominating the last-wave.  The third applies the subadditive ergodic theorem to
translations by $y \in \mathcal{L}$, ergodic by Hypothesis 5.1, and replaces the moment
bound it needs by the two bounds of `eq:generalized_lipschitz`, through the transformation induced on
$\{\tilde{T}(0,ny) \leq C'n + K \mbox{ for all } n\}$ and Kac's lemma.

The first change states the dependence that Theorem 0.0 of Liggett, Schonmann and Stacey
needs.  The second replaces a supercritical cluster, for which the holes and chemical
distance bounds were not argued, by the construction of Section 2.  The third fills a gap:
Section 3 fixes $\eta \geq 2d-2$, and its Lemma 2.1 is false for the backgrounds of
Section 5, where the support of $\tilde{u}^{(x)}$ need not be a rectangle; Section 3 takes
explosiveness from Fey, Levine and Peres, which does not apply here; and Hypothesis 5.3
holds only on an event of probability 1, so it gives no bound on the mean of
$\tilde{T}(0,y)$, which the subadditive ergodic theorem needs, and stationarity under
$\mathcal{L}$ alone does not make a single translation ergodic.  On backgrounds with values
in $\{0,1,2,3\}$ in $d = 2$, the support of $\tilde{u}^{(x)}$ was not a rectangle in 117 of
311 cases, while the bound of Lemma 3.3 and the subadditivity of Lemma 3.4 held in every
case tested.
