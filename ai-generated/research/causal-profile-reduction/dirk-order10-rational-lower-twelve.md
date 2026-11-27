# Twelve stages are necessary for rational DIRK order ten

**Theorem (mathematical).** Let \(A\) be lower triangular with \(s\) stages,
and let \(\boldsymbol b\) be its output weights, both with entries in \(\mathbb Q\).
If the tableau satisfies actual rooted-tree order ten, then \(s\ge12\).
The real eleven-stage construction is unaffected. This note does not
construct a twelve-stage rational method. A [subsequent explicit rational tableau](../dirk10-twelve-rational-three-ports/README.md) attains the bound.

Write \(\boldsymbol c=A\boldsymbol 1\) for the abscissa vector and \(\boldsymbol g=A\boldsymbol c^{\odot2}-\boldsymbol c^{\odot3}/3\) for the cubic stage defect. Set
\[
 D=\{c_i:g_i\ne0\},\qquad
 r=\#\{c_i:b_i g_i\ne0\},\qquad
 z=\#\{i:b_i=0,\ g_i\ne0\},\qquad d=|D|.
\]
Thus \(d\) counts distinct physical dirty clock values, including unweighted
ones; \(r\) counts distinct individually active dirty values, not nonzero
aggregate signed masses; \(z\) counts physical rows, not labels. In particular
\(d\le r+z\), even if dirty clocks repeat or coincide with a clean clock.
All power operations on columns are componentwise.

## 1. Native equality inputs and a support exclusion

By the native stage floor
[`CrossedOrderTen.stage_floor`](../../lean/RKCert/ReviewedNative/DIRKOrderTenSaturation.lean)
it suffices to exclude \(s=11\). The same file, theorem `saturated`,
gives \(C(2)\), a true zero first row, an active physical terminal clock
\(1\) with zero tableau column, \(D(1),D(2)\), \(\dim E_4=7\),
\(\dim E_5=9\) and \(\dim F_5=3\). Here \(E_j\) is the native
tree column space and \(F_j\) the native defect space at grade \(j\).
Paid coefficient separation gives \(\dim F_4=2\).
Both physical endpoints have zero cubic defect: this is immediate at the
first row and proved at the terminal in
[`last_cubic_clean`](../../lean/RKCert/ReviewedNative/DIRKOrderTenDirtyInventory.lean)
via its terminal indicator in \(E_5\). In particular \(r\le9\).
The ordinary first moment gives a nonzero clock. At its first occurrence
\(C(2)\) gives \(A_{ii}=c_i/2\), so \(g_i=c_i^3/6\ne0\).
Hence \(d\ge1\).

In fact \(d\notin\{2,3\}\), regardless of output weights. For \(d=2\),
the two independent vectors \(g,Cg\), where \(C=\operatorname{diag}(c)\),
span \(F_4\); for \(d=3\), the three independent vectors \(g,Cg,C^2g\)
span \(F_5\). Membership costs one paid grade per multiplication by \(C\);
independence follows by evaluating at one nonzero \(g_i\) per label.
In each case every polynomial weighted evaluation \(g_iP(c_i)\) belongs
to this span by interpolation on \(D\), so the space is \(C\)-invariant.
With \(j=4\), the native
[`dirk_forward_invariant_outgoing` / `dirk_forward_invariant_incoming`](../../lean/RKCert/ReviewedNative/DIRKPrefixHermite.lean)
give a gain of at least two dimensions from \(F_4\) to \(F_5\)
if respectively \(F_4\) or \(F_5\) is invariant. Either contradicts the
actual gain \(3-2=1\). This uses genuine inclusive DIRK Hermite, not
a stricter explicit-method chronology or any assumed zero diagonals.
The Hermite bridge is field/characteristic-zero; no ordering is needed. The [native adapter](../../lean/RKCert/ReviewedNative/DIRKOrderTenPhysicalDirtySupport.lean) proves both the two- and three-label exclusions and the resulting singleton-or-at-least-four dichotomy directly for actual \(\mathtt{HasOrder}\). Both theorems passed the [typed Lean 4.36.0 audit](dirk-order10-physical-dirty-lean-audit.txt).

## 2. A small exact quadrature test

If the ordinary aggregate weights are supported on some rational set
\(T\) with \(0,1\in T\) and \(|T|\le6\), add distinct rational labels
with zero mass to make \(|T|=6\). Put
\(P(x)=\prod_{t\in T\setminus\{0,1\}}(x-t)\).
For \(k=0,1,2,3\), the ordinary tree moments through degree nine give
\[
 \int_0^1 x(1-x)x^k P(x)\,dx=0,
\]
as the corresponding weighted evaluation vanishes at every label of \(T\).
The unique monic quartic satisfying these equations is
\[
 J_4(x)=x^4-2x^3+\tfrac43x^2-\tfrac13x+\tfrac1{42}.
\]
The displayed coefficients satisfy the four equations using
\(\int_0^1 x(1-x)x^j\,dx=1/((j+2)(j+3))\).
For uniqueness take the difference \(R\) of two candidates, of degree
at most three, and test it against itself; strict positivity of its
weighted square unless \(R=0\) suffices over \(\mathbb Q\).
Equivalently the exact shifted Beta matrix is nonsingular.
But with \(\rho=x(1-x)\),
\(42J_4(x)=42\rho^2-14\rho+1\) has discriminant \(28\), not a rational
square. Thus \(J_4\) has no rational root, contradicting the four
rational roots of \(P\). The no-rational-root scalar fact is also [Lean-checked](../../lean/RKCert/ReviewedNative/DIRKOrderTenRationalPoleScalars.lean) as `no_rat_root_jacobi`. This argument allows signed weights, unused
labels, zero aggregate mass at an endpoint, and repeated physical
clocks; only the support set is distinct.

## 3. Exhaustive multiple-dirty ledger

The reviewed native [signed dirty inventory](dirk-order10-signed-dirty-inventory.md)
proves \(r\le2\) or \(r\ge8\), and its theorem `dirty_inventory_of_small`
gives \(6+2r+z\le11\) in the low branch. Its proof constructs the
accounting support, not just its cardinality, as recalled below.
The high branch uses the separate
[eight-/nine-label cubic census](dirk-order10-eight-dirty-endpoint-census.md).
Only its scalar clock conclusion is needed here: \(r=9\) is impossible
and \(r=8\) gives an actual clean interior clock satisfying \(J_4=0\).
The later pivot or rank refinements in that note are not used.
Consequently \(r\ge8\) cannot occur over \(\mathbb Q\).

Now assume \(d\ge2\). Section 1 gives \(d\ge4\). The low possibilities
are as follows.

* **\(r=2\):** \(z\le1\), so \(d\le r+z\le3\), impossible.
* **\(r=1\):** Necessarily \(z=3\) from \(d\le r+z\) and the
  inventory. At the unique active dirty clock choose two distinct
  active dirty rows, possible since the paid first defect moment is
  zero on that fiber. Remove these two rows and the three ghosts.
  The six remaining rows include both true clean endpoints. For a
  label that disappears, if it had any nonzero weights, these were
  exactly the chosen pair. The paid first two defect moments at this
  fiber say \(w_i+w_j=w_i g_i+w_j g_j=0\) for \(w_i=b_i g_i\ne0\),
  so the pair has equal nonzero defect and opposite ordinary weights.
  Thus the disappearing label has zero aggregate weight. If additional
  active/clean rows at the same label occur, it does not disappear
  and requires no cancellation argument. Ghosts never affect ordinary
  mass. This is precisely the `choose_pairs` /
  `raw_outside_after_pairs` accounting in the native inventory.
  Therefore the remaining label set is a possible support as in
  Section 2, a contradiction.
* **\(r=0,z=5\):** Every dirty row is a ghost, so the at most six
  clean labels contain the ordinary support and the two true
  endpoints. Section 2 applies directly, including all repeated
  clean or dirty labels.
* **\(r=0,z=4\):** This is the only other case, since
  \(4\le d\le z\le5\). Here \(d=4\) and the four ghosts have distinct
  labels. For each ghost \(i\) its unit indicator is in \(F_6\subseteq E_6\):
  use \(g\) times the degree-three cardinal polynomial for its dirty
  label, divided by \(g_i\). This vanishes on all clean rows even
  if a clean row has that same label. The genuine reflected cubic
  row \(G=\beta Y^2 A-\beta Y^3/3\), with
  \(\beta=b^\mathsf{T}\) as an output row and \(Y=\operatorname{diag}(1-c)\),
  annihilates \(E_6\); this is the paid cubic read.
  It is nonzero: there is an active clock other than \(1\) by the
  ordinary zeroth and first moments. At the physically last such
  row \(i\), put \(u=1-c_i\ne0\). Causality and the exact reflected
  \(D(2)\) give \(A_{ii}=u/2\) and then \(G_i=b_i u^3/6\ne0\).
  Since \(G\) kills the four indicators, it vanishes at every ghost.
  If the seven remaining rows had distinct clocks, its seven reads
  on \(1,c,\ldots,c^6\in E_6\) would force every remaining entry
  of \(G\) to vanish by Vandermonde. Thus the clean label set has
  at most six elements and again satisfies Section 2. This is only
  the initial support argument of the
  [four-invisible-row analysis](dirk-order10-invisible-four-lobatto.md);
  none of its later mixed-rank or modular eliminants enter.

The repeated/zero-weight cases are exhausted by this ledger. We have
excluded every rational tableau with \(d\ge2\).

## 4. Conclusion and proof scope

The separate
[exact genus-two closure](dirk-order10-rational-single-clock-genus-two.md)
excludes \(d=1\) for rational eleven-stage order-ten DIRK; \(d=0\)
was excluded above. The native stage floor then gives \(s\ge12\)
over \(\mathbb Q\), and also over any coefficient ring embedded in
\(\mathbb Q\), by transport of its actual rooted identities.
The proof makes no claim over arbitrary characteristic-zero fields
or over arbitrary rings: already the Lobatto test is rational
arithmetic, and eleven stages are attained over the reals.

This is a mathematical stage lower bound assembled from reviewed native
equality inputs, the exact rational support argument, the prior high
mathematical census, and the exact one-clock genus-two proof. It is
not a single fully native Lean theorem; in particular the Chabauty
step is a mathematical argument with separate exact arithmetic receipts.
