# Active single-physical-dirty-clock exclusions for normalized DIRK11/13

Assume the [signed cubic census](../causal-profile-reduction/dirk-order11-thirteen-signed-cubic-census.md) hypotheses:
literal thirteen-stage lower triangular rooted order eleven, forward
\(C(2)\), genuine reflected \(D(1),D(2)\), and the ordinary grade-six
surplus. Here every nonzero forward cubic defect is at one physical
numerical clock \(\xi\), and at least one such row has nonzero weight
(\(r=d=1\)). Thus this is a different face from the
[one-active five-physical-label exclusion](../dirk11-thirteen-fourth-clean/README.md).

We exclude both of these branches:
* the nonzero cubic values on the **active** dirty rows are not all equal;
* those active cubic values are equal, and the weighted fourth head
  defined below is nonzero on **at most one** numerical label outside
  \(\xi\).

In particular the remaining active one-local face has common active
nonzero cubic value and at least two weighted exterior fourth-head
labels. No restriction is asserted for an entirely invisible cubic
or for an unnormalized tableau. The unrestricted real interval
remains **13–14**. The deductions here are over characteristic-zero
fields given the stated normalized ranks. The rational moment Gram
forms used in the proof are fixed and nondegenerate, and do not
require an order on the tableau field.

## 1. One physical cubic clock and the next true head

Use \(C=\operatorname{diag}(c)\), \(\beta=b^{\mathsf T}\), and write
\(g=Ac^2-c^3/3\), \(h=(A-\xi/2)g\). Let \(E_j,F_j\) be the actual tree
and zero-profile spaces; \(E_6\) contains the genuine terminal cardinal
\(e_T\), while \(E_5\) does not, and the indicated true ranks are
\(f_4=2,f_5=3,f_6=5,e_5=9,e_6=11,e_7=12\). The terminal weight is
nonzero, its clock is one, and its actual \(A\)-column is zero.
The literal first row and its clock are zero.

At the first nonzero physical clock \(x\), \(C(2)\) gives diagonal
\(x/2\), so \(g=x^3/6\ne0\) there and \(x=\xi\ne0\). Throughout a prefix
of clocks only \(0,\xi\), the identity \(Ac^2=\xi Ac\) on that prefix
gives \(g=\xi^3/6\) at \(\xi\) and zero at 0. The same weighted tap read
into \(\xi\) shows \(h=0\) throughout that prefix. At the first
clock \(z\notin\{0,\xi\}\), which exists by the ordinary scalar
moment tests, \(g_z=0\). If \(S\) is its actual aggregate tap into
\(\xi\), the two true stage moments give
\[
 \xi S+z A_{zz}=z^2/2,\qquad \xi^2 S+z^2 A_{zz}=z^3/3.
\]
Here \(A_{zz}\) denotes the physical debut row's diagonal, not an
aggregate over other positions. It follows that
\(h_z=\xi^2 z^3/[36(z-\xi)]\ne0\). Thus \(F_4=\langle g,h\rangle\).
The inclusive two-detector Hermite gain out of \(F_4\) or into \(F_5\)
rules out clock invariance of either (it would cost two, not one,
dimensions at this step). Since \(Cg=\xi g\), this gives
\[
 F_5=\langle g,h,Ch\rangle,\qquad
 U_4=\langle g,h,Ch,C^2h\rangle\subset F_6,\qquad \dim U_4=4.
\]
True pairing of \(e_T\in E_6\) with \(h\in F_4\) shows \(h_T=0\);
\(g_T=0\) is also known. Thus \(U_4\) is terminal-zero.

At the reflected clock \(y=1-c\), the genuine unscaled cubic row
\(G=N(b y^2)-b y^3/3\), \(N=A^{\mathsf T}\) in reverse chronology,
is a nonzero multiple of \(\beta g\), since both annihilate \(E_7\).
At the latest active nonunit row its value is \(b_i y_i^3/6\),
paid by the actual first reflected moment and the literal diagonal.
Consequently \(V=1-\xi\ne0\). Write
\(Z=E_5^\perp\cap\{\ell_T=0\}\), of dimension three, and
\(U_0=E_6^\perp\), of dimension two with \(U_0\subset Z\).
Both \(G\in U_0\) and \(NG\in U_0\) are genuine, the latter from
\(A E_6\subset E_7\).

## 2. Grouped fourth-head invisibility and the terminal alias

Whenever the grouped weighted row \(\beta h\) has aggregate zero at
every numerical clock, one has
\[
 F_6=U_4+K(e_T-H_T(c)),\qquad E_6=\mathcal P_5(c)+U_4+K e_T,\qquad
 H_T(X)=30 b_T X\Phi_4(X),
 \quad \Phi_4=42X^4-84X^3+56X^2-14X+1.                 \tag{1}
\]
Here \(H_T\) is the genuine terminal polynomial profile already
determined in the signed census. To prove (1), if its residual
\(e_T-H_T(c)\) were in \(U_4\), evaluation at \(T\) would give
\(H_T(1)=1\). Then every numerical clock outside \(\xi\) and the six
fixed possible nodes \(0,1,\{\Phi_4=0\}\) has constant nonzero \(h\)
on its physical fiber: the terminal equation reads
\(H_T(x)+L_2(x)h_i=0\) with \(L_2(x)\ne0\).
The vanishing \(\beta h\) aggregate forces ordinary aggregate zero
on every such fiber. The one possibly remaining off-node clock
\(\xi\) is killed by the true ordinary test \(X(1-X)\Phi_4(X)\): its
integral is zero and its value at an off-node \(\xi\) is nonzero.
But then \(X(1-X)\Phi_4(X)^2\) would have zero quadrature reading and
integral \(1/330\ne0\), contrary to its paid degree ten. This is a
rational identity, not a sign test on an unknown clock.

Thus the actual terminal residual adds the fifth direction of
\(F_6\). The six degree-five scalar evaluations are separated from
\(F_6\) by the true origin and the fixed \(X\,dX\) Gram matrix on
degree at most four: a coincident polynomial has \(P(0)=0\) and its
five genuine zero-profile moments paid. This proves the \(E_6\)
decomposition in (1). No value of \(b_T\) is prescribed in (1).

## 3. A weighted-variable active core is impossible

Suppose \(\beta g\) sees at least two distinct nonzero cubic values.
Then \(G_1=\beta g\), \(G_2=\beta g^2\) are independent (divide only
at the two live nonzero cubic entries). They both lie in \(Z\), and
both are supported on the active dirty core. For \(G_2\), test the
actual \(E_5=\mathcal P_5(c)+\langle g,h,Ch\rangle\): the tests reduce
to \(\beta g^2=0,\ \beta g^3=0,\ \beta g^2 h=0\) as scalar sums, paid at
grades \(6,9,10\), because \(c=\xi\) on the support of \(g\).
In particular no unpaid degree-eleven product with \(Ch\) has been
used. Meanwhile \(\beta h\in U_0\) (grade \(4+6\)) and
\(Y(\beta h)\in Z\) by the true single-clock multiplication grade.

If grouped \(\beta h\) were nonzero, its seven zero scalar moments
through degree six would require at least eight live numerical
aggregates by Vandermonde. At least seven would be outside \(\xi\).
On those coordinates \(\beta h,Y(\beta h)\) are independent modulo
the two purely core-supported rows \(G_1,G_2\): any relation gives
an affine polynomial vanishing at two or more distinct live clocks.
This would give four independent rows in \(Z\), contradiction.
Thus grouped \(\beta h=0\), and (1) holds. The same localized
\(G_2\) payments also annihilate \(C^2h\) and \(e_T\), so now
\(U_0=\langle G_1,G_2\rangle\) is entirely supported on the active
dirty rows.

There is a live nonzero reflected clock on a \(g\)-clean row;
otherwise the ordinary measure is supported on \(\{0,V\}\) in
the reflected variable and the first three positive moments force
both \(V=2/3\) and \(V=3/4\). Take the first such row in reverse
chronology, denoted \(u\). Every earlier live nonzero donor in that
chronology is at the numerical clock \(V\). On any such earlier
physical row, the genuine first reflected moment and the one-clock
donor support give \(G_i=b_i V^3/6\). More generally on the whole
strict prefix, including ghost rows and live zero-clock rows,
\(G_i=(V^2/6)b_i y_i\); both sides are zero at the latter two kinds.
Since \(NG\in U_0\), its actual \(u\)-coordinate is zero. By the
displayed prefix identity and \(G_u=0\), this cancels the aggregate
first-power dirty donor read at \(u\), hence also its second-power
read (all at \(V\)). The true first and second reflected reads
at \(u\) now both use just its diagonal, requiring \(A_{uu}=u/2\) and
\(u/3\), impossible. This is exactly the row argument checked by
the native adapter; the support census supplying it is above.

## 4. Constant active cubic and no weighted exterior fourth head

Suppose the active dirty values are a common \(\gamma_*\ne0\). If
\(\beta h\) has no weighted exterior entries and is independent of
\(\beta g\), then \(U_0=\langle\beta g,\beta h\rangle\) is supported
at the numerical core \(\xi\). The same native clean cutoff applies
at the first live nonzero reflected row **outside the numerical
core**, which exists by the same scalar tests. This is impossible.
So \(\beta h=\lambda \beta g\); put \(h'=h-\lambda g\), zero on all
active physical rows. This changes neither \(U_4\) nor the true
grade-four space, and (1) holds.

Call a physical row regular if \(g=h'=0\). The signed active dirty
weights sum to zero (paid \(\beta g=0\)), and all other active rows
are regular. The ordinary rule therefore has at least five distinct
live non-endpoint regular labels: otherwise their degree-at-most-four
nodal hull, tested with all polynomials through degree four under
\(X(1-X)\,dX\), contradicts the fixed rational nonsingular Gram
matrix within degree ten. Both actual endpoints are regular.
From the genuine \(c^6\) column in (1), every nonterminal regular
label is a root of one monic sextic. Thus there are exactly seven
distinct regular labels including the endpoints, and the terminal
label has just its actual terminal among regular physical rows
(a second regular unit row would require seven roots). The five
non-endpoint regular masses are live; the physical origin weight
need not be. Also \(g^2\in U_4\): on six distinct nonterminal
regular labels \(g^2=U_4=0\), but \(H_T\) has degree five and cannot
vanish at all six. The coefficient of the terminal residual in
\(g^2\in F_6\) is therefore zero. Evaluating on an active dirty
row also shows that every nonzero \(g\) row where \(h'=0\) has
\(g=\gamma_*\).

All active dirty rows have the same \(E_6\) profile by (1).
Three would fill \(U_0\) by purely core contrasts and give the
same impossible first-clean reverse cutoff; four or more give
too many contrasts already. Two are needed for their signed sum,
so exactly one signed pair remains. Let \(B\) be the actual
pair weights, \(D=NB\); \(G=(V^3/6)B\). The vector \(D\) is
independent of \(B\), or the actual core-only reverse gate would
apply (equivalently the pair would fold). Hence \(U_0=\langle B,D\rangle\).
All physical nonregular rows besides this pair are ghosts. There
are at most four, and at least three distinct nonzero \(h'\) labels
among them (needed for \(g,h',Ch',C^2h'\) to be independent).

* **Three ghosts.** The \(h'P_2\) moments kill \(D\) at each single
  ghost. The \(g\) moment then kills the pair's aggregate \(D\), and
  ordinary powers through degree five kill all six nonterminal
  regular \(D\) class sums. With eight regular physical rows there
  is one duplicate regular class, so \(U_0\) is exactly the two
  signed contrast directions. Use the [grouped reverse debit](../causal-profile-reduction/dirk-order11-thirteen-zero-one-low-dirty.md):
  move regular mass to each last reverse representative, and
  subtract all dirty weight. The resulting two sampled class sums
  contradict the one-dimensional slack \(Z/U_0\).
* **Four ghosts, but only three carry \(h'\).** The three carriers
  again have zero \(D\). The remaining ghost has \(g=\gamma_*\)
  by the \(g^2\) identity. The \(g\) moment now kills the ordinary
  \(D\) aggregate on the entire core, hence degree-five test
  annihilates \(D\) on all regular coordinates. The core-only
  reverse cutoff again applies.
* **Four \(h'\) carriers at three distinct labels.** Both \(D\)
  entries of the repeated ghost label \(\eta\) (reflected variable)
  are live, as the two singleton ghost entries are zero and
  a completely ghost-zero \(D\) would be proportional to \(B\).
  The vector \((Y-\eta)D\in Z\) has no ghost entries and has zero
  dirty-pair aggregate by its \(g\) moment. Its degree-five
  moments then show that \(D\) on regular rows can be nonzero
  only at \(\eta\). At the first nonzero live regular \(u\) in
  reverse the genuine first and second moments give
  \(u\ne V,\ D_u/b_u=-u^3/[6V(V-u)]\), so \(\eta=u\ne V\).
  The \(g\) moment for \(D\) also kills its pair aggregate, since
  its two live ghosts are at \(\eta\ne V\). Subtract a multiple of
  \(B\) to obtain \(D'\) supported only at the regular \(u\) and
  those two ghosts. The true reflected quartic lies in \(U_0\);
  its \(D\) coefficient is \(\mu=V(V-u)(V-u/2)\) by the first
  regular read. At the next distinct nonzero live regular \(v\)
  the aggregate dirty tap \(D_v\) vanishes and the exact cubic
  moment on \(\{0,u,v\}\) forces \(v=2u\). No \(D\)-live ghost
  can precede the third such regular \(w\): applying
  \(P=Y(Y-u)(Y-v)\) to the actual donor slice would force
  \(P(V)=\mu\), hence \(v=u/2\). Thus a literal mask supported on
  \(B\) and a scaled \(D'\) removes the whole active dirty pair
  and the single regular \(u\) entry through \(w\); it introduces
  no ghost entry in that prefix. Both components are supported
  on one clock each, so the mask is in \(U_0\) after multiplying
  by *any* polynomial. The existing [two-sample paid reverse cut](../causal-profile-reduction/dirk-order11-thirteen-paired-reverse-exclusion.md)
  at \(v,w\) gives the contradiction.
* **Four distinct \(h'\) labels.** Every ghost is \(D\)-live by the
  four-label \(D h'P_2\) moment test and the same ghost-zero
  exclusion. The full [grade-six one-active exclusion](../dirk11-thirteen-fourth-clean/README.md)
  transfers, with the precise allowed silent/duplicate timing
  modifications below.

### Why the grade-six closure transfers in the last case

The ordinary measure is on seven regular distinct labels, so their
five non-endpoint labels again follow the same Jacobi pencil. The
actual \(E_4=\mathcal P_4(c)+\langle g,h'\rangle\) vanishes in its
pure coordinates on the regular rows. Thus the clean barycentric
\(H\) and exact \(Z_6=\langle B,D,YD,Y^2D,H\rangle\) hold verbatim,
using the four distinct \(D\)-live ghosts. The same genuine
\(G_4,G_5,G_6,ND,N(YD)\) paid rows and first-two clean calibration
therefore hold.

Only the earlier dirty pair member may have
\(\widetilde D_i=D_i-(V/2)B_i=0\). It is then *silent in the two
compensated marked reads* no matter its physical timing; its
ordinary contributions are already in the aggregate dirty tap.
Every effective nonregular row (one with \(\widetilde D_i\ne0\))
is after the first three clean labels \(u,v,w\), by the same
\(P(V)=\mu\) contradiction at \(v\). That proof uses the actual
ordinary taps, so a silent pair earlier in the suffix does not
alter it. The \(D_v=0\) guard and its \(ND\) contradiction also
ignore only the same silent coefficient. For
\(P=Y(Y-u)(Y-v)\) remove the **whole signed pair** from
the weighted input \(bP(y)\). This input is zero through \(v\);
its genuine Volterra row in \(\langle B,D,YD\rangle\) is killed
by its strictly included values at \(j,u,v\), and hence vanishes
identically. The pivot at \(w\) now gives \(A_{ww}=0\) directly.
The undivided fourth moment and diagonal identity from the
macro packet force the same \(J=0\), whatever silent physical
stages intervened.

Between \(w\) and the fourth regular \(a\), **every effective**
nonregular row must have the same reflected numerical clock
\(z=w+M/[6(u-v)^2]\), from its genuine scalar quartic test.
Their number can be two only if an effective early pair member
shares a numerical clock with one ghost. Use the **first**
effective row to calibrate both grade-six profiles. Its diagonal
is \(z-w\) exactly as before: if the silent earlier pair member
intervenes between \(w\) and this first effective row, its three
true regular positive-power moments are zero since
\(\widetilde D=0\). On the three available distinct nonzero
regular labels this kills its \(w\) tap by Vandermonde. Hence
the Volterra entry from \(w\) to the first effective row has
no intervening \(A^2\) term even in this situation. The tap
from \(w\) is live by the same three-positive-moment test, so
the claimed diagonal follows. At \(a\), subtract \(zND\)
from \(N(YD)\): **all** possible effective terms cancel, as
they have the same \(z\), not just an assumed single ghost.
The prime-101 unit residual at the fourth row is unchanged.
After its exclusion there is no effective nonregular row
through \(a\). The first effective row before \(b\), if any,
or the \(b\)-row if none, is handled by exactly the same
two fixed quadratic determinants. A physically intervening
silent pair is already included in the ordinary dirty
aggregate and has zero compensated marked contribution.
Thus no missing timing case prevents the transfer.

## 5. Constant active cubic, one weighted exterior fourth-head label

Suppose instead that \(\beta h\) is nonzero outside the core
at exactly one numerical label. Grouped \(\beta h\) and
\(\beta h^2\) are zero at each of their at most two weighted
clock labels by the first two paid scalar moments. Thus (1)
holds. Put \(B\) equal to the weights on **all** active
dirty rows, zero elsewhere; \(G=(V^3/6)B\) as before and
\(U_0=\langle B,\beta h\rangle=\langle B,D\rangle\), since
the first true clean read forces \(D=NB\) nonzero there.
The first live nonzero \(g\)-clean reflected row has clock
\(u\ne V\) by its positive moments, and its \(D\) entry is
nonzero as above. Consequently \(u\) is the unique weighted
exterior head label. It is not the terminal (its reflected
clock is nonzero).

On this numerical fiber \(E_6\) restricts to the span of
\(1,h\), so there can be at most three physical rows there:
four would give two independent local contrasts plus the
independent core row \(B\). If there are at most two distinct
nonzero **active** \(h\) values there, the first two grouped
weighted \(h\) moments kill each separate value's ordinary
mass. There is then exactly one such value in an equal-\(h\)
signed active pair; three identical rows would already give
two local contrasts. This literal pair contrast and \(B\)
fill \(U_0\). Mask the actual signed exterior pair and the
whole active dirty part; their ordinary aggregates are zero
and their polynomial-weighted masks are in \(U_0\).
Two nonzero distinct live clean samples of the remaining
ordinary rule suffice for the same paid Hermite contradiction.

In the other case there are exactly three distinct live
nonzero \(h\) values at \(u\). The restriction of \(\beta h\)
there annihilates \(1,h\), so the pure \(u\)-supported contrast
\(D'\) is in \(U_0\) and spans it with \(B\). Outside the
core the ratios \(D_i/b_i\) on this fiber are thus a fixed
nonzero multiple of the three distinct \(h_i\). Let \(v,w\)
be the next two distinct live nonzero \(g\)-clean labels
different from \(u\) in reverse. They exist since the
clean ordinary rule has at least five non-endpoint labels
by the fixed Gram argument. At \(v\), \(D_v=0\) kills the
aggregate dirty tap; true integration through degree three
on \(\{0,u,v\}\) gives \(v=2u\). The actual quartic row is of
the form \(aB+\mu D\) with \(\mu=V(V-u)(V-u/2)\) obtained at the
first \(u\). Apply \(P=Y(Y-u)(Y-v)\) at *every* live \(u\)
row before \(w\): the true equation is
\((P(V)-\mu)D_i=b_i I P(u)\). Its denominator is nonzero
since \(u\ne V\) and \(v=2u\ne u/2\). Therefore all those
\(u\) rows have the same \(D_i/b_i\), so precisely one can
occur before \(w\). Mask that one by a multiple of \(D'\)
and remove the entire active dirty \(B\); both are
single-clock masks in \(U_0\). The inclusive two-sample
cut at \(v,w\) now gives the contradiction.

## Verification boundary

The module [DIRKOrderElevenLocalCorePivot](../../lean/RKCert/ReviewedNative/DIRKOrderElevenLocalCorePivot.lean)
checks the precise first-clean reverse contradiction on the actual
rooted-order rows, from an explicit \(U_0\) sample support and
one-clock tail. The signed support and grade band arguments above
supply those premises mathematically. The existing grouped and
paired Hermite modules supply the alternate weighted mask
contradictions, and the frozen prime-101 certificate verifies the
identical grade-six scalar closures in the four-distinct-ghost
transfer. No end-to-end Lean proof of the whole signed census is
claimed.
