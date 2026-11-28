# Forward masks close the entire all-clean reverse prefix in invisible DIRK11/13

**Result.** In the normalized, actual rooted-order-eleven invisible
six-clock DIRK13 face, the remaining no-late-ghost array cannot place all
six dirty ghosts before its first nonorigin forward clean stage. In the
[prior chronology count](../dirk11-thirteen-invisible-six-no-late/README.md)
this excludes \((\alpha,\beta,\gamma)=(0,0,6)\) without any additional
support or reality restriction and leaves eight count profiles not yet
excluded. Among the remaining ones, \(\alpha=0\) also excludes both a
constant and a linear ghost cubic profile. Further exact cuts for the
other profile degrees and the constant-profile clock schedule are below.
The unrestricted numerical real stage interval is still **13–14**.

Use the established signed-census hypotheses: literal lower triangular
\(A\) of size thirteen, actual \(\mathrm{HasOrder}(11)\), forward \(C(2)\),
genuine reflected \(D(1),D(2)\), order-six surplus, and the support
\(r=0,d=z_{\mathrm{count}}=6\). There are six zero-weight cubic-dirty
rows at distinct clocks, and seven distinct clean clocks including
the literal origin and terminal. In the no-late chronology the seven
clean rows appear in reverse as
\[
 T,v,u,w,[\alpha\ \text{ghosts}],a,[\beta\ \text{ghosts}],b,
 [\gamma\ \text{ghosts}],O ,
\]
with no gaps among \(T,v,u,w\). The five non-endpoint clean clocks
are live. Here \(v,u,w,a,b\) denote **reflected** clock labels and
\(x_b=c_b=1-b\) is the nonzero forward clock of the first nonorigin
clean stage. The argument below, once this signed-skeleton and
paid-rank input is available, is over any characteristic-zero field.
It does not invoke positivity of weights, order on the coefficient
field, or a transformation to a new RK tableau.

## 1. A true forward head and its first two primitive errors

Write \(g=Ac^2-c^3/3\), \(C=\operatorname{diag}(c)\), and \(IF\)
for the formal primitive with zero constant. Let \(F_j\) be the
true zero-profile space, \(E_j\) the true rooted column space.
The census supplies \(F_4=g\mathcal P_1(c)\) and
\(F_5=g\mathcal P_2(c)\), by size and the six distinct dirty
clocks. It also supplies the \(E_6\) decomposition and the true
terminal profile:
\[
 E_6=\mathcal P_5(c)+g\mathcal P_3(c)+K e_T,\qquad
 H_T(X)=30b_T XJ_4(X),
 \quad J_4(X)=42X^4-84X^3+56X^2-14X+1 .
\]
In particular,
\[
 F_6=g\mathcal P_3(c)+K(e_T-H_T(c)).
\]
The terminal-profile vector has a nonzero nonterminal clean entry:
a degree-five nonzero polynomial cannot vanish on the six distinct
nonterminal clean labels. Thus it is independent of the four
\(g\)-polynomial columns; this is the exact dimension five, not just
a containment.

Using \(g^2\in E_6\) and its vanishing on clean rows, first compare the
six nonterminal clean clocks and then the terminal in this decomposition.
The polynomial and terminal-cardinal coefficients must be zero.
Consequently there is a unique nonzero polynomial \(U\) of degree
at most three with \(g_i=U(c_i)\) on every ghost. This relation is
specific to dirty rows; on clean rows the actual \(g\) is zero even
if one happens to share a clock with a ghost. Set
\[
 \phi=U(c)-g .
\]
This is a true grade-three column supported only on the clean rows,
with value \(U(c_i)\) there. For \(j=0,1,2\), the **actual** marked
primitive is
\[
 A(C^j\phi)-I(X^jU)(c)\in F_{4+j}.
\]
Indeed the pure-polynomial primitive error is paid at that grade,
and \(A(C^j g)\in F_{4+j}\) by the actual graded product and unary
maps. In particular both \(A\phi\) and \(A(C\phi)\) have their exact
scalar primitive values at every clean row. This does not claim
the masked array has order.

## 2. A general degree restriction at the initial ghost prefix

The initial forward ghost block contains \(\gamma\) distinct dirty
clocks after \(O\) and before \(b\). At all of them \(A(C\phi)=0\):
all inclusive ghost entries of \(C\phi\) vanish, and at the origin
the forward clock is zero. The actual grade-five shape therefore gives
\[
 I(XU)(p)+U(p)Q_2(p)=0
\]
at every prefix ghost clock \(p\), for a single polynomial \(Q_2\) of
degree at most two. If \(\gamma>\deg U+2\), this degree-bounded
polynomial vanishes identically, hence \(U\mid I(XU)\).

More generally a nonzero polynomial \(U\) over a characteristic-zero
field can divide \(I(X^j U)\) only if \(U\) is a monomial. Indeed
\(I(X^jU)/U\) has both ordinary and trailing degree \(j+1\), hence is
a scalar times \(X^{j+1}\). Comparison at each nonzero coefficient
\(U_i\) says that scalar is \(1/(i+j+1)\). Characteristic zero makes
these numbers distinct. If \(U\) has positive degree \(m\) and is
a monomial, its origin value is zero. At the first nonorigin clean
stage \(b\) the two exact marks then use only the literal diagonal,
since all physical ghost columns of \(\phi\) vanish. They force
both \(A_{bb}=x_b/(m+1)\) and \(A_{bb}=x_b/(m+2)\), impossible.

Thus every **nonconstant** profile satisfies
\[
 \gamma\le\deg U+2 .
\]
If also \(U(0)=0\) with multiplicity \(m_0\), then \(A\phi=0\)
on the same prefix. The grade-four calculation gives \(IU+UQ_1\)
of degree at most \(\deg U+1\). It is divisible by \(X^{m_0}\)
and all prefix ghost clocks are nonzero because their \(U\)-values
are individually nonzero. The quotient still vanishes at them.
Applying the same divisibility argument with \(j=0\) gives
\[
 U(0)=0,\ U\ne0\quad\Longrightarrow\quad
 \gamma\le\deg U+1-m_0 .
\]
Since \(\gamma\ge3\), the only possible zero-at-origin branch has
\(\gamma=3\), a cubic \(U\), and a simple root at zero. In particular
a nonconstant profile with \(\gamma=5\) must be cubic with nonzero
constant, and \(\gamma=6\) forces a constant.

## 3. No degree at most one for \(\alpha=0\); the six-prefix case is closed

For \(\alpha=0\) all ghosts are before the second nonorigin forward
clean \(a\). Take the true grade-five input
\[
 \psi=C(C-x_b)\phi .
\]
It vanishes at every ghost and at the two possible clean donors
\(O,b\) for a ghost; hence \(A\psi\) is zero at all six ghosts by the
inclusive DIRK cut. It is also zero at \(b\). Its actual grade-six
discrepancy is in \(F_6\) by the primitive rule in §1, and on the
ghosts gives one polynomial relation
\[
 F(X)+U(X)Q_3(X)-\eta H_T(X)=0,\qquad
 F=I[X(X-x_b)U],                        \tag{1}
\]
evaluated at the six distinct dirty clocks. Here \(Q_3\) is cubic-or-
lower and \(\eta\) is a scalar; signs are absorbed into \(Q_3\).
If \(\deg U\le2\), (1) is a polynomial of degree at most five and
is identically zero. At the clean \(b\), the actual discrepancy
and \(A\psi_b=0\) give \(F(x_b)=\eta H_T(x_b)\). Thus \(\eta=0\)
would give both \(U\mid F\) and \(F(x_b)=0\). In characteristic
zero that is impossible: \(F'=X(X-x_b)U\), \(F(0)=F(x_b)=0\);
at either anchor \(z\), \(F\) has multiplicity exactly two higher
than \(U\), including if \(U(z)=0\). But \(F/U\) has degree three
and cannot have two distinct double roots. It follows that
\(\eta\ne0\) whenever \(\alpha=0,\deg U\le2\).

If \(\deg U\le1\), the other two terms in (1) have degrees at
most four, while \(H_T\) has its genuine degree five. Comparing
the leading coefficient would force \(\eta=0\), contradiction.
Thus for \(\alpha=0\) there is no constant or linear profile at
any of the old counts. Since \(\gamma=6\) already forces constant
by §2 and has \(\alpha=0\), this proves the full exclusion of
\((0,0,6)\). The remaining count profiles are
\[
 (0,1,5),(0,2,4),(0,3,3),(1,0,5),(1,1,4),(1,2,3),
 (2,0,4),(2,1,3).
\]
These are not-yet-excluded counts, not examples. In the first
one only a cubic with \(U(0)\ne0\) remains. In the next two,
only degrees two and three remain, with the further restrictions
of §2.

## 4. Reciprocal clean profile and the finite constant chart

Use \(y=1-c,Y=\operatorname{diag}(y),N=A^{\mathsf T}\) in literal
reverse order and the genuine reflected cubic \(G\), nonzero at
every ghost and at \(v,u,w\).
The actual grade-seven annihilator satisfies \(G\in E_7^\perp\).
Multiplying it by the **true** grade-three \(\phi\) gives
\(G\phi\in E_4^\perp\): pair with an actual \(E_4\) column and
use the graded product. This row is zero on all ghosts and on
\(T\), so its clean values annihilate powers zero through four
on the six distinct nonterminal clean sites. There is just one
such direction, the clean barycentric row \(H\) of the
[late-ghost exclusion](../dirk11-thirteen-invisible-six-paid/README.md).
Scale \(H_s/b_s=h(s)=sJ_4(s)\) at the five regular non-endpoint
sites. Thus for a single scalar \(\tau\)
\[
 G\phi=\tau H .
\]
If \(\tau=0\), the three old live clean locations force \(U\) to
be cubic with exactly their forward clocks as roots. Then
\(G_a=G_b=G_O=0\). If \(\tau\ne0\), all clean nonterminal
coordinates of \(G\) and \(U(c)\) are individually live, and
\(h(s)/k_s=U(1-s)/\tau\), where \(k_s=G_s/b_s\) at the regular
five sites. In this second branch both actual paid grade-six
rows \(G_6=N W(X^5)-W(X^6/6)\) and \(N(Y^2G)\) are cubic times
\(G\) **on the clean sites**: their allowed shape globally is a
cubic times \(G\) plus a multiple of \(H\). Four clean clocks
therefore fix their complete clean profiles. One does not remove
the independent \(H\) coefficient on the ghost sites.

If \(U\) is constant, \(\tau\ne0\), and \(k_s=h(s)v^3/(6h(v))\)
at every regular site, by the literal first reverse cubic at \(v\).
The order-ten ordinary scalar rule again puts the five ordinary
interior clocks on the monic Jacobi pencil \(J_5+\lambda J_4\)
(leading coefficient \(132\)); \(J_5=(2X-1)(66X^4-132X^3+
84X^2-18X+1)\). At the first three clean rows the actual paid
reverse \(D(2)\), \(G_3,G_4,NG\) give one clock-only condition:
obtain the two positive-power taps at \(u\) from \(m_1,m_2\),
and the three at \(w\) from \(m_1,m_2,m_3\). Here
\[
 m_1(s)=s^2/2,\quad m_2(s)=s^3/3+k_s,\quad
 m_3(s)=s^4/4+L_1(s)k_s .
\]
The affine \(L_1\) comes from the actual \(v,u\) samples
\(L_1(s)=u+v-K(s)/k_s\), where \(K=I[X(X-u)(X-v)]\).
The other affine row \(NG=\Lambda(Y)G\) is fixed at \(v,u\)
by their actual tap reads. At \(w\) the first three scalar
moments solve the taps \(T_{w,r}\) uniquely, and
\[
 R(v,u,w)=\sum_{r=v,u,w} T_{w,r}k_r-\Lambda(w)k_w=0 .       \tag{2}
\]
There is no ghost earlier than \(w\), so this is an actual
marked row equation. All graph denominators are among powers of
distinct nonzero clocks, their pairwise differences, \(h(v)\),
\(k_u,k_v\), and ordinary factorial constants.

Clear those denominators in \(R\), form its multiplication norm
in the rank-\(5\cdot4\cdot3=60\) ordered-three-root algebra of the
Jacobi pencil over \(\mathbb Q[\lambda]\). This algebra is finite
free by successively adjoining a monic chosen root and deflating
the monic quintic, then degree four, then degree three. At any
characteristic-zero candidate a vanishing factor (2) forces this
norm polynomial to vanish. It is **not identically zero**:
at \(\lambda=0\) modulo \(43\) the exact five simple roots are
\(2,9,22,35,42\). All denominators used above are units there.
The product of the 60 values of \(R\) is \(4\) modulo \(43\);
clearing denominators multiplies this by a nonzero product.
Thus this is a finite set of \(\lambda\)'s, and a finite set of
ordinary clock schedules, in the constant-\(U\) subcase. The argument
does not perform any reduction of an unknown tableau or assert these
finite candidates are realized.

For constant \(U\) and \(\alpha=1\), there is a further explicit
necessary clock lift. Because \(\gamma\ge3\), the grade-five
ordinary/ghost calculation at three prefix ghosts yields
\(A(C\phi)=C^2\phi/2\) globally: the ghost polynomial is quadratic
with three roots. At any of the \(\beta\) ghosts, with only \(b\)
as a possible positive clean donor, this kills its \(b\)-tap.
Consequently
\[
 \Psi=A(C^2\phi)-C^3\phi/3\in F_6
\]
vanishes at the five ghosts before \(a\). The \(F_6\) terminal
head coefficient of \(\Psi\) is nonzero because its clean
\(b\) value is \(U x_b^3/6\ne0\) (the exact \(A(C\phi)\) at \(b\)
forces its diagonal \(x_b/2\)). Therefore these five distinct
ghost forward clocks are the full roots of
\(H_T(X)-U R_3(X)\) up to a scale. Their sum is 2, from the two
top coefficients of \(XJ_4(X)\).
The six ghost clock sum equals the six clean nonterminal forward
clock sum: for the monic hull \(S_6\) of the latter labels the
\(E_6\) shape gives \(S_6(c)=g Q_3(c)+\kappa e_T\), since its
polynomial piece of degree at most five vanishes on those six
sites. The monic \(S_6-U Q_3\) therefore has all six ghost roots
and the same degree-five coefficient as \(S_6\). The sole
\(\alpha\)-ghost's reverse clock is thus
\(x=v+u+w+a+b-2\).
The actual degree-two primitive comparison from the
[no-late cut](../dirk11-thirteen-invisible-six-no-late/README.md)
then tests at \(x\) the interpolant on \(v,u,w\) with prescribed
values \((I(XP)(s)-w\,IP(s))/k_s\), \(P=X(X-u)(X-v)\).
This is a second necessary gate on the finite clock list, not a
claim the list has been exhausted.

## 5. Reproduction and Lean scope

Run \(\texttt{python3 replay_constant.py}\) for the exact
finite-field nonzero-norm specialization. The polynomial
and actual-row Lean adapters are in
\(\texttt{RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixPrefix}\).
Its rooted declarations use the existing reviewed \(E_j,F_j\)
definitions and actual \(\mathrm{HasOrder}\); its scalar declarations
check the unweighted-ghost degree debit, two-anchor quotient
obstruction, literal diagonal contradiction, and quintic head
separation. The audit uses the pinned Lean/Mathlib 4.36.0.
The core-only
\(\texttt{RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixConstantArithmetic}\)
checks the split specialization and modular product by kernel reduction
on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1.
The full paper-to-tableau branch inventory is not yet end-to-end Lean.
