# Exact dense fourth-head reductions on the constant active \(d=1\) face

Use literal normalized DIRK11/13 as in the
[local-active proof](../dirk11-thirteen-local-active/README.md):
actual rooted order eleven, thirteen lower triangular physical
stages, \(C(2)\), genuine \(D(1),D(2)\), and the paid grade-six rank.
All nonzero forward cubic defects \(g\) lie at one clock \(\xi\);
their nonzero values on active dirty rows are constant.
Write \(h=(A-\xi/2)g\). By the [grouped-zero exclusion](../dirk11-thirteen-local-grouped-zero/README.md)
any remaining such active case has nonzero grouped \(\beta h\).
The reductions here use that assumption, and make no unrestricted
stage-bound change. The real DIRK11 interval remains **13–14**.

The tight eight-head case with two active dirties and no extra active
unmarked non-endpoint row is excluded, without any simple-root or
ordered-field hypothesis. More generally the surviving eight-head
two-dirty configuration has one precise reproducing-kernel anomaly;
the nine-head and three-dirty branches have explicit Jacobi
polynomial profiles. These remaining alternatives are not excluded.

## 1. The exact dense census and the fixed rational Gram

All true notation \(E_j,F_j,U_4,e_T,H_T\) is as in the local-active
note. In particular \(U_4=\langle g,h,Ch,C^2h\rangle\) has dimension four
in \(F_6\), \(H_T=30 b_T X\Phi_4\), and the true terminal residual is
\(e_T-H_T(c)\in F_6\). Neither \(g\) nor \(h\) is nonzero at the actual
physical endpoints. Let
\[
 \omega(X)=X(1-X),\qquad
 J_4=\Phi_4,\qquad J_5=(2X-1)(66X^4-132X^3+84X^2-18X+1).
\]
The Gram matrices of \(\int_0^1 \omega P Q\) on each fixed polynomial
degree here are nonsingular over the rationals (positive definite
there), and therefore remain nonsingular over every
characteristic-zero field. The same exact integral is used with
arbitrary field coefficients. We use
\(\int\omega J_4=0\) and \(\int\omega J_4^2=1/330\), and the fact
that \(J_4,J_5\) span the degree-five polynomials orthogonal
against degree at most three. The latter follows from the
fixed Gram rank and their exact rational orthogonality.
Also \(\gcd(J_4,J_5)=1\) as in the earlier macro certificate.

The active dirty values have one common nonzero \(g\), so their
ordinary aggregate and their \(h\)-weighted aggregate both vanish,
by the paid \(\beta g=0,\ \beta gh=0\). Thus every nonzero grouped
\(\beta h\) label contains at least one actual **nondirty** live
head row with \(h\ne0\). The row \(\beta h\) kills all true
scalar degrees \(0,\ldots,6\), so its nonzero grouped label count
is at least eight. With two actual endpoints and at least two
dirty actives, the number \(k\) of active dirty rows is two
or three, and the nonzero grouped-head count is eight or nine.

* If \(k=3\), exactly eight nondirty active head rows are present
  at distinct labels, and there is no spare physical row.
* If \(k=2\) and the grouped-head count is nine, there are exactly
  nine such head rows at distinct labels and no spare row.
* If \(k=2\) and the grouped-head count is eight, there are either
  eight distinct nondirty heads and one spare physical row, or
  nine nondirty heads in eight labels, exactly one of them doubled
  and with nonzero weighted head aggregate. A canceled extra label
  cannot occur with only one spare physical row.

For \(k=2\) the two dirty weights are opposites and their actual
\(h\) values agree (from the vanishing dirty \(h\)-weighted
aggregate). Their \(h^2\) mass is therefore zero, regardless of
the number or values of unweighted ghosts. For \(k=3\), if the
active dirty \(h\) values were equal, its dirty \(h^2\) mass would
also be zero. The direct Gram test in the next section would then
exclude this tightly counted configuration. If any two different
dirty \(h\) classes occur, the two signed sums in \(1,h\) would
require at least two physical members of each class. Thus the
remaining \(k=3\) chart has three distinct \(h\) values and
nonzero signed dirty \(h^2\) mass.

## 2. Eight grouped heads, two active dirties: exact rank-one anomaly

On the eight distinct grouped-head labels \(S\), let \(W\) be their
monic nodal hull. Write \(\alpha_x\) for their actual grouped
\(\beta h\), and \(\eta_x\) for the nondirty \(\beta h^2\) aggregate.
Then
\[
 \alpha_x=\lambda/W'(x),\qquad
 U(x)=\eta_x/\alpha_x,\qquad x\in S,\qquad \deg U\le4
\]
for a common \(\lambda\ne0\) and a polynomial \(U\).
The first assertion is the eight-point barycentric null line;
the second uses the true \(\beta h^2\) moments through degree two.
In detail interpolate the displayed values to degree at most seven;
the reads at degrees zero, one, two kill its coefficients of degrees
seven, six, five successively by the Lagrange leading-coefficient
identity. At any singleton nondirty head label \(U(x)=h_x\ne0\).
There are at least seven such singleton head labels, so \(U\ne0\).

For \(P\in\mathcal P_4\), the original ordinary read of
\(\omega U P\) is paid, and the original \(\beta h\) read
of \(\omega P\) is zero. Compare the two. The actual endpoints
do not contribute (even if their numerical labels coincide
with other rows), and the dirty part contributes zero by its
two aggregate mass identities. At a singleton head the
difference is zero. Therefore only the one spare physical
slot can contribute a discrepancy:

* If there are only eight physical head rows, the spare must
  be a **live nondirty** \(h=0\) row at a non-endpoint numerical
  label \(q\), and there \(U(q)\ne0\); otherwise there is no
  discrepancy and the nonsingular Gram gives \(U=0\).
  Its discrepancy is \(C=b_q U(q)\ne0\). This formula also
  holds if it shares a clock with a head row.
* If there are nine physical heads in eight labels, let \(q\) be
  the doubled label. Its discrepancy is
  \[
   C=\mu_q U(q)-\alpha_q
     = b_1 b_2(h_1-h_2)^2/\alpha_q
  \]
  with the actual two head rows at that label, and \(\mu_q=b_1+b_2\).
  If it were zero or \(q\) were an endpoint, the same nonsingular
  Gram would be contradicted. Thus these two live \(h\) values
  are distinct, and \(q\ne0,1\). No division by \(\mu_q\) occurs.

The exact surviving equation is
\[
 \int_0^1 \omega(X) U(X)P(X)\,dX
     = C\,\omega(q) P(q)\qquad\text{for every }\deg P\le4 .           \tag{1}
\]
This is a fixed rank-one Gram statement, with no assumption of simple
virtual roots of \(U\). In particular a tight eight-head chart with any
unweighted spare row (dirty or clean) is excluded. All remaining
slots are active apart from the potentially unweighted actual
endpoints, and \(g\) is physically constant on its dirty support.
Equation (1) identifies \(U\) as a nonzero scalar multiple of the
fixed degree-four \(\omega\)-reproducing kernel at \(q\).
If \(\deg U\le3\), the tests \(P=(X-q)Q,\ \deg Q\le3\),
force \((X-q)U\) proportional to \(J_4\).
Thus in this case \(q\) is a fixed root of \(J_4\) and \(U\)
has degree exactly three.

## 3. Check both actual terminal residual choices in the eight-head chart

If \(e_T-H_T(c)\in U_4\), then \(H_T=XJ_4\) from its terminal
entry, and the actual terminal equation reads
\(e_T=H_T(c)+\delta g+L_2(c)h\). On the seven or more singleton
head labels this gives \(H_T+L_2 U=0\), an exact polynomial
identity of degree at most six. At the anomalous nondirty
slot of §2 (either one \(h=0\) row or two different \(h\)
values at the same nonterminal label), \(H_T(q)=0\).
Hence \(J_4(q)=0\). The reproducing kernel at such \(q\)
has degree at most three, by testing \(P=J_4\) in (1);
indeed \(J_4\) spans the degree-four orthogonal complement
to degree at most three. The preceding identity then forces
\[
 U\ \propto\ J_4/(X-q),\qquad L_2\ \propto\ X(X-q).
\]
This is the exact remaining shared-root terminal chart,
not a contradiction from residue support of lower degree.

If \(e_T-H_T(c)\notin U_4\), then the genuine \(E_6\)
decomposition is \(\mathcal P_5(c)+U_4+K e_T\).
The literal \(c^6\) column gives the monic sextic
\(M(c)=\delta g+Q_2(c)h+\kappa e_T\). On seven or more
singleton head labels this gives \(M=Q_2U\) identically.
Therefore \(\deg U=4,\deg Q_2=2\). The anomaly \(q\)
is a root of \(Q_2\): in the doubled-head case compare the
two actual \(h\) values; in the \(h=0\) spare case
\(M(q)=0\) and \(U(q)\ne0\). From the true origin
\(M(0)=0\), if \(U(0)\ne0\) this gives \(Q_2\propto X(X-q)\).
If \(U(0)=0\), write \(U=X R_3\). The tests
\(P=(X-q)Q\), \(\deg Q\le3\), now show that
\((X-q)R_3\) is proportional to the degree-four
\(X\omega(X)\)-orthogonal polynomial \((J_5+J_4)/X\).
Thus \(q\) belongs to the fixed quartic's root set in this
exceptional origin subcase. These are necessary exact
conditions on a viable anomaly, not a tableau construction.

## 4. The exact nine-head envelope

With nine distinct nondirty heads, two dirty actives are
forced. Write \(W_9\) for the monic head hull. The first
seven head moments give
\[
 \alpha_x=L(x)/W_9'(x),\qquad \deg L\le1,\qquad L(x)\ne0
 \ \text{at every head}.
\]
The next three true \(h^2\) reads give
\(P_5(x)=L(x)h_x\) on the heads for a polynomial
\(P_5\) of degree at most five (interpolation leading
coefficient as above). Test the ordinary rule against
\(\omega P_5 Q\) for \(\deg Q\le3\).
At heads the masses times \(P_5\) are \(L^2/W_9'\), so
the read vanishes since \(L^2\omega Q\) has degree at most
seven. The dirty pair cancels, endpoints disappear,
and the ordinary test is paid. Thus \(P_5\in\langle J_4,J_5\rangle\).

If \(L\) divides \(P_5\) and the quotient has degree at most four,
then the head amplitude is a polynomial \(U_4=P_5/L\) and
the test \(\omega U_4 Q\), \(\deg Q\le4\), is again paid and
zero (since \(L\omega Q\) has degree at most seven). This is
impossible. Thus constant \(L\) requires degree-five \(P_5\),
and nonconstant \(L\) is coprime to \(P_5\).

* In the terminal-in-\(U_4\) alias, the nine head labels give
  \(XJ_4 L+L_2 P_5=0\) identically. Constant \(L\) forces
  \(P_5\propto XJ_4\), not in the Jacobi pencil (test
  \(Q=X^3\)). For nonconstant \(L\), degree-five \(P_5\)
  is coprime to \(J_4\) and cannot divide \(XJ_4L\), as
  at most one of the four simple \(J_4\) factors could be
  lost upon dividing by the affine \(L_2\). Thus the only
  remaining alternative is \(P_5\propto J_4,\ L_2\propto X L\)
  with \(L\) affine nonconstant.
* In the other alias, the literal sextic identity gives
  \(M L=Q_2 P_5\). If \(L\) is affine nonconstant then
  comparison of degrees forces \(\deg P_5=5,\deg Q_2=2\)
  and \(L\mid Q_2\). If \(L\) is constant, degree-five
  \(P_5\) is already forced and \(\deg Q_2=1\).
  Thus in either case \(M\) is a degree-five Jacobi pencil
  element times an affine factor.

## 5. Three active dirties: the exact shifted-head polynomial

Here there are exactly eight singleton nondirty heads. The dirty
\(h\) values cannot all be equal, since then the preceding tight
eight-head direct Gram argument has no anomaly and contradicts
nonsingularity. They are three distinct values, and the signed
dirty \(h^2\) sum is nonzero by the three-by-three Vandermonde.

Let \(W\) be the eight-head nodal hull. The paid \(\beta h\)
moments still give \(b_x h_x=\lambda/W'(x)\), the dirty
\(h\) mass being zero. A polynomial \(R\) of degree at most
five satisfies \(R(x)=(x-\xi)h_x\) at all eight heads.
Indeed the two tests \(1,X\) for \(R\) against the barycentric
row follow from the true \(h^2\) moments against
\((X-\xi)\) and \(X(X-\xi)\), which kill the extra dirty
\(h^2\) mass. They kill the top two interpolation coefficients.
This argument works also when \(\xi\) is itself one of the
ordinary head labels, without a division by \(x-\xi\).
The ordinary tests \(\omega R Q\) for \(\deg Q\le3\)
are paid and zero, since the head numerator is
\(\lambda (X-\xi)\omega Q\) of degree at most six.
Thus \(R\in\langle J_4,J_5\rangle\).

* In the terminal-in-\(U_4\) alias, varying \(h\) on the three
  equal-\(g\) dirty rows forces \(L_2(\xi)=0\).
  Write \(L_2=(X-\xi)L_1\); the head tests yield
  \(XJ_4+L_1R=0\) identically. Degree-five \(R\) would force
  a constant \(L_1\) and the disallowed \(R\propto XJ_4\);
  hence \(R\propto J_4\) and \(L_2\propto X(X-\xi)\).
  If \(\xi\) is a nondirty head label then also \(J_4(\xi)=0\).
* In the other alias, varying \(h\) on the actual dirty
  rows gives \(Q_2(\xi)=0\). Write \(Q_2=(X-\xi)Q_1\).
  The eight scalar head identities give \(M=Q_1 R\)
  exactly, so \(R\) has degree five and \(Q_1\) is affine.
  This includes the possible coincidence \(\xi\) with a
  nondirty head without any pole division.

This proof uses only paid order and support for the reductions.
The shared-root and other dense skeletons left by these
identities require additional literal chronology and mixed
tree conditions. The companion scalar Lean file checks the
exact duplicate mass correction; the polynomial head
interpolation and Gram arguments are written mathematics.
