# Quadratic carrier with an early ghost: no monomial old fit

**Results.** In the normalized invisible-six, no-late DIRK11/13
census with a degree-two forward carrier \(U\), if \(\alpha\ge1\)
then the old quadratic-or-lower transverse fit \(m\) is not a
monomial. This covers both early-gap counts over every
characteristic-zero field. The unrestricted real stage interval
stays **13–14**.

The actual rooted-order, signed-census, and first reverse gap
notations are those of the [zero first diagonal](../dirk11-thirteen-invisible-six-alpha1-five-zero/README.md)
packet. Reflect clocks by \(Y=1-c\), write \(V=1-a,\ B=1-b\)
for the fourth and fifth regular reverse clocks, and let
\(R(Y)=Y^3+c_2Y^2+c_1Y+c_0\) be the old three-site reverse hull.
The first and second ordinary **forward** sites are \(b,a\).
The forward carrier is quadratic, not the old \(m\) in reverse.
Those degrees are unrelated a priori.

Reciprocal clean support \(G\phi=\tau H_{\rm bary}\) shows
\(\tau\ne0\) for quadratic \(U\), since otherwise all three
distinct old roots would be roots of \(U\). Thus all nonterminal
clean carrier and reverse cubic values are live. Normalize the
reverse head so \(\tau=1\), retaining the same normalization
for the true \(H_{\rm bary}\). On ordinary regular sites
\(k_y=G_y/b_y=h(y)/U(1-y)\) with \(h(y)=yJ_4(y)\).
Use \(P=Ym,\ P_0=YR\), and the true literal first reverse ghost
\(z\) satisfying \(l(z)=w_0(z)=0\), where
\(l=IP/P\), \(w_0=IP_0/P\) are reduced in the old cubic.

## 1. A monomial pins the first clock and one old coefficient

If \(m\) is proportional to \(Y^k,\ k=0,1,2\), then
\(l=Y/(k+2)\), so \(z=0\) (the numerical terminal reverse clock,
but a distinct physical row). To apply \(w_0(0)=0\), use the
first coefficient of the adjugate of \(Y^k\)-multiplication
applied to \(IP_0/Y\bmod R\). The three numerators are
\[
 -c_0c_2/20,\qquad -3c_0^2/10,\qquad -c_0^2c_1/6 .
\]
They follow by the ordinary monic cubic remainder operation;
the \(Y^k\) multipliers are live on the old sites. Thus \(k=1\)
is impossible, \(k=0\) requires \(c_2=0\), and \(k=2\)
requires \(c_1=0\).

Using the forward ordinary Jacobi quintic, deflate first at \(a\)
and then at \(b\) and reflect the old cubic. If \(D=132J_4(a)\)
and \(C_2,C_1\) denote the scaled \(X^2,X\) coefficients of
the deflated old forward cubic, the two equations are precisely
\(C_2+3D=0\) and \(C_1+2C_2+3D=0\). The resultant of each
equation with the \(b\)-quartic has a single primitive
degree-twelve factor in \(a\) besides \(J_4(a)^2\) or \(J_4(a)^3\),
respectively. The \(J_4(a)\) factor is impossible by coprimality.
The first equation in \(b\) is linear; for the second use the
separate linear cofactor, whose pivot is a residue unit at 101.
Each projection is exact over \(\mathbb{Q}\).

In the recovered clock field, the normalized quadratic forward
carrier is determined up to scale: its reverse polynomial
\(U(1-Y)\) is proportional to \(J_4(Y)/Y^k\bmod R\),
as it agrees at all old sites and has degree at most two.
For \(k=2\), \(Y^{-2}=-(Y+c_2)/c_0\bmod R\) since \(c_1=0\).
The replay therefore may use \(J_4(Y)\) or \(J_4(Y)(Y+c_2)\)
reduced modulo \(R\), then reflects to obtain \(U\).
Any scaling of \(U\) used here is matched by inverse scaling
of \(G\) in the reciprocal normalization.

## 2. The \(\alpha=1\) tail hull, including its zero multiplier

Let \(\phi=U(c)-g\), \(H=XJ_4(X)\) in forward coordinates,
\(V_b=C(C-b)\phi\), \(F_b=I[X(X-b)U]\), and
\(K_b=F_b-rH\) where \(r=F_b(b)/H(b)\). The true \(F_6\)
error has the form
\[
 K_b+UQ_3=\nu R_5
\]
on the scalar polynomial level: both \(AV_b\) at \(b\) and
all its inclusive donor entries at the five ghosts before \(a\)
are zero. The polynomial has degree at most five, so it is
exactly a scalar multiple of that hull \(R_5\), including \(\nu=0\).
There is just one late forward ghost, with forward clock
\(\xi=1-z\). At this physical ghost the actual masked row gives
\[
 A_{\xi,a}\,a(a-b)U(a)=\nu R_5(\xi),
\]
where the left hand side means the tap from the physical clean
stage \(a\), even if their numerical clocks coincide.

If \(\nu=0\), that tap is zero. Thus in the genuine reverse
inclusive row for \(V\) the only possible pre-\(V\) ghost has
zero tap. Its weighted/cubic moment equations, not its physical
chronology, now give exactly the three unordered marks of the
[quadratic closure](../dirk11-thirteen-invisible-six-quadratic-closure/README.md).
The other requirements of that finite proof also hold: the
\(F_b-rH\) identity factors \(X(X-b)U\) with affine quotient
as in the original macro, \(r\ne0\) by the same two-anchor
degree argument, and \(d_a\) is that quotient evaluated at \(a\).
The grade-seven mark \(C(C-a)(C-b)\phi\) vanishes under \(A\)
at both clean anchors and all six ghosts because possible
nonzero clean donors are only \(O,b,a\), all killed. This
retains the second prefix mask of the earlier macro.
No other step of that exclusion requires the late ghost to be
physically absent. Hence the **entire** \(\alpha=1\) quadratic
\(\nu=0\) branch is impossible, including mixed old \(m\).

Otherwise \(\nu\ne0\). As \(U\) is quadratic the true \(E_6\)
six-root relation gives \(R_6=S_6-UQ_3^*\), where
\(S_6=XT_5\) in forward coordinates. Comparing both
relations in the quadratic quotient,
\((X-\xi)K_b\bmod U\) is proportional to \(S_6\bmod U\).
Here \(\xi=1\) in the monomial chart. The resulting
two-coordinate determinant is a unit in each full
degree-twelve clock algebra modulo 101.

## 3. The \(\alpha=2\) actual commutator

There are two distinct first-gap ghosts \(z,w\) and the true
quartic \(w_0\) is a genuine quadratic with those roots.
This determines \(w=-[Y]w_0/[Y^2]w_0\) in the monomial
chart, since \(z=0\). Its leading coefficient is known live
even before the residue check.

Use the actual commutator \(\mathcal R=CA-AC-A^2\).
Its adjoint applied to the degree-four weighted input \(W(P_0)\)
belongs to \(Z_6\), by the same paid \(4+6+1=11\)
[commutator pairing](../dirk11-thirteen-invisible-six-cubic-zero-two/README.md).
Write it \(GQ+\theta H_{\rm bary}\) with \(\deg Q\le3\).
It vanishes at all old rows and both early ghosts: every
inclusive \(W(P_0)\) donor is zero. At the old rows this
forces \(Q=-\theta U(1-Y)+\mu R\) as a polynomial.
At both ghosts it forces
\(\mu R(y)=\theta U(1-y)\), since the ghost \(G\) is live
and \(H_{\rm bary}\) is zero. At \(V\) the *only* nonzero
weighted \(P_0\) donor is itself, and the commutator diagonal
is \(-d_a^2\). The reciprocal relation cancels \(\theta\)
there, leaving \(\mu k_V R(V)=-d_a^2 P_0(V)\).
Thus \(\mu=-d_a^2 V/k_V\) and the necessary equation is
\[
 d_a^2\{R(z)U(1-w)-R(w)U(1-z)\}=0 .
\]
Here \(d_a=K_b(a)/(a(a-b)U(a))\) by its literal forward
grade-six read. No division by \(d_a\) or by \(R(z)\)
takes place, so this also retains the zero-\(d_a\) and
old-clock-contact cases. This signal too is a unit in each
degree-twelve clock algebra modulo 101.

## 4. Reproduce

Run **python3 replay.py** with SymPy and sibling arithmetic
sources; an isolated layout can use **--research PATH**.
The script verifies the exact ordinary factorization, checks
both good reductions in each rank-twelve algebra, and
individually multiplies every used inverse to one.
All residue arithmetic lifts through the prescribed
finite-free clock algebras; no unknown tableau is reduced.
The native scalar zero-diagonal and one-late supported-tap
identities are supplied by **DIRKOrderElevenInvisibleSixEarlyGhost**.
The scoped root ingress and exact finite reductions are
written/source proofs, not a new native numerical endpoint.
