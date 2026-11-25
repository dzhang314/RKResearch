# A fixed-functional ladder from a nontorsion same-gap seed

The [two-shift elliptic criterion](../two-shift-elliptic-transfer/elliptic-transfer.md)
tests a single fixed-prefix completion. The result here is that its
nontorsion hypothesis can persist after raising both exact order and
support by one, without changing the moment functional.

**Theorem.** Fix one rational linear functional
\(L:\mathbb Q[X]\to\mathbb Q\). Suppose a genuine rational rule for \(L\)
has \(n\ge2\) distinct sites with nonzero weights, has exact order
\(n+2\) (degrees \(0,\ldots,n+1\) paid, degree \(n+2\) fails), and has
a pair whose two-shift elliptic curve is smooth and whose second
infinity point \(D\) is nontorsion. Then for every \(j\ge0\), the
**same** \(L\) has a rational rule with \(n+j\) distinct contributing
sites and exact order \(n+j+2\). At each step two sites are
replaced by three, two of which supply a smooth pencil with a
nontorsion infinity point for the next step. The weights are not
required to have one sign, and no interval condition is imposed.

## The one-step data that must persist

For the monic nodal polynomial \(P=\prod_i(X-x_i)\), write
\(C_i=L(P/(X-x_i))\), \(h=L(X^2P)\), \(k=L(X^3P)\). The two
paid shifts are \(L(P)=L(XP)=0\); the lower rule's weights are
\(C_i/P'(x_i)\), and exactness gives \(h\ne0\) by polynomial
division. In particular \(h,k,C_i\) all come from the fixed \(L\).

For the chosen pair \(u,v\) put \(\ell=v-u\), \(B=(X-u)(X-v)\),
\(H=P/B\), and \(R_u=h/(C_u\ell)\), \(R_v=-h/(C_v\ell)\).
The earlier criterion's paid cubic pencil, in physical coordinates, is
\[
 G_\tau=(X-\tau)B+R_u(X-v)+R_v(X-u),\qquad Q=HG_\tau.
\]
The corresponding normalized parameters are
\(a=R_u/\ell^2=h/(C_u\ell^3)\) and
\(b=R_v/\ell^2=-h/(C_v\ell^3)\). The model from the single-step
criterion is smooth for \(ab\ne0\) and
\(\chi(a,b)=(a+b-1)^3+27ab\ne0\); its Weierstrass equation has
the form \(Y^2=X^3+A_E X^2+B_E X+C_E\) with coefficients
polynomial in \(a,b\), origin \(O\), marked point
\(D=(0,-4ab(a-b))\), and a rational point of order three.
Over \(\mathbb Q\), Mazur's theorem restricts the rational
torsion subgroup containing this point of order three to cyclic
order \(3,6,9,12\) or \(\mathbb Z/2\times\mathbb Z/6\). Thus the exact
test is
\[
                 [6]D,\ [9]D,\ [12]D\ne O .
\]

The nonzero residues ensure \(G_\tau(u),G_\tau(v)\ne0\).
Two update identities suffice. For a new finite simple root \(x\)
of \(G_\tau\) and for the next unpaid moment,
\[
 C_x(Q):=L(Q/(X-x))=\frac{h}{B(x)},\qquad
 h_Q:=L(X^2Q)=k-(\tau+u+v)h.
\]
For the first, set \(F=G_\tau/B\) and use
\(Q/(X-x)=P(F(X)-F(x))/(X-x)\). The residue contribution is
\(-R_uC_u/(x-u)-R_vC_v/(x-v)=h/B(x)\).
For the second, \(L(X^2P/(X-i))=i^2C_i\) at either old site \(i\)
by the two paid shifts, and
\(R_u u^2C_u+R_v v^2C_v=-h(u+v)\).
In particular the new weights cannot vanish at distinct new sites.
The old cofactor at a retained site \(x_i\) is affine in \(\tau\)
with slope \(-C_i\), since the coefficient of \(\tau\) in \(Q\)
is \(-P\). The collision test \(G_\tau(x_i)=0\) also has nonzero
slope \(-B(x_i)\). The cubic has distinct projective roots at the
infinity fibre, so its discriminant excludes only finitely many
finite parameters. The exactness test \(h_Q\ne0\) excludes one
more. Together with infinity, the invalid first moves therefore
remove only finitely many points of the ordered-root curve.

## Specialization and the finite nontorsion test

Use the earlier rational identification of the Weierstrass model
with the smooth projective ordered-root curve \(E\). Let \(P_\infty\)
be its rational point \((u,v,\infty)\) in physical root coordinates.
Call its first two root functions \(x,y\).
This is the simple-pole fibre of the degree-three map, so
\(\epsilon=1/\tau\) is regular and zero at \(P_\infty\).
In its local ring, the cubic equation gives
\[
 \frac{B(x)}{\epsilon}
 =\frac{R_u(x-v)+R_v(x-u)}{1-\epsilon x}
 \ \xrightarrow{P_\infty}\ -h/C_u,\qquad
 \frac{B(y)}{\epsilon}\ \xrightarrow{P_\infty}\ -h/C_v.
\]
Also \(\epsilon h_Q/h\) is regular there with value \(-1\).
The normalized pair after replacing \(u,v\) by the three
new roots is computed on two fresh roots \(x,y\) as
\[
        a'=\frac{(h_Q/h)B(x)}{(y-x)^3},\qquad
        b'=-\frac{(h_Q/h)B(y)}{(y-x)^3}.
\]
The last identities show that \(a',b'\) extend regularly to
\(P_\infty\) and specialize **exactly** to \(a,b\), because
\(y-x\) specializes to \(\ell\ne0\). Here all applications of
\(L\) have used its original moment sequence; the open parameter
varies the new roots, not the functional.

Smoothness of the next model persists by \(a'b'\chi(a',b')\ne0\).
For nontorsion there is a finite explicit argument. Start with
\(D'=(0,-4a'b'(a'-b'))\) in the next Weierstrass model, double
it once, and then add \(D'\) successively through \([12]D'\)
using affine chord and tangent formulas. At \(P_\infty\) the
doubling denominator \(2Y(D)\) is nonzero since \(D\) is not
2-torsion. For each addition after doubling, the denominator
\(X([i]D)-X(D)\), \(2\le i<12\), is nonzero: an equal abscissa
would give \([i]D=\pm D\) in that model, contradicting nontorsion.
By induction these same rational expressions are regular at
\(P_\infty\), with the calculated affine value \([i]D\) there.
Remove their poles and the zeros of their denominators. On the
remaining open the computations are valid and \([6]D',[9]D',
[12]D'\) are affine, hence different from \(O\). Their complement
is finite: the denominators are nonzero at the specialization
point, so none vanishes identically on the integral curve \(E\).
This proves nontorsion at every rational point of that open.

Intersect this open with the finite exclusions for the first
move. The intersection is cofinite, although the limiting
point \(P_\infty\) itself is not an allowed move. The original
elliptic model has infinitely many distinct rational multiples
of \(D\). Enumerating them and testing the exact exclusions
finds an allowed ordered triple in finitely many tries.
It makes \(Q\) a genuine exact next seed with the same nontorsion
hypothesis on \(x,y\). Induction proves the theorem. The preferred
rank-free candidate from the earlier note may be tried first,
but it need not pass exactness or the next nontorsion test.

## Scope and exact replay

The hypothesis is conditional for uniform integration
\(L(X^j)=1/(j+1)\). This theorem supplies no starting uniform
seed. The known 19-site order-20 uniform rules have gap one,
not the gap two needed here, and this result does not settle
any order-20 support or stage bound.

Run `python3 verify-seed-ladder.py` in this directory
([expected output](exact-check.txt)). The unchanged exact
arithmetic checker uses a fully specified finite set of moments
of a **synthetic** rational functional. It checks exact orders
4, 5, and 6, a rational multiple with a nontorsion fresh pair,
and a failure of the preferred candidate's exactness on altered
unpaid data. Those probes are not uniform quadrature witnesses.
The proof and checks make no Lean claim.
