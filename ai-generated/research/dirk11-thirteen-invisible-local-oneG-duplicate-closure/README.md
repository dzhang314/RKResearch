# The one-label reflected cubic cannot use an unmarked duplicate in DIRK11/13

**Result.** In the normalized characteristic-zero DIRK11/13
invisible one cubic-clock chart with zero grouped fourth head and
nonzero grouped fourth-head square, assume that the true reflected
cubic \(G\) has just one numerical support label. Its support
cannot be an unmarked two-physical-row class with \(h=0\) on both
members. This includes when its second member is unweighted and
every interleaving among the other four marked pairs. The distinct
marked-triple allocation and the other grouped support slices are
not ruled out here. The unrestricted real interval stays **13–14**.

## 1. Exact support and different reverse flag

Use the actual signed normalization and
[grouped-square census](../dirk11-thirteen-invisible-local-square/README.md).
Let \(g=Ac^2-c^3/3\), \(h=(A-\xi/2)g\), let \(\beta=b_{\rm wt}^{\mathsf T}\)
in forward chronology, and read its fourth head as the reverse
column \(\mathfrak B=\beta h\). The single unweighted dirty row \(j\)
is the first nonzero forward clock. This follows from \(C(2)\),
which gives the genuine first nonzero cubic value \(c_j^3/6\).
The actual reverse order consists of \(T\), the ordinary nonendpoint
rows, \(j\), and \(O\); if \(j\) numerically shares an ordinary
label it still has its separate later physical position.
Set \(Y=1-c\), \(N=A^{\mathsf T}\) with the actual reverse
ordering, \(W(U)=b_{\rm wt}U(Y)\), and let \(I\) be zero-constant
primitive. The true \(G=NW(Y^2)-W(Y^3/3)\) kills \(E_7\), and
\(G_j=0\) by \(Gg=0\).

The sole numerical support of \(G\), of clock \(x\ne0,1\), must
be the first nonzero weighted reverse clock: at its first
weighted row only its own diagonal contributes to the genuine
weighted first and second scalar reads, giving
\(d=x/2,\ G_i=b_i x^3/6\ne0\).
The other zero-clock prior contributors cannot affect this.
At \(x\), \(G1=0\) makes its two \(G\) entries opposite and live,
so an unweighted \(x\)-row cannot precede the first weighted
one (its genuine \(G\) would be zero before any weighted
nonzero donor). Their weights sum to the live \(\mu_x\).
Thus the second row's \(G-b_i k_{\rm first}\) is nonzero whether
its weight is live or not. At the four other nonendpoint
clocks there are weighted marked pairs with opposite distinct
nonzero \(b_i h_i\), live ordinary sums, and distinct \(h_i\).
The latter follows since equal nonzero \(h\)'s would force their
ordinary sum zero. \(G\) is zero at all their rows.
The present allocation has no other silent slots.

The paid ranks now give different reverse flags from the
multi-label \(G\) proof:
\[
 E_6^\perp=\langle G,\mathfrak B\rangle,\qquad
 Z_5=E_5^\perp\cap\{T=0\}=\langle G,\mathfrak B,Y\mathfrak B\rangle,
\]
\[
 Z_6=E_4^\perp\cap\{T=0\}
       =\langle G,\mathfrak B,Y\mathfrak B,Y^2\mathfrak B,H\rangle .
\]
The dimensions are \(2,3,5\) by the true normalized ranks and
terminal indicator. The marks of \(\mathfrak B\) are paid by
grades \(4,5,6\), and \(G\) is on a separate label; the
four distinct \(\mathfrak B\) supports make the marked
columns independent. Here \(H\) is the actual numerical
barycentric lift on the six nonterminal ordinary labels,
putting each nonendpoint mass proportionally on its physical
weights, the \(Y=1\) mass on actual \(O\), and zero at \(j,T\).
The construction and cardinal identity in the
[five-pair proof, §1](../dirk11-thirteen-invisible-local-five-pair-closure/README.md#1-actual-no-slack-ranks-companion-and-stage-chronology)
apply to this allocation as well: all nonendpoint masses
are live, grouped \(\beta h=0\), and the assigned origin has
\(h=0\). In particular \(H\) annihilates \(E_4=\mathcal
P_4+\langle g,h\rangle\) and has nonzero numerical sums,
whereas all the other displayed marks have class sums zero.
No primitive is evaluated with redistributed weights.

For degree at most three, the actual weighted primitive
error \(NW(P)-W(IP)\) lies in \(E_6^\perp\); for degree
at most four it lies in \(Z_5\). These are the usual exact
charges \(3+6+2=11,\ 4+5+2=11\) for weighted reverse
primitives. Use \(\mathcal C=YN-NY-N^2\).
For a weighted degree-three or degree-four input \(W(P)\),
\(\mathcal C W(P)\) belongs respectively to \(Z_5\) or \(Z_6\):
\(CA-AC-A^2\) maps \(E_j\) into \(F_{j+2}\) for \(j=5,4\),
and the charges are \(3+7+1=11,\ 4+6+1=11\).
The constant \(\mathfrak B\) and \(G\) terms also have
\(\mathcal C\)-image in \(Z_6\) since both annihilate \(E_6\),
and \(G\) has \(\mathcal C G\in Z_5\) since \(G\) annihilates
\(E_7\). All these images are zero at actual \(T\).

## 2. No completion before the fourth distinct clock

If a class finishes among the first two distinct nonendpoint
labels \(x,u\), apply the actual weighted primitives of
\(Q=Y(Y-x)(Y-u)\), \(YQ\), both of which have zero
input throughout that inclusive prefix. The errors have
zero sums on a completed class since every element of
\(E_6^\perp,Z_5\) has zero numerical class sums.
The live ordinary mass of that class therefore forces both
primitives to zero on its clock. At \(x\ne0\) these
are \(x^3(2u-x)/12\), \(x^4(5u-3x)/60\), and at \(u\) they
are the swapped formulas. They are incompatible. This proof
includes a second \(x\) of zero weight and uses its literal
position in the completed class.

Consequently the literal third-debut prefix is \(T,x,u,v\),
where \(u,v\) are marked first mates. Write \(P=Y(Y-u)(Y-v)\).
Scale the whole genuine cubic by the nonzero factor making
\(G_{\rm first}/b_{\rm first}=P(x)\) at the first \(x\).
We continue to call it \(G\); its support, every flag space,
and ordinary weights are unchanged. Put \(D_0=G-W(P)\),
zero on that prefix. The paid rows now have the shape
\[
 ND_0=\alpha_0G+\ell\mathfrak B-W(IP),\qquad
 N^2D_0=\alpha_2G+\rho(Y)\mathfrak B-W(I^2P), \tag{1}
\]
with constants \(\alpha_0,\alpha_2,\ell\) and affine \(\rho\).
To see the second shape, \(\mathcal C D_0\in Z_5\) is zero
on the literal prefix. The read at \(x\) (only \(G\) live)
kills its \(G\) coefficient; the distinct \(u,v\)
read kills the full affine multiplier of \(\mathfrak B\).
Therefore \(\mathcal C D_0=0\) globally; subtract the paid
\(N(YD_0)\) fit from \(Y ND_0\), using the
true \(Y IP-I(YP)=I^2P\) identity and \(YG=xG\).
At the three old rows both outputs in (1) are zero.
In particular \(\ell h(u)=IP(u)\), \(\ell h(v)=IP(v)\).
If \(\ell=0\), the two primitives vanish at \(u,v\);
since \(IP\) has zero derivative at \(0,u,v\) and already
vanishes at zero, this gives three distinct double roots of
a nonzero quartic. Thus \(\ell\ne0\).
The first \(x\) calibrates
\(\alpha_0=IP(x)/P(x),\ \alpha_2=I^2P(x)/P(x)\).

If the next row were an old completion at \(u\) or \(v\),
it has \(D_{0,i}=0\) (because \(G_i=P(Y_i)=0\)).
All actual \(ND_0\) reads would still vanish through it.
Comparing (1) on the two actual mates with unequal \(h\) would
force \(\ell=0\). If the next is the second physical \(x\),
then \(D_{0,i}=G_i-b_iP(x)\ne0\) by the live class sum.
The first-support \(-d_i^2D_{0,i}=0\) gives zero diagonal,
so both outputs of (1) still vanish. The actual
comparison at \(x\), now using \(\mathfrak B=0\) and its
live \(G-b_i k_{\rm first}\), gives
\(IP(x)=I^2P(x)=0\). These are the two fixed conditions
\[
 u+v=\tfrac65 x,\qquad uv=\tfrac3{10}x^2 .
\]
For the ordinary rule, the remaining two distinct nonendpoint
clocks would give an unknown monic quadratic factor for the
degree-five ordinary hull. Write
\(R=(Y-x)(Y^2-\tfrac65 xY+\tfrac3{10}x^2)\).
Writing the quadratic as \(Y^2-\sigma Y+\pi\), the true ordinary
degree-ten reads give
\(J_{k+2}-\sigma J_{k+1}+\pi J_k=0\), \(0\le k\le3\),
where \(J_k=\int_0^1Y^{k+1}(1-Y)R(Y)\,dY\).
The four size-three Hankel minors have exact rational gcd one
in \(x\), as checked in **projection.py**. Thus the hypothesized
second \(x\) before the fourth is impossible as well.

## 3. The fourth and the exact full degree-30 clock algebra

The next row must be the distinct fourth debut of literal clock \(z\).
Here \(G=0\), its weight and \(P(z)\) are live, and
\(D_{0,z}=-b_z P(z)\ne0\). At this first support \(\mathcal C D_0=0\)
forces \(d_z=0\), so both outputs in (1) vanish through it.
Regauge \(X=Y/z\), rescaling \(N\) by \(1/z\) and \(G,P\)
by \(1/z^3\); the previous identities remain true with
their rescaled coefficients. The fourth is now \(X=1\),
the first \(x\) is \(a=x/z\), and the fifth is \(b=B/z\)
with \(B\) its literal clock. Use \(u,v\) now for the scaled
two old marked clocks, and \(P=Xm\), \(m=X^2+rX+s\)
with roots \(u,v\). Write \(\Psi=\rho/\ell\) in this gauge.
At the three actual weighted marked debuts \(u,v,1\), (1)
gives \(IP=\ell h\ne0\) and \(I^2P=\Psi IP\).

At \(u,v\), reduce \(IP/X^2\) on the monic \(m\).
Its multiplication determinant \(s(9s-2r^2)/144\) is
live because both actual old readings are live; \(s=uv\ne0\).
Hence the unique affine \(\Psi\) is pinned by those two
readings. Exact division gives \(I^2P-\Psi IP=\Xi P\), with
\[
 \Psi=\frac{(4r^2-21s)X-rs}{5(2r^2-9s)},\qquad
 \Xi=-\frac{X[(r^2-6s)X-rs]}{10(2r^2-9s)} .
\]
Since \(P(1)\ne0\), the actual fourth gives \(\Xi(1)=0\).
Thus \(s=r^2/(r+6)\); the factors \(r,r+6,2r+3\) are live,
and in this gauge
\[
 \Psi(X)=\frac{(4r+3)X-r}{5(2r+3)},\qquad
 \Xi(X)=\xi_0X(X-1),\quad \xi_0=-r/[10(2r+3)] .
\]

The genuine ordinary five-interior hull is
\((J_5+\alpha J_4)/132\), as in the
[five-pair companion and ordinary proof](../dirk11-thirteen-invisible-local-five-pair-closure/README.md#1-actual-no-slack-ranks-companion-and-stage-chronology).
Here \(J_4=42Y^4-84Y^3+56Y^2-14Y+1\),
\(J_5=(2Y-1)(66Y^4-132Y^3+84Y^2-18Y+1)\).
Thus the actual \(u,v\) imply \(m\mid H_4\) in normalized
coordinates, where
\[
 H_4(X,z)=
 [J_5(zX)J_4(z)-J_4(zX)J_5(z)]/(X-1),\qquad
 h_4=132z^5 J_4(z)\ne0.
\]
Clear \((r+6)^2\) from the two remainder coefficients of
\(H_4\bmod m\); the first factors \(z\), the second
\(z^2(r+6)\), are live, leaving the two polynomials
**p0,p1** in **projection.py**. Their exact \(r\)-resultant
is, up to nonzero constant, \(z^{13}J_4(z)^3D_{30}(z)\),
where \(D_{30}\) is irreducible. Therefore \(D_{30}(z)=0\).
Undivided rational polynomial pseudodivisions (checked
before removing any contents, all content factors units
modulo \(D_{30}\)) yield a linear \(r\)-relation with live
leading coefficient. Thus \(r\) is the specified ratio in
the single exact base algebra of degree 30.
The monic quadratic quotient
\[
 H_4/h_4=m(X)(X^2+A_1X+A_0)
\]
retains both assignments \(a,b\) in its entire rank-60
extension; the old roots \(u,v\) are always retained by the
full \(m\)-norm when a check needs them.

## 4. No first repeat immediately after the fourth

All inputs to \(ND_0,N^2D_0\) are still zero through the
literal fourth. The actual next row can be a repeat of
one of \(a,u,v,1\) or the first fifth \(b\). These are the
four physical repeat tests:

* **Old marked return \(q=u\) or \(v\).** Its \(D_{0,i}=0\)
  but \((ND_0)_i\ne0\) by the distinct two weighted \(h\)'s
  in (1) and \(\ell\ne0\). Only the fourth contributes to
  its \(ND_0\), so \(\mathcal C D_0=0\) yields \(d_i=q-1\);
  the \(N^2D_0\) read divided by that live \(ND_0\) yields
  \(d_i=\Psi(q)\). The norm of \(\Psi(X)-(X-1)\) over the
  entire old quadratic \(m\) is an exact unit.
* **Fourth return \(q=1\).** Both possible nonzero
  \(D_0\) inputs then have the same clock 1, and
  \((ND_0)_i\ne0\) by the true weighted contrast.
  Hence \(\mathcal C D_0=0\) forces \(d_i=0\),
  and \(N^2D_0\) requires \(\Psi(1)=0\), also an exact unit.
* **Unmarked duplicate \(q=a\).** Set
  \(l_a=IP(a)/P(a), r_a=I^2P(a)/P(a)\).
  The live \(D_{0,i}\) and (1) give its divided outputs
  \(l_a,r_a\), whether this second member has a weight or
  not. Write \(T_i=N_{i,z}D_{0,z}/D_{0,i}\).
  The actual \(ND_0,N^2D_0,\mathcal C D_0\) give
  \(T_i+d_i=l_a,\ d_i l_a=r_a,\ (a-1)T_i=r_a\).
  Thus \(r_a(a-1+l_a)-(a-1)l_a^2=0\), with no division
  by \(l_a\). This is a unit on both complement assignments.

Hence the next row is consecutive distinct fifth \(b\).

## 5. The live fifth, a new commuting column, and all final returns

At the actual fifth \(G=0\). Normalize its \(ND_0,N^2D_0\)
reads by its physical weight and write
\[
 g_b=\ell h_b-IP(b),\quad j_b=\rho(b)h_b-I^2P(b)
       =\Psi(b)g_b-\Xi(b)P(b),\qquad t=b-1 .
\]
The only earlier \(D_0\) donor is fourth 1 and all earlier
\(ND_0\) is zero. Since \(D_{0,b}/b_{{\rm wt},b}=-P(b)\),
the actual identities are
\[
 j_b=d_b g_b,\qquad j_b=t(g_b+d_b P(b)).
\]
Because \(b, t, \xi_0,P(b)\) are live, the first and the
primitive relation show \(g_b\ne0\); the second gives
\(d_b\ne0\). Set \(u_b=g_b/P(b)\).
Then \(d_b(u_b-t)=t u_b\), so \(u_b-t\ne0\).
Define \(y=d_b/t=u_b/(u_b-t)\). Both \(y,y-1\) are live.
The literal quadratic is
\[
 t y^2-\Psi(b)y-\xi_0 b(1-y)=0. \tag{2}
\]
The code adjoins its **full** monic quadratic to the rank-60
ordinary algebra (rank 120), with no singular leader or branch
chosen.

The key different column is
\[
 \widehat D=-\frac{(X-1)D_0}{1-a}=G-W(\widehat P),\qquad
 \widehat P=\frac{(1-X)P}{1-a},
\]
where the equality uses \((X-a)G=0\). It vanishes through fourth
and has live \(b\)-entry \(b_{{\rm wt},b}tP(b)/(1-a)\).
Its commutator is in \(Z_6\) and zero through fourth.
The space of \(Z_6\) rows zero through that prefix is a line:
at \(a\) there is only the live \(G\) entry and the companion,
and the three distinct \(u,v,1\) live \(\mathfrak B\) reads
fix the quadratic multiplier of \(\mathfrak B\) from the
same companion coefficient. The literal \(\mathcal C\widehat D\)
at fifth equals \(-d_b^2\widehat D_b\ne0\).
Thus this line is nonzero at fifth and the zero-prefix
subspace in \(Z_6\) **through fifth is zero**.

Put \(\eta=u_b(1-a)/t\) and
\(E=ND_0-\eta\widehat D\), which is zero through fifth.
It has constant \(G,\mathfrak B\) parts and a degree-at-most-four
weighted part, so \(\mathcal C E\in Z_6\) by the same genuine
grade charges in §1. Its zero prefix through fifth now gives
\(\mathcal C E=0\) globally. There is a next literal nonendpoint
row: five further physical mates remain, and \(j,O\) both
come later. Its first-support calculation gives
\(d_i^2 E_i=0\) and therefore \((NE)_i=d_i E_i=0\),
even if \(E_i=0\); its actual earlier mate has zero
\(NE\) as well. This does not assume the next diagonal
is zero without a live nonzero coordinate.

With \(N\widehat D\) paid by \(\widehat P\) and the
\(N(XD_0)\) fit, its \(\mathfrak B\)-coefficient is
\(\ell[\Psi(X)-(X-1)]/(1-a)\); its \(G\)-coefficient
at the actual first \(a\) is
\(I\widehat P(a)/P(a)=l_a+r_a/(1-a)\).
Subtracting the two actual normalized \(NE\) reads on a
marked pair therefore gives
\[
 \Psi(q)=y(q-1)
\]
at the next marked clock \(q\). For the next actual unmarked
duplicate \(a\), two weighted mates with their live \(G/b\)
contrast, or the zero-weight live \(G\) second mate,
give instead the undivided condition \(r_a=y(a-1)l_a\).
Both follow directly from (1) and the definition of \(E\);
the passage uses the live \(u_b-t\) and no interpolation
at an unavailable later row.

For the fifth marked repeat \(q=b\), the necessary gate
\(\Psi(b)=t y\) contradicts (2) by \(\xi_0 b(y-1)\ne0\).
For the fourth repeat \(q=1\) it requires the already excluded
\(\Psi(1)=0\). For \(q=u,v\), the exact \(\Psi(X)-y(X-1)\)
norm over \(m\) is a unit in the full rank-120 model.
The last unmarked \(r_a-y(a-1)l_a\) is an exact unit there
as well. This exhausts the first literal return and
closes the chart. No restriction on the total separation of
the duplicate or on shared diagonal values was imposed.

## 6. Reproduction and transfer of the residue certificates

Run **python3 check.py --prime 103 --prime 107** with SymPy
and python-flint. The called **projection.py** checks the
ordinary zero-primitive gcd, exact primitive decomposition
and determinant, full rational \(D_{30}\) projection,
factor/clearing guards and the undivided live ratio.
The finite-free checks retain the whole complement
quadratic and fifth parameter quadratic and evaluate all
old-root tests by their full norms. The stated units at
each prime certify characteristic-zero units by the
multiplication determinant in the same monic bases over
the local coefficient ring. Denominators, leading coefficients
and all inverses used in that arithmetic are checked on
reduction. No actual tableau coefficient or embedding is
assumed prime-integral, and there is no conclusion for
the tableaux in positive characteristic. The rooted
flag/physical bridge is the written proof, not a complete
Lean HasOrder theorem.
