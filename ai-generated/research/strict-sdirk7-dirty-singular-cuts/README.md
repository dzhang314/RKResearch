# Rational helper recovery and exact exclusions in the dirty six-active chart

This packet concerns the genuinely cubic-dirty nine-stage order-seven
strict SDIRK chart with the first three output weights zero and six
distinct nonzero-weight tail clocks. The [prior structural gate](../strict-sdirk7-unpaid-head/README.md)
shows that an unpaid rational head under this mask must enter the
dirty chart. Work in normalized reciprocal-diagonal time \(z=1/\gamma\).
In the reflected tail order use coordinates \((a,b_*,c,v,u,1)\);
\(h\) is the third ghost's reflected clock. The two reverse
branches are \(v=4-u\) (reflection) and \(v=2u-1\) (arithmetic).

The results below exclude specific chronological and algebraic fibers,
not general rational nine-stage methods:

- \(u=2\) or \(3\) is impossible even over a characteristic-zero
  field, given the actual normalized dirty reverse interface.
  In the remaining rational chart the last four active columns
  of the four reverse reads necessarily have full rank.
- In the reflection branch over the rationals, \(h\) cannot
  equal \(a\) or \(b_*\), at any allowed \(u\). At \(u=0\) or \(4\)
  **all** six ghost/active aliases are impossible, including
  \(h=c\) and terminal coincidences.
- In the reflection branch, if \(h\) is distinct from all six
  active clocks, the three early active clocks cannot form a
  symmetric triple about \(z/2\), **in any physical order**.
  Both the helper tap and terminal \(u\) were free.
- Freeing the helper avoids an extra algebraic extension
  whenever a rational clock core is found and the scalar
  assembly pivots are nonzero. No such new core was found here.

## Singular terminal suffixes and the unit suffix minor

Write \(\beta\) for the six active weights, \(B\) for their
normalized lower triangular block with diagonal one, \(Y\) for
the reflected clock, and \(D\) for the second adjoint error.
Use rowwise multiplication when writing a function of \(Y\).
The old dirty chart supplies
\[
 \beta B=\beta Y,\quad
 (\beta Y)B=\beta Y^2/2-D,\quad
 DB=D\bigl(1+\theta(1-Y)\bigr),\quad
 \theta=\frac1{u^2-4u+2}.
\]
It also supplies the third reverse row
\((\beta Y^2)B=\beta Y^3/3+f(Y)D\), where
\(f(y)=-4/3+(2\theta-2)(y-1)/3\).
Here \(D\) in the displayed block equations is restricted to the
tail. Its missing ghost entry \(\delta=D_3\) at \(h\) contributes
to the homogeneous moments: \(\delta h^j+D Y^j=0\) for \(j\le4\).

The last and penultimate ratios are \(D_9/\beta_9=-1/2\)
and \(D_8/\beta_8=L_2(u)=u^2/2-2u+1\).
At \(u=2\), the row \(E=D+\beta Y/2\) satisfies \(EB=E Y/2\).
If \(E\ne0\), its last nonzero physical coordinate has \(y=2\)
by lower triangularity and diagonal one. The sole such coordinate
is the penultimate, which already has \(E=0\).
Thus \(D=-\beta Y/2\).
At \(u=3\), \(E=D+\beta/2\) satisfies \(EB=EY\) (here
\(\theta=-1\)). Its last nonzero coordinate would have \(y=1\),
necessarily the final physical stage where \(E=0\). Thus
\(D=-\beta/2\). The first three \(D\)-moment equations now
give respectively \(\delta=z/4,h=2z/3,z^3=0\), or
\(\delta=1/2,h=z/2,z^2=0\), both contradictions.

For the suffix minor, set \(M=u^2-4u+2\) and
\(T=u^3-7u^2+10u-2\), both nonzero over \(\mathbb Q\).
The third terminal ratio is \(D_7/\beta_7=L_2(u)\) in
the reflection branch and
\[
 \frac{L_2(u)(4u^3-24u^2+39u-17)}{T}
\]
in the arithmetic branch. Substitute the first reverse read to
eliminate one tap, then the second to solve the tap toward \(u\).
The fourth read has coefficient
\(-(u-3)(u-2)^2/(2M)\) in the third ratio in the reflection
branch, or \(-T/(2M)\) in the arithmetic branch; the denominators
and coefficients are nonzero at the distinct allowed clocks.

Let \(Q_2\) interpolate the three terminal ratios. In physical
column \(c\) the first three reverse reads specify the three
weighted moments of the later taps (degrees zero through two).
If \(D_6/\beta_6=Q_2(c)\), the fourth read, after these moments
are substituted, would give the vanishing of
\[
 \frac{2(c-u)(c-1)(c+u-4)}{3M}
\]
in the reflection branch, or a nonzero scalar multiple of
\[
 (c-u)(c-1)(c-(2u-1))(u-3)(u-2)^2(u-1)^3
\]
in the arithmetic branch. Distinctness and the preceding \(u=2,3\)
exclusion rule both out. Since all active weights are nonzero,
the weighted Vandermonde determinant proves the four reverse
rows have a nonsingular restriction to \(c,v,u,1\).
The exact scalar identities are replayed in
[check-suffix-rank.py](check-suffix-rank.py).
The actual normalized reverse-interface exclusion of \(u=2,3\)
is kernel-checked in
[SDIRKSevenDirtySingularSuffix.lean](../../lean/RKCert/Research/SDIRKSevenDirtySingularSuffix.lean).

## Shared ghost and active clocks

Suppose \(h=y_i\) for one active coordinate \(i\). After grouping
the ghost error \(\delta\) with \(D_i\), the resulting six-site
row kills degrees zero through four. Hence it equals
\(\kappa/P'(y)\) at every site, for the full nodal polynomial \(P\).
It is nonzero because at least one of the last two physical sites
is not matched by the ghost and has nonzero \(D\).

Write \(K_y=I_z(P(X)/(X-y))\) and
\(I_z(X^j)=z^j/(j+1)\). An unaliased site has
\(D_y/\beta_y=\kappa/K_y\).
The visible cubic column is proportional to \((Y-h)D/\beta\):
both weighted versions annihilate the five-dimensional visible
cubic stage space. It vanishes at the alias and is nonzero at
all other active sites. The weighted form on those other five
coordinates is nondegenerate; the four clock powers through
degree three have one-dimensional orthogonal complement
spanned by this isotropic column. The restricted four-by-four
Gram matrix is therefore singular. Subtracting the aliased
rank-one mass from the invertible uniform Hilbert Gram matrix
gives the necessary Christoffel weight
\[
 \beta_h=\frac1{1+3(2h/z-1)^2+5(6(h/z)^2-6h/z+1)^2+
                     7(20(h/z)^3-30(h/z)^2+12h/z-1)^2}.
\]

### Any reflection with the first or second active clock aliased

In the reflection branch put \(\rho=u(4-u)\), and let \(L\)
be the monic cubic with roots \(a,b_*,c\).
Set \(I_j=I_z(X^j L)\). If the ghost is aliased to either of the
first two active clocks, all last three sites are unaliased.
Their ratios give \(K_u=K_v\) and \(M K_u+K_1=0\).
With \(\rho\ne3\), subtraction gives \(I_1=I_0\) and
\(I_2=2I_0\); quadrature then gives \(I_3=6I_0\).
The fourth reverse read also applies to an *unaliased* \(c\).
With \(F_2=L/(X-c)\) and \(R_3=(X-1)(X^2-4X+\rho)\),
it simplifies to
\[
 R_3(c)\, I_z\bigl((X^3-9X^2+18X-6)F_2\bigr)=0.
\]
For example, substitute
\(K_c=I_0(c^2-4c+1+\rho)+R_3(c)I_z(F_2)\) and
\(\kappa=MI_0/2\) into the fourth reverse equation, and
use the identity
\[
 (c^3-9c^2+18c-6)(c^2-4c+1+\rho)
 +(2+\rho)c+6-5\rho
 = R_3(c)(c^2-8c+11).
\]
Since the three terminal nodes differ from \(c\), this is the
prior rootless Laguerre bridge together with its three Laguerre
moments. The new
[SDIRKSevenDirtyEarlyAliases.lean](../../lean/RKCert/Research/SDIRKSevenDirtyEarlyAliases.lean)
checks this scalar ingress and uses the published exceptional
branch theorem. The preceding tableau-to-alias reduction is
mathematical; it is not an extra native theorem about all methods.

### All aliases at terminal set \(\{0,1,4\}\)

For \(u=0\) or \(4\) in the reflection branch the terminal set
is the same. Both paired ratios at 0 and 4 are one, the ratio
at 1 is \(-1/2\), and for an unaliased \(c\) the fourth read is
\[
 (c^3-9c^2+18c-6)K_c+2(c+3)\kappa=0 .
\]
For \(h=0,1,4\), quadrature, the remaining terminal ratios,
and the Christoffel value at the alias give three linear
equations for the coefficients of \(L\). Recover \(L\) and
eliminate \(c\) between \(L(c)=0\) and the displayed fourth read.
The nonlinear projection factors have respectively degrees
\([3,3,9]\), \([2,3,6,18]\), and \([2,3,6,18]\).
The only rational Cramer/projection poles besides zero are
\(z=2\) for \(h=1\) and \(z=8\) for \(h=4\). At each the
three linear equations have a literal left-null contradiction,
so no determinant branch is lost.

For any early alias, including \(h=c\), all three terminal
ratios instead determine \(L\) with the three Laguerre moments.
Eliminate \(h\) from the root equation \(L(h)=0\) and its
Christoffel mass equation, without needing the fourth read at
the aliased site. The projection has only a zero rational root;
its nonlinear factors have degrees 3 and 15 and are
projectively rootless modulo 17 and 11 respectively.
[check-zero-penultimate-aliases.py](check-zero-penultimate-aliases.py)
verifies the determinant exceptions, exact factor products,
and all finite rootlessness receipts.

## The whole symmetric-early fiber, with either tap and terminal free

Now assume the reflection branch with no ghost/active alias.
The earlier active triple has the form
\[
 \{m-d,m,m+d\},\qquad m=z/2,\quad p=d^2 ,
\]
and any of its nodes can occur in physical position six.
No assumption is made about the helper tap or rational value of \(u\).

Let \(L(X)=(X-m)((X-m)^2-p)\),
\(R_3(X)=(X-1)(X^2-4X+\rho)\), and \(P=R_3 L\).
Symmetry gives \(I_0=0\), \(I_2=z I_1\),
\(I_1=z^4/80-pz^2/12\), and
\(I_3=13z^6/1120-3pz^4/40\). The quadrature equation solves
\[
 p=
 \frac{13z^4/1120+(\rho+4-5z)z^2/80}
      {3z^2/40+(\rho+4-5z)/12}.
\]
At a zero denominator the numerator would instead be \(z^4/2800\),
so that exceptional branch is impossible.

For distinct \(h\), the affine error numerator \(W\) has
\(W(y)=L_2(u)[(y-h)J+((4-y)h-\rho)F]\), where
\(F=I_1-I_0\), \(J=I_2-I_1\). In particular \(F\ne0\) because
\(W(h)\ne0\) (the ghost error is nonzero). The last terminal
ratio therefore forces
\[
 (3-\rho)\bigl((4-z)h-(\rho+2-z)\bigr)=0.
\]
The case \(z=4\) would force \(\rho=2\), impossible over
the rationals; otherwise it gives \(h=(\rho+2-z)/(4-z)\).
This expresses both \(p,h\) rationally in \(z,\rho\), without
fixing \(\rho=u(4-u)\).

For the fourth reverse condition use the scalar
\(L_3(c)+2[4+(4/M-1)(c-1)]D_c/\beta_c=0\)
with \(M=2-\rho\).
For isotropy, let \(K\) be the divided-difference moment
polynomial of \(P\). On the six nodes \(v(y)=W(y)/K(y)\).
The sum \(\sum_y W(y)^2/(K(y)P'(y))\) is the coefficient of
\(X^5\) of \(W^2/K\bmod P\). Multiplication by \(K\) is
invertible in this residue algebra because every weight is
nonzero. Thus append \(W^2\) to the five multiplication columns
from \(1,X,\dots,X^4\); its determinant must vanish.
The replay uses a uniform pseudo-remainder scale. Any additional
common column factor is nonzero at a valid chart: the scaled
column before dividing is nonzero, since \(K\) is a unit and
\(W\) is a nonzero affine polynomial on six distinct sites.

With \(c=m\) the fourth condition produces a degree-seven
polynomial, while isotropy has factors of degrees 2 and 9.
The two projections in \(z\) have nonlinear factors of degrees
7 and \((5,21)\), with projective rootlessness respectively
modulo 11 and \((29,13)\). When \(c=m+d\) or \(m-d\), eliminate
the displacement by its quadratic \(d^2=p\). The surviving
fourth-read factor has degree 12 in the two parameters. Its
two projections have nonlinear degrees 12 and \((2,39)\),
projectively rootless modulo 19 and \((3,19)\).
The sole rational \(z\) in either chronology is the already
rejected \(z=4\). The exact scripts are
[check-symmetric-midpoint.py](check-symmetric-midpoint.py) and
[check-symmetric-endpoint.py](check-symmetric-endpoint.py).
All discarded polynomial factors correspond to explicitly
nonzero scales, clock gaps, or paid-section coefficients.

## A rational helper is not a quadratic hurdle

Fix a rational clock core and the usual nonsingular assembly
pivots. Put \(w=z-h\) and use
\(q(X)=(X-w)(X-\eta)\), with its primitive \(Jq\) from zero.
The first physical-tail condition
\(q(x_a)-Jq(x_a)+Jq(w)v_a/v_3=0\) is affine in \(\eta\).
Thus \(\eta\) is rational under the nonzero coefficient pivot.
Writing \(E=(1-w)(1-\eta)\), the actual helper compatibility is
\[
 q(1+t)-(1+2t-t^2)q(1)
 =t\bigl((1+E)t-(2E-2+w+\eta)\bigr).
\]
For nonzero rational \(t\) with that compatibility, \(1+E\)
cannot vanish: the two vanishing numerators would give
\(w+\eta=4,\ w\eta=2\), hence \((w-2)^2=2\).
On the finite-quadratic chart the tap is the displayed
linear fractional expression. A vanishing first-read coefficient
or other assembly pivot is not a construction claim. This
arithmetic is native in
[SDIRKSevenDirtyRationalHelper.lean](../../lean/RKCert/Research/SDIRKSevenDirtyRationalHelper.lean).

## Replay scope

The native modules checked on stock Lean 4.36.0 certify the
singular suffix exclusion, its independent early-alias Laguerre
bridge, and the rational helper recovery. Their input bridge from
the reviewed dirty tableau is the earlier mathematical reverse
saturation argument; the symmetric and complete \(u=0,4\) alias
eliminations are exact arithmetic replays, not native tableau
theorems.

Run the four Python checks above with SymPy and python-flint
0.8.0 available. Each finishes within seconds; no floating point,
bounded clock scan, or external algebra service is used.
