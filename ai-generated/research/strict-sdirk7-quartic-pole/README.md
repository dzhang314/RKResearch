# Quartic-over-affine cubic defects without active zeros

In the [seven distinct active, two zero weight chart](../strict-sdirk7-two-ghost/README.md),
take a cubic-defect profile \(V=g/W\), with \(W\) affine and
\(g=P_4+\delta P_3\) monic quartic. Here \(P_j\) denotes a monic
orthogonal polynomial for the exact uniform clock functional.
This is a genuinely different construction: neither a
Christoffel mass nor a zero of \(W\) or \(V\) at an active site
is assumed. Two exact finite controls realize all these
nonvanishing conditions. No rational nine-stage tableau
has been found in the chart.

## Pay the nonlinear order conditions by degree

Set \(P=R_3 S_4\), where \(R_3=(Y-1)(Y-u)(Y-v)\) fixes the
last three reflected clocks and \(S_4\) is monic quartic.
For a polynomial \(A\) write
\(J_I(A)=I((A(Y)-A(X))/(Y-X))\). Put
\(J=J_I(P),\ H=J_I(g)\).
On a node \(y_i\), \(K_i=J(y_i)\).
Choose affine factors \(W,L\), let \(T=WL\), and require the
polynomial identity
\[
                      gJ-HP=\tau W T .
\]
Then \(b_i V_i=\tau W(y_i)L(y_i)/P'(y_i)\), with
\(b_i=K_i/P'(y_i)\). For \(D=\tau W/P'\), all cubic
orthogonality and the three nonlinear payments follow
by barycentric degree:
\(WV=g\), so \(bV^2\) has numerator \(\tau Lg\) of degree
at most five, and \(DV,DYV\) have respective numerator
degrees four and five. Likewise \(bVY^j\) for \(j\le3\)
has degree at most five. All these sums vanish on seven
distinct nodes. These implications are
[kernel-checked over a commutative ring once the nodal
identities are supplied](../../lean/RKCert/Research/SDIRKSevenQuarticPoleScalar.lean).

At the three terminal nodes use
\(T(y)=g(y)/r_y\), quadratic interpolation, where \(r_y\)
is the corresponding \(D_y/b_y\) rate from the two-zero chart.
The fourth equation at a candidate \(c\) then becomes
\(G(c)T(c)+E(c)g(c)=0\).
For a given rational \((z,u,c)\) this is **linear in \(\delta\)**.
Let \(T_j\) be the interpolation made with \(P_j\), and
\(F_j=(GT_j+EP_j)/R_3\). Both \(F_3,F_4\) are polynomials
of degree at most two, since \(G(y)+E(y)r_y=0\) at each
terminal site. At a regular point
\(\delta=-F_4(c)/F_3(c)\). The T-split condition is now
the single quadratic root test \(T(h)=0\); set \(W=Y-h\)
and take the other factor as \(L\).

For the nodal construction use the quotient algebra
modulo monic \(g\):
\[
 H_*=-W T (H R_3)^{-1}\bmod g,\qquad S_4=g+\tau H_* .
\]
The inversion is valid when \(g\) is nonzero at the
suffix. The second-kind Wronskian
\(P_4J_I(P_3)-J_I(P_4)P_3=-\|P_3\|^2\)
makes \(H^{-1}\) proportional to \(P_3\bmod g\),
independently of \(\delta\).
The left side \(gJ-HP\) has degree at most three:
it equals \(P\sum_i b_i g(y_i)/(Y-y_i)\);
its first three coefficients at infinity vanish since
\(I(gX^k)=0\) for \(k\le2\).
Thus the congruence modulo \(g\) proves the whole cubic
identity above. On the regular chart
\(\tau=-g(c)/H_*(c)\) makes \(c\) a root of \(S_4\).
The only remaining clock split is the residual monic cubic
\(S_4/(Y-c)\), followed by the regularity of the weights
and the actual helper chronology. No scalar clock solution
is counted as a tableau without those final checks.

## Exact rational partial cores and productive continuation

For fixed rational \(z,u\), the \(T\)-split equation
\[
 T_4(h)F_3(c)-T_3(h)F_4(c)=0
\]
has bidegree at most \((2,2)\). A rational seed is often
available at \(c=h\) equal to the root of affine \(E\);
the seed cannot itself be a valid fourth site, since
\(E(c)=0\) would force \(K_c=0\) by \(G+Eq\ne0\).
A second quadratic root can move away from that seed, but
the two obvious root swaps commute, preserving \(\delta\)
and yielding at most four points per seed.
A genuine rational continuation uses the discriminant
quartic in \(c\). Given a point with nonzero ordinate,
take a quadratic with the same value and first two Taylor
coefficients of the chosen square root. The resulting
quartic intersection has a triple rational root there
and a remaining rational root. Tangents and secants give
further exact partial clock cores; they do not by themselves
solve the cubic.

In the reflection suffix the *fourth* polynomial is independent
of \(M=(u-2)^2-2\) after the known \(R_3\) factor is removed.
The native [reflected quartic identity](../../lean/RKCert/Research/SDIRKSevenQuarticPoleScalar.lean)
gives its exact coefficients for monic quartic \(g\).
For fixed \(m=z/2,c\), this leaves a second rational even-quartic
continuation in \(u-2\): the discriminant of the scaled \(T\)
is generally **quadratic**, not linear, in \(M\).
Its quadratic coefficient is \((g_3+6)^2+4g(1)\).
The reflected inversion is also economical: modulo \(g\),
\(T/R_3\) is proportional to
\(g(1)/(Y-1)-(Y+g_3+5)\), independently of \(M\).
Thus the early quartic in this reflection family is governed
by the affine pole root \(h\), not independently by \(u\).

The [standalone rational replay](check-rational-cores.py)
records two **exact regular partial cores** with width \(z=2\)
and \(u=0\). Reflection has \(c=1942/1399,h=-3\);
arithmetic has \(c=-186/83,h=2\).
The interpolants split over \(\mathbb Q\) and all stated scalar
identities hold, but their remaining cubics are projectively
rootless modulo 29 and 13 respectively.
These are proved failures only for those two exact cores.

## Verified all-active finite profiles

The two literal \(\mathbb F_{19}\) tableaux in this directory
have \(W\) and \(V\) nonzero on all seven active sites.
The rooted order check uses all 85 trees, and the actual
physical \(B^2x-x^3/6\) and adjoint row are checked against
the claimed profile and \(W\).

| Suffix | \((z,u,c,t)\) | Active reflected clocks | Eighth-bush residual |
| --- | --- | --- | --- |
| Reflection | \(2,0,7,10\) | \(5,17,9,7,4,0,1\) | 8 |
| Arithmetic | \(1,10,4,8\) | \(14,3,9,4,0,10,1\) | 7 |

Run:

    python check-controls.py
    python check-rational-cores.py

The first uses standard Python; the second python-flint 0.8 and
SymPy 1.14. Build the two linked Lean modules and run
[proof-audit.lean](proof-audit.lean).
The native finite witnesses are complete order-seven
certificates; the clock-recovery arguments are written
mathematical proofs and not a new native HasOrder wrapper.
