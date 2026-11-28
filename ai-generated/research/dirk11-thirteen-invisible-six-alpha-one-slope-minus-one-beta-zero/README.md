# Five initial ghost reads eliminate the live beta-zero slope-minus-one chart

**Result.** In the normalized invisible-six no-late DIRK11/13
chart with live reciprocal multiplier, \(\alpha=1,\beta=0\)
and \(\gamma=5\), the old affine slope \(-1\) is impossible.
Combined with the
[independent first-ghost bridge](../dirk11-thirteen-invisible-six-alpha-one-slope-minus-one-bridge/README.md)
and the
[beta-one and beta-two slope certificate](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-minus-one/README.md),
this closes the affine-slope-minus-one profile, including the
direct \(F_1\) branch, in all three live \(\alpha=1\) counts.
The unrestricted real DIRK11 interval remains **13–14**.

Write \(Y=1-c\), \(N=A^{\mathsf T}\) in literal reverse
order. The physical order here is
\(T,v,u,w,z,V,B,[5\text{ ghosts}],O\) in reverse.
In forward coordinates the five initial ghosts are after
\(O\) and before the first nonorigin regular row \(b=1-B\).
The remaining ghost is \(\xi=1-z\); \(a=1-V\) is the next
ordinary forward clock after \(b\).
Use the actual rooted-space and reciprocal identities of the
[forward mask proof](../dirk11-thirteen-invisible-six-prefix/README.md).
In particular \(g=U(c)\) on ghosts and \(g=0\) on clean rows,
\(\phi=U(c)-g\) is genuinely grade three, and \(U\) is live
at all nonterminal clean and ghost clocks. It is necessarily
cubic in the live five-prefix count: a nonconstant carrier of
lower degree cannot have five initial zero primitive reads,
and the constant case was already excluded in the earlier
census. All signs below refer to the same live reciprocal
gauge; a common nonzero scaling of \(U\) is immaterial.

## 1. A single proportionality from the true first five ghosts

Write \(J=I_X[XU(X)]\) and let \(R_5\) be the monic hull
of the five initial forward ghosts. The genuine grade-five
identity \(A(C\phi)-J(c)\in F_5=g\mathcal P_2\) gives
\(J+UQ_2=\eta R_5\) for a scalar \(\eta\):
all five actual inclusive donor sets see zero \(C\phi\),
and the polynomial degree is at most five.
The single remaining ghost is at \(\xi\), so the whole
six-ghost hull is \(R_6=(X-\xi)R_5\).
There is no need to divide by \(\eta\).

Let \(S_6\) be the monic hull of the six nonterminal clean
clocks. The actual \(E_6=\mathcal P_5+g\mathcal P_3+K e_T\)
decomposition of \(S_6(c)\) forces its degree-five ordinary
part to be zero at six distinct ordinary sites and hence
identically zero. Its ghost reads give \(S_6-UQ'_3=\omega R_6\).
Here \(\omega\ne0\): otherwise the nonconstant \(U\) divides
the split \(S_6\), though \(U\) is live at all its roots.
Multiplying the first fit by \(X-\xi\) and reducing modulo \(U\)
therefore gives \((X-\xi)J\equiv(\eta/\omega)S_6\).

Use reverse polynomials \(U_r(Y)=U(1-Y)=M+tR\),
\(R=(Y-v)(Y-u)(Y-w)\), and \(D_R=(Y-V)(Y-B)R\).
The reflected clean hull is \((Y-1)D_R\).
The reflected primitive \(J(1-Y)\) has the exact polynomial
factor \(Y-1\), and this factor is a unit modulo \(U_r\)
since \(U(0)\) is live. Thus for some scalar \(\sigma\),
\[
 E(Y)= (Y-z)\frac{J(1-Y)}{Y-1}
           \equiv \sigma D_R \pmod{U_r}.
\]
All operations are in a single reverse variable; the sign of
the reflected mark can be absorbed in \(\sigma\).
The code computes \(J(1-Y)\) as
\(\int_Y^1(1-s)U_r(s)\,ds\) and independently verifies the
reflected coefficients.

Since \(\deg E,\deg D_R\le5\) and \(U_r\) is cubic,
\(E\) lies in the span of \(U_r,YU_r,Y^2U_r,D_R\).
Replace the third column by \((Y-V)(Y-B)U_r\) by lower
column subtractions, and then by \((Y-V)(Y-B)M\) by
subtracting \(t D_R\). Reduce the remaining columns modulo
the monic \(D_R\). The four resulting columns in a
five-coordinate space have rank at most three.
All five maximal minors vanish and each has degree at most
three in \(t\): only \(E,U_r,YU_r\) vary with \(t\).
The other gate is the true strong adjacent \(V\) quadratic
using \(I^2P(V)-\rho(V)k=(z-V)T\), from the
[actual live old-profile proof](../dirk11-thirteen-invisible-six-alpha-one-live-cubic/README.md).
No \(1+\ell_1\), diagonal, or ghost–regular difference is
inverted in this adjacent gate.

## 2. Exact rank over the already isolated clock field

By the first-ghost bridge, slope \(-1\) here has live direct
\(F_n\) ratio. The exact resultant and coefficient
reconstruction are precisely those of the slope-minus-one
certificate: the \(c_1=0\) fallback is an exact ordinary
contradiction, and the rest has the unique irreducible
degree-60 clock factor and unit linear recovery of \(B,s\).
The supplied **clock.py** reproduces those exact identities
and **rank.py** checks both denominator pivots on the full
residue algebra at 101.

Use the basis \(1,V,\ldots,V^{59}\) over the monic degree-60
algebra, with fixed carrier degree cap four. The Macaulay
matrix has columns from the adjacent gate (degree at most 2)
and the five minors (degree at most 3), multiplied by every
basis element and every allowed power of \(t\).
The full row rank is **300/300** at 101. Thus the rational
matrix already contains 1 in its image, and no exact
characteristic-zero candidate can kill the true gates.
This does not use integrality of unknown tableau entries,
ordinary clocks, or \(t\). There is no assumption on \(d_V\)
or \(d_B\), and no middle-ghost argument was imported into
the empty middle gap.

Run **python3 coordinate-audit.py**, **python3 clock.py**
and **python3 rank.py** with SymPy and python-flint 0.9.
This is an exact written and executable source proof with
the separate native old-fit certificate, not an end-to-end
Lean nonexistence theorem for DIRK tableaux.
