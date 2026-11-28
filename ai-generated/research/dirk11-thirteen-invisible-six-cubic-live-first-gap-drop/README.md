# No first-gap cubic degree loss in the live cubic DIRK11/13 chart

**Result.** In the true normalized invisible-six live cubic
DIRK11/13 chart with \(\alpha=0,\tau\ne0,\deg U=3\), the cubic
first-reverse-gap polynomial \(r_1^*(Y)-Y r_0^*(Y)\)
cannot lose its leading coefficient. The entire exact degree-60
ordinary-clock projection of this loss is excluded in ranks 60
and 120. This is independent of earlier exclusions on the
\(F_3\) leader or affine \(r\) pivot. The unrestricted real
DIRK11 interval remains **13–14**.

Use the genuine tableau hypotheses and true signed ranks of
the [live fourth-clean](../dirk11-thirteen-invisible-six-cubic-live-fourth/README.md)
and [fixed-gap](../dirk11-thirteen-invisible-six-cubic-live-fixed-gap/README.md)
proofs. In particular \(A_{aa}=0,\ m=Y^2+rY+s,\ rs\ne0\).
Write \(V,B\) for the fourth and fifth ordinary reverse clocks,
\(R_3=Y^3+c_2Y^2+c_1Y+c_0\) for the old regular cubic,
\(P=Ym,\ P_0=YR_3,\ k=Ym\) on the old triple,
and \(q=k(V)=G_V/b_V\) in the chosen normalization.
The sites \(V\) and the old triple are distinct and nonzero,
so \(V,c_0,P_0(V)\ne0\). \(I\) means the zero-constant
primitive. The argument is over characteristic zero once
the normalized signed shape holds.

## 1. A genuine weighted primitive comparison

The old affine fit \(\ell=IP/k\bmod R_3\) satisfies the
exact polynomial identity
\[
 IP=\ell P+\delta P_0,\quad
 \delta=1/4-\ell_1\ne0.
\]
At \(V\), the two actual fourth-clean reads with
zero literal diagonal give \(IP(V)=\ell(V)q\) and
\(IP_0(V)=w(V)q\), where \(w=IP_0/k\bmod R_3\).
In particular \(\ell(V)\ne0\).
The corrected quartic matching \(G/b\) also at \(V\)
is \(P_0^*=P+\delta P_0/\ell(V)\);
the four-site cubic marking uses its companion \(P_1^*\).
Thus
\[
 r_0^*=\ell+\frac{\delta}{\ell(V)}w.
\]
The cubic leader of \(r_1^*-Y r_0^*\) is zero if and
only if \(w\) is affine.

Suppose \(w\) is affine. Matching \(IP_0-wP\) on the
three old and zero sites gives the true polynomial identity
\[
 IP_0=wP+(Y/5+\eta)P_0.
\]
The factor \(Y/5\) is the actual top primitive coefficient,
not an interpolation assumption. Divide both polynomial
identities by their root factor \(Y\) in the polynomial ring,
and compare coefficients. With
\[
 d_1=c_2-r-c_0/s,\qquad d_2=c_1-s-rc_0/s
\]
the four reads are
\[
 \delta d_1=r/12,\quad \delta d_2=s/4,\qquad
 \eta d_1=2c_1/15-rc_2/20,\quad
 \eta d_2=3c_0/10-sc_2/20.
\]
The initial coefficients also give
\[
 \ell_0=-c_0\delta/s,\ \ell_1=1/4-\delta,\quad
 w_0=-c_0\eta/s,\ w_1=c_2/20-\eta .
\]
Both \(d_1,d_2\) are live because \(r,s,\delta\ne0\);
eliminating \(\eta,\delta\) in the shared coefficient reads
gives the actual necessary equation
\[
 4c_1s=r(3c_0+c_2s). \tag{1}
\]

At \(V\), apply the two actual paid fourth-clean samples
to the above identities for \(IP,IP_0\). Since \(P_0(V)\ne0\),
they give
\[
 \ell(V)(V/5+\eta)=\delta w(V).
\]
The constant terms of \(\delta w-\eta\ell\) cancel
and \(V\ne0\), yielding
\(\ell(V)=\delta c_2/4-5\eta/4
        =\delta(c_2-3c_0/s)/2\).
With \(t=c_2-c_0/s\), this gives
\((1-4\delta)V=2\delta t\), while the first old
coefficient read gives \(r=12\delta(t-r)\).
Eliminating \(\delta\) yields
\[
 r\Phi=6V(c_2s-c_0),\qquad
 \Phi=(c_2+8V)s-c_0 . \tag{2}
\]
If \(\Phi=0\), then \(c_2s-c_0=-8Vs\ne0\)
contradicts (2). Hence \(\Phi\ne0\), and since
\(r\ne0\) also \(c_2s-c_0\ne0\). Neither an
intercept nor a middle-coefficient degeneracy is
inferred from a residue.

## 2. Exact degree-60 projection and all live factors

Define \(N_0=6V(c_2s-c_0)\), so \(r=N_0/\Phi\).
Equation (1) gives a polynomial \(E\) of degree at most two
in \(s\):
\[
 E=4c_1s\Phi-(3c_0+c_2s)N_0.
\]
Its constant \(18Vc_0^2\) is nonzero.
The true affinity quadratic \(\mathcal D(r,s)=0\)
gives, after this substitution,
\[
 Q=\frac{c_0N_0^2-(2s^2+c_1s)N_0\Phi+
                (3c_2s^2-3c_0s)\Phi^2}{3(c_2s-c_0)}=0 ,
\]
a polynomial of degree at most three. The division
is exact polynomial arithmetic and the canceled
\(c_2s-c_0\) is genuinely live by (2).
The exact resultant in \(s\) has only the live factors
\(V^4,c_0^4\) and one degree-three-in-\(V\)
factor. Substitute the old Jacobi deflation from the
live \(132J_4(B)\) leader, clear that denominator,
and pseudo-reduce in \(V\) by the ordinary quartic
\(T_4\). The exact resulting polynomial content is
\(J_4(B)^6\) up to a rational scalar. The resultant
in \(V\) has factors \(J_4(B)^4\) and a new irreducible
degree-60 base factor. No other polynomial contents
or clock fibers are dropped.

The linear cofactor for \(V\), then the linear cofactor
for \(s\) from \(E,Q\), have unit leaders in the full
rank-60 modular clock algebra at 101. The exact
profile formula (2) follows, with \(\Phi\) also
unit-tested there. These cofactor implications use
degree bounds and retain intermediate degree drops;
a tested unit is only needed for the final linear
pivot. Reconstruct \(q\), \(k\), and \(U_{\rm rev}\)
by live interpolation and test all coefficient
inversions in the whole algebra.

## 3. Both actual gap shapes excluded

For five initial forward ghosts, the established
true grade-four cutoff and its paid grade-five shape
force the determinant of \(I(XU),X I(XU),S_6\bmod U\)
to vanish. This determinant is a unit in rank 60.

For two or three reverse-gap ghosts, the true branch
hypothesis has already killed the first-gap cubic
coefficient. Truncate that coefficient **by the
proved chart identity**, not just because it reduces
to zero. The remaining quadratic leader is a unit
in rank 60, so adjoining the first gap ghost costs
only a quadratic and gives rank 120. The distinct
second clock is obtained through the previously
proved two-root equation (the quadratic coefficient
of that equation is also unit-tested here). The true
quintic crossing is a unit throughout rank 120.

Run `python3 replay.py` with SymPy. The same four
optional sibling-source overrides as in the affine-pivot
packet are supported. The proof lifts residue units
only in the prescribed monic clock algebras over
\(\mathbb Z_{(101)}\); it never reduces an unknown
time, tableau, or weight modulo 101. The scalar
shared primitive equations and live \(\Phi\) pivot
are kernel-checked in the companion Lean module;
the true rank ingress and clock replay are exact
source arguments. Earlier \(F_3\)-leading-drop
and affine-pivot cases are not hypotheses for this
exclusion, and no claim is made for arbitrary other
normalized or unnormalized tableaux.
