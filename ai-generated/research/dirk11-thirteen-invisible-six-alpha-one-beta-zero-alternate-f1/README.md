# Alternate F1 is impossible in live beta-zero DIRK11/13

**Result.** Over characteristic-zero fields there is no
normalized no-late invisible-six DIRK11/13 candidate with live
reciprocal multiplier, \((\alpha,\beta,\gamma)=(1,0,5)\),
and an alternate old \(F_1\) fit. The scope is the nonmonomial
old generic case with live \(rs(c_2s-c_0)\) and zero affine
pivot \(A_1\) of the
[old-profile census](../dirk11-thirteen-invisible-six-early-profile-census/README.md).
Together with the [alternate F2 proof](../dirk11-thirteen-invisible-six-alpha-one-beta-zero-alternate-f2/README.md)
this leaves the alternate \(F_n\) branch outside \(F_1,F_2\)
in the live beta-zero cubic count. No general DIRK11 stage
bound changes; the unrestricted real interval remains **13–14**.

## 1. Actual old affine root and two compact equations

Use \(R=Y^3+c_2Y^2+c_1Y+c_0\), nonmonomial
\(m=Y^2+rY+s\), \(P=Ym\), \(P_0=YR\), and the actual
old identity \(IP=\ell P+\delta P_0\).
The old ordinary clocks make \(c_0\ne0\); the nonmonomial
origin coefficient gives \(s\ne0\). Therefore \(a=c_0/s\)
is live. Since
\[
 F_1=96s^3-80c_1s^2+75c_0c_2s-75c_0^2=0,
 \qquad
 c_1=\frac65s+\frac{15}{16}a(c_2-a).
\]
The old affinity factors exactly as
\[
 \mathfrak D=s\left(r-\frac{15}{16}(c_2-a)\right)
                  \left(ar-\frac{16}{5}s\right)=0.
\]
The first root is the old slope \(-1\): since \(c_2-a\)
is live, the literal coefficient
\(\delta(c_2-r-a)=r/12\) gives \(\delta=5/4\).
Use the already closed [beta-zero slope chart](../dirk11-thirteen-invisible-six-alpha-one-slope-minus-one-beta-zero/README.md).
It applies to that root irrespective of the affine pivot.
Thus the actual alternate choice has \(r=16s/(5a)\).
This argument also covers a coincident pair of affinity roots,
which would already fall into slope \(-1\).

**old-factors.py** rebuilds the exact old multiplication adjugate
and the affine remainder \(A_1r+A_0\) before specializing.
At the displayed \(F_1\) old coefficients put
\[
 D_1=192s-25a(a+c_2),\qquad D_2=5a^2-5a c_2+16s .
\]
It verifies
\[
 A_1=-\frac{3s^4D_1 D_2^2}{1250a},\qquad
 A_0=-\frac{15}{16}(c_2-a)A_1,\qquad
 n=-\frac{s(-225a^2+512s)D_2^2}{6400a^2}
\]
for the determinant \(n\) on the actual alternate root.
The live old \(m\) evaluations give \(n\ne0\), so
\(D_2\ne0\) without ordering or division by \(D_2\).
Therefore \(A_1=0\) forces \(D_1=0\).

Combining this with \(c_0=as\) and the \(F_1\) expression
for \(c_1\) gives \(c_1=42s/5-15a^2/8\) and the exact
short equations
\[
 P_3(a)=25a^3+25c_2a^2-192c_0=0,\qquad
 P_2(a)=15c_2a^2-8c_1a-48c_0=0 .
\]
The latter is the indicated linear combination of the
first and the displayed \(c_1\) formula. Both are necessary
without assuming a live \(c_2\) or quadratic coefficient.

## 2. Exact ordinary field, both assignments, and the live old lift

The exact resultant in \(a\) is \(-19200c_0 H\), with
\[
 H=3600c_0^2+3720c_0c_1c_2-2205c_0c_2^3
                  +128c_1^3+240c_1^2c_2^2 .
\]
The only removed old factor \(c_0\) is live. As a polynomial
resultant it remains necessary if \(P_2\) loses a leader.
Deflate the actual ordinary Jacobi pencil at the physically
fourth regular clock \(V\) to get
\[
 F(Y)=\frac{J_4(V)J_5(Y)-J_5(V)J_4(Y)}{Y-V},
 \qquad D=132J_4(V)\ne0.
\]
The old cleared coefficients \(C_i=Dc_i\) are those obtained by
deflating \(F\) at \(B\). Substitute them into \(D^4H\),
and take its primitive pseudo-remainder \(G(B)\) modulo
\(F(B)\), removing only integer content and \(J_4(V)^3\).
The exact resultant in \(B\) is a nonzero rational constant
times \(J_4(V)^7 f_{48}(V)\), with one irreducible
\(f_{48}\) of primitive constant **−14638292540815408663567**.

In \(F_{48}=\mathbb Q[V]/f_{48}\), **proof.py**:
1. checks the exact inverse of the leading coefficient of the
   penultimate linear \(B\)-subresultant \(h_1B+h_0\);
2. independently computes the entire exact \(\gcd(F,G)\)
   over \(F_{48}\) and checks that its monic result is
   \(B+h_0/h_1\);
3. verifies the physical transposition exactly:
   \(B\ne0,1,V\), \(J_4(B)\ne0\), \(f_{48}(B)=0\),
   and \(h_0(B)+h_1(B)V=0\) with \(h_1(B)\ne0\).
   Thus \(B(B(V))=V\) in the same ordinary field, not
   a selection of one orientation;
4. computes the complete exact \(\gcd(P_3,P_2)\) over
   that field with the recovered old coefficients.
   Its degree trace is \(3/2\), \(2/1\) then zero,
   and its monic linear row reconstructs one live \(a\).
   All exact inverse pivots are individually checked.
   Consequently the apparent loss of the \(P_2\) leader
   cannot occur in this full projected field. No such leader
   was used before projection.

The nonzero \(a\) allows the normalized old fit to be
represented by the cleared gauge
\(m^\#=5a^2Y^2+16c_0Y+5ac_0\).
For its three coefficients \(m_i\),
\[
 p=m_1m_2c_0,\qquad
 q=3m_0m_2c_2-4m_0m_1-3m_2^2c_0
\]
give the genuine first-ghost clock \(z=p/q\), with the live
old affine-root denominator. No lost direct ratio is used.

## 3. True opposite pins with the universal fifth diagonal

The [universal fifth-pivot proof](../dirk11-thirteen-invisible-six-alpha-one-beta-zero-universal-fifth/README.md)
supplies \(d_B=0,D_B\ne0\) in this alternate chart.
There is no middle ghost. The true matched column has
\((ND)_V=(ND)_B=0\), as in the
[beta-zero primitive closure](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-beta-zero/README.md).
Together with the actual affine first-forward-clean equation
\(J_b(t)=j_0+j_1t=0\), these give the two necessary
opposite primitives \(H_C(t)=\sum_{i=0}^2 h_{Ci}t^i=0\)
for \(C=V,B\). Compute the two cleared pins
\[
       j_1^2 h_{C0}-j_0j_1 h_{C1}+j_0^2 h_{C2}=0
\]
in the **same** recovered old clock algebra.
As before the unscaled forward integral is reflected from
\(B\) to 1; there is no division by \(j_1\), \(V-z\),
or a quartic signal.

Use prime **103**, residue \(V+25\) of \(f_{48}\).
The replay checks the ordinary inverse denominators and
the same exact degrees at every step of the local residue
\(a\)-gcd, then both cleared pin columns have joint
multiplication rank **1/1** over that residue field.
In fact the first pin suffices after exact old projection.
Every coefficient lifts through the local algebra inverting
the checked denominators, so a nonzero residue entry proves
a nonzero exact entry. The joint image contains 1 over
\(F_{48}\), contradicting a true field evaluation killing
the pins. Actual unknown clocks and tableau coefficients are
not reduced, and no orbit is selected by clock ordering.

Replay with `bash verify.sh` using SymPy and python-flint 0.9.
The exact written/source proof is separate from the local
Lean scalar adapter and is not a full native tableau theorem.
