# Generic quartic-head exclusion in characteristic zero

This application uses the first-provider lemma in the companion note. It also uses the established paid ordinary order-eight stage floor \(s(8)\ge10\), and the previous general reduction of the low degree-eight paid branch to a rank-three invariant core \(U\) and one quartic head at degree four. No fixed high-order chart or exceptional-characteristic computation is needed.

Assume the rank-three quartic profile through degree eight. Apply chronological compression through \(E_8\) as in the companion note; its width is 17. There are at least five clean labels (including the origin) and at least six head labels. The width lemma puts the first ordinary order-eight provider on at most \(3+4+3=10\) rows. By the order-eight floor, there are exactly ten preceding rows: all three core pivots, the clean origin, and six head labels. In particular the saturated residue conditions apply to \(k=2,3\).

There is also a separate Hermite tail constraint: if the size-six defect input gives \(d_8\ge7\) on actual ordinary order-eight providers, then \(g\le6\), so the complete compressed tableau has precisely five or six clean labels. This optional count is not used in the exclusion below.

## Two clean reads

Dilate the first nonzero clean clock to 1 and write \(y\ne0,1\) for the second. Dilating preserves the flag and all normalized moment assertions. Put
\[
W\coloneqq XP,\qquad H\coloneqq J^3 W.
\]
At the first clean read, apply \(A\) to the contrasts with multipliers \(X,X^2,X^3\). Each contrast agrees with a core vector on the preceding physical rows. Strict chronology and the pure relations imply
\[
     (J W)(1)=(J(XW))(1)=(J(X^2W))(1)=0.
\]
Equivalently \(H(1)=H'(1)=H''(1)=0\). Also \(X^4\mid H\), by the origin and the three primitives, and \(\deg H=8\). Hence
\[
H(X)=\alpha X^4(X-1)^3(X-r),\qquad \alpha\ne0.
\]
At the second clean read, the multipliers \(X(X-1)\) and \(X^2(X-1)\) kill both earlier clean labels; all preceding head reads vanish as before, after subtraction of the relevant core vector. Strict chronology gives the same two moment tests for \((X-1)W\) at \(y\). Thus the polynomial \(J^2((X-1)W)\) and its derivative vanish at \(y\). The exact primitive identity is
\[
\begin{aligned}
 J^2((X-1)W)
  &=(X-1)H'-2H\\
  &=\alpha X^3(X-1)^3\bigl(6X^2-5(1+r)X+4r\bigr).
\end{aligned}
\]
The displayed quadratic must have a double root at \(y\), so
\[
25r^2-46r+25=0. \tag{1}
\]
In particular \(r\ne0,1\) in characteristic zero.

## The same early heads compare three successive primitives

The saturated residue conditions at \(k=2,3\) and integration by parts give
\[
H'\equiv L H'',\qquad H\equiv M H''\pmod P,
\qquad \deg L\le1,\quad\deg M\le2.
\]
In detail, the three primitives \(J W,J(XW),J(X^2W)\) are \(H''\), \(XH''-H'\), \(X^2H''-2XH'+2H\). The two residue congruences therefore yield the stated affine \(L\) and quadratic \(M\). Moreover \(H''\) is invertible modulo \(P\). A common root would by those congruences annihilate \(H'\) and \(H\) as well. The only possible roots of \(H\) are \(0,1,r\): \(P(0)\ne0\) since \(r\ne0\), \(P(1)=H'''(1)\ne0\) since \(r\ne1\), and \(r\) is a simple root of \(H\).

Use the exact logarithmic derivative identity
\[
R H'=S H,\qquad
R\coloneqq X(X-1)(X-r),\quad
S\coloneqq 8X^2-(5+7r)X+4r.
\]
One differentiation gives \(R H''=(S-R')H'+S'H\), and a second gives
\[
R H'''=(S-2R')H''+(2S'-R'')H'+S''H.
\]
Modulo \(P\), \(H'''=XP=0\). Substituting the two residue relations and dividing by \(H''\) yields actual polynomial identities, because their degrees are at most three:
\[
R=(S-R')L+S'M,\qquad
0=(S-2R')+(2S'-R'')L+S''M.
\]
Eliminating \(M\) gives \(N+D L=0\), where
\[
\begin{aligned}
N&\coloneqq S''R+S'(S-2R')\\
 &= 48X^3-(42+78r)X^2+(5+70r+21r^2)X-10r-14r^2,\\
D&\coloneqq S'(2S'-R'')-S''(S-R')\\
 &=336X^2-(210+294r)X+40+68r+84r^2.
\end{aligned}
\]
The cubic and quadratic coefficients force \(L=-X/7+(1+3r)/28\). The coefficient of \(X\) then gives
\[
                           315r^2-382r+115=0. \tag{2}
\]
Over every field of characteristic zero, (1) and (2) are incompatible. The quadratic (1) is irreducible over the prime field \(\mathbb Q\) since its discriminant is \(-384\), and (2) is not a rational multiple. Thus the quartic-head branch is excluded in characteristic zero, including unordered fields where \(-6\) is a square.

## What is gained

Combined with the earlier paid source reduction of all other low-rank profiles, this gives \(\dim F_8\ge9\) at separated degree eight over every characteristic-zero field. Inserting this into the ordinary midpoint rents would give the degree-eight-based floors \(s_{\mathrm{ERK}}(16)\ge24\) and \(s_{\mathrm{ERK}}(17)\ge26\) over those fields, subject to independent checking and the existing table comparison. This note alone claims neither a stronger already-verified table cell nor transport to arbitrary rings from this characteristic-zero argument.

The first-provider width theorem offers an independent outer-degree obstruction: a rank-three quartic head cannot persist one further flat degree in the paid range, because the first true order-nine provider would have at most ten rows, conflicting with the established paid order-nine floor of twelve. This is a general width mechanism; it does not require the characteristic-zero quadratic comparison or exceptional arithmetic.
