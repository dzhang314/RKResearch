# The remaining cubic mean cannot vanish at either physical endpoint

Continue the
[all-live eight-clock ten-active-row chart](ERK10-FORCED-TWO-ACTIVE-PAIR-SEAMS.md)
after the
[quadratic-mean exclusion](ERK10-QUADRATIC-MEAN-EXCLUSION.md).
The polynomial mean \(R\) is monic cubic, the repeated
clocks \(p,q\) are nonendpoint, and both groups have unequal
nonzero amplitudes. Over any characteristic-zero field,
**\(R(0)R(1)\ne0\)**. This does not exclude the still-
possible cubic means with both endpoint values nonzero.

Suppose \(R(1)=0\) and write \(S=(X-p)(X-q)R\).
The genuine singleton residue
\(J_R D_s+\kappa X(X-1)\equiv0\bmod R\) at \(X=1\)
gives \(J_R(1)=0\): all singleton amplitudes equal their
nonzero \(R\)-values, so \(D_s(1)\ne0\).
But by the definition of \(J_R\),
\[
            J_R(1)=\int_0^1 X S(X)\,dX .
\]
As \(S(1)=0\), write \(S=(X-1)Z_4\) with monic \(Z_4\)
of degree four. The three already paid anchored tests
\(\int X(1-X) S X^j=0\) for \(j=0,1,2\) make \(Z_4\)
orthogonal, under the \(X(1-X)\) measure, to
\((1-X),X(1-X),X^2(1-X)\).
The test \(\int X S=0\) adds orthogonality to 1.
Those four test polynomials form a basis through degree
three. The nonsingular anchored moment matrix thus fixes
\[
   S=(X-1)L_4(X)/42,\qquad
   L_4(X)=42X^4-84X^3+56X^2-14X+1 .
\]
In particular \(p,q\) are roots of \(L_4\).

Use the genuine **two-step physical seam** of the
[two-pair packet](ERK10-FORCED-TWO-ACTIVE-PAIR-SEAMS.md):
\(\int_0^1 H_p(X)P_R(z)(X)\,dX=0\), where
\[
       H_p=J^2[X(X-p/2)(X-p)]
              =X^5/20-pX^4/8+p^2X^3/12.
\]
With \(R(1)=0\), the actual scalar model
\(P_R(z)=-(X-q)(1-t_R)(1-w)(1-z)R\).
Its factored constant is nonzero: \(t_R,w,z\) are singleton
active clocks, so none can be 1 when \(R(1)=0\).
Consequently the true paid grade-nine condition forces
\[
           \int_0^1 H_p(X)(X-1)\frac{L_4(X)}{X-p}\,dX=0 .
\]
The quotient is polynomial and the scale 42 is nonzero.
The integral evaluates to \(-N(p)/7200\), where
\(N=1260X^5-2940X^4+2580X^3-1055X^2+195X-12\),
by direct synthetic division and integration. The exact
reduction is
\[
 N(X)-(60X^3-75X^2+25X-2)=(30X-10)L_4(X).
\]
The two remaining possible polynomials cannot vanish
together: writing \(K=60X^3-75X^2+25X-2\), the
integer Bézout identity is
\[
 (-16800X^2+18900X-4675)L_4
 -(-11760X^3+22050X^2-12950X+2338)K=1 .
\]
That proves the right endpoint exit; genuine weighted
reflection proves the left one. All step and model
arguments were genuine rooted or scalar tests through
total grade nine, and no square of a grade-five pure
profile was assumed paid.

[ERK10CubicMeanEndpointGate.lean](ERK10CubicMeanEndpointGate.lean)
checks the integral (six exact integer values for
a degree-at-most-five identity), remainder and Bézout
certificate. No unrestricted stage bound changes.
