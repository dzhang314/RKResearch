# A single crossing is impossible in the ERK10 five-unequal-pair case

Work over any characteristic-zero field in the
[all-live two-carrier ERK10 equality case](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md).
Assume the pooled \(br\) row is zero and all ten middle
active rows occur at **five** clock labels, each exactly twice,
with unequal nonzero amplitudes at every pair. Each pair
has nonzero ordinary pooled weight, as in the
[carrier census](ERK10-THREE-CARRIER-EXCLUSION.md).
The two actual repeat groups 4/5 and 10/11 lie wholly in
opposite halves of the physical 7|7 cut. Therefore the number
of crossing pairs is one or three. **This note excludes one.**
It does not exclude the remaining three-crossing case.

## Whole-half models and the first clock choice

Suppose the only crossing pair has clock \(u\).
The two whole left pairs have clocks \(p=c_4=c_5,a\);
the two whole right pairs have clocks \(q=c_{10}=c_{11},b\).
The first nonzero active clocks are \(t=c_3\) and \(t_R=c_{12}\).
The [actual doubled entrances](ERK10-DOUBLED-ENTRANCE-TRIPLET-EXCLUSION.md)
give \(p=2t,\ q=2t_R-1\), with \(t\ne0,\ t_R\ne1\);
each repeated group has nonzero unequal amplitudes.
Left \(t\) is either \(a\) or \(u\), and right \(t_R\) is
either \(b\) or \(u\).

The genuine grade-four models
\[
  P_L=X(X-p)(X-a)(X-u),\qquad
  P_R=(X-1)(X-q)(X-b)(X-u)
\]
give actual numerical vectors zero through all of the
respective physical first/last seven rows after subtracting
the carrier value times the pure carrier indicator \(s\).
The model degrees remain four. With these actual vectors,
strictness pays the usual one-step seam
\(\int JP_L\,P_R=0\) at total grade nine.

Use also the real physical degree-three input
\(B_L(c)-B_L(\theta)s\), \(B_L=X(X-t)(X-p)\).
It vanishes through row 5, since the actual row-4/5
clock is \(p\). Its genuine two-step unary advance is
zero through row 7. Thus the same grade-four \(P_R\)-lift
pays
\[
   \int H_p P_R=0,\qquad
   H_p=J^2 B_L=X^5/20-pX^4/8+p^2X^3/12 .
\]
These are true zero-products on the physical rows,
not hypothetical restrictions on a reversed dense tableau.

If \(t=a=p/2\), then \(P_L=(X-u)B_L\) and
\(JP_L=(X-u)JB_L-H_p\), by the formal product rule,
with \(JB_L=X^2(X-p)^2/4\).
Evaluate the two zero integrals by the actual ordinary
clock quadrature (degree at most nine).
The **only** potentially contributing distinct clocks
are \(p,a\): endpoint 0 is killed by the primitives,
endpoint 1 by \(P_R\), and \(q,b,u\) by \(P_R\).
If neither \(p,a\) is 1, the respective pooled weights
and the two evaluations of \(P_R\) are all nonzero.
The resulting \(2\times2\) determinant on their unknown
weighted reads, up to sign, is
\[
 H_p(p) (JP_L)(a)-H_p(a)(JP_L)(p)
          = H_p(p)(a-u)\, JB_L(a)\ne0 .
\]
Indeed \(H_p(p)=p^5/120\), \(p\ne0\), and
\(a=p/2\) is distinct from \(0,p,u\).
This is impossible. If \(p=1\) the \(a\)-term alone in
the two-step seam is nonzero (\(H_p(a)=p^5/240\));
if \(a=1\), the \(p\)-term alone is nonzero.
There is no possibility \(p=0\) or \(a=0\) in this branch.
All other clock-endpoint coincidences still give zero
at the indicated factor or the endpoint primitive.
Thus \(t=a\) is excluded also with endpoint collisions.
Reflecting excludes \(t_R=b\).

Therefore the single crossing pair occurs exactly at
physical rows 3 and 12:
\[
                    c_3=c_{12}=u,\qquad
                    p=2u,\quad q=2u-1 .
\]
This does **not** mean its two amplitudes are equal.

## The remaining clock geometry and exact seam norm

Put \(U=2u-1\), \(A=2a-1\), \(B=2b-1\).
If \(U=0\), then \(p=1,q=0\) and the potential ordinary
scalar support has at most five distinct clocks including
both endpoints. This is impossible: testing the product
of the at most three interior clock factors times
\(X(1-X)\) gives weighted orthogonality up to its own
degree, contrary to the nonsingular anchored Gram.
This support argument includes cancellation of any
pooled endpoint weights. In particular the division
by \(U^3\) below is guarded.

With \(Z=2X-1\), the physical active hull is
\[
 (Z-U)((Z-2U)^2-1)(Z^2+d_1Z+d_0),\quad
               d_1=-(A+B),\quad d_0=AB .
\]
The ordinary degree-nine scalar quadrature makes it
orthogonal under \(1-Z^2\) to \(1,Z,Z^2\), using the
known endpoints as anchors. This is also valid if an
individual active label coincides with an endpoint.
The moment system on \((d_0,d_1,1)\), with a harmless
constant row scale, has matrix
\[
 M=\begin{pmatrix}
 -105U^3& 3(14U^2-1)&-3U(7U^2+2)\\
 3(14U^2-1)&-3U(7U^2+2)&18U^2-1\\
 -3U(7U^2+2)&18U^2-1&-U(9U^2+4)
 \end{pmatrix}.
\]
This follows from the even centered moments
\(4/[(k+1)(k+3)]\), the odd ones being zero.
Its determinant is \(-84U^3 F(U)\), where
\(F=126U^6-138U^4+51U^2-5\).
Thus \(F(U)=0\). The first two rows' coefficient pivot
for \(d_0,d_1\) is \(9P(U)\), where
\(P=245U^6-126U^4+28U^2-1\).
This is nonzero on every characteristic-zero root of
\(F\): the explicit mod-37 Bézout calculation in the
companion proves \(F,P\) coprime after this reduction.
Every actual \(U\) is integral above 37 as \(F\)'s
leading coefficient is a unit, so no common zero can
be lost by passing to the residue field.

The two solved coefficients at \(F(U)=0\) are
\[
   1390\,d_0=-3(2982U^4-2608U^2+625)=n_0,\qquad
   1390\,d_1=-5U(4410U^4-3528U^2+521)=n_1 .
\]
The companion checks the cleared two-row identities;
their residuals are explicit multiples of \(F\).
These divisions remain legitimate at every branch,
since \(1390\ne0\) and the pivot was established.

The actual right-supported two-step probe was already
paid from \(B_L\) on physical rows through 5.
For the surviving location \(p=1+U,\ q=U,\
u=(1+U)/2,\ b=(1+B)/2\), its scalar \(201600\)-multiple is
\[
      H_A(U) B+H_B(U),\quad
 H_A=210U^4-60U^2+10,\quad
 H_B=-70U^4+60U^3+35U^2-10U-7 .
\]
Thus \(H_A B+H_B=0\).
Multiplying the actual quadratic for \(B\) by
\(1390 H_A^2\) and substituting yields the necessary
identity
\[
            1390 H_B^2-n_1 H_A H_B+n_0 H_A^2=0 .
\]
There is no division by \(H_A\) here, so a collapsed
affine seam has not been discarded.
The exact norm identity modulo \(F=0\) is
\[
 189\,(1390 H_B^2-n_1 H_AH_B+n_0 H_A^2)
                  =-13\cdot1390\,G,\qquad
 G=9015U^4-6000U^2+853 .
\]
The displayed divisor identity is verified on a
14-point integer grid for degree at most 13.
But the explicit second mod-37 Bézout identity makes
\(F,G\) coprime, again with \(F\)'s leading coefficient
a unit. This excludes **all** one-crossing charts
over characteristic zero.

[ERK10FivePairOneCrossGate.lean](ERK10FivePairOneCrossGate.lean)
checks the determinant, solved coefficients, exact integral,
cleared norm, and both modular Bézout identities.
The grade budgets and stage topology are the mathematical
bridges in this note. No unrestricted 14–15 bound changes.
