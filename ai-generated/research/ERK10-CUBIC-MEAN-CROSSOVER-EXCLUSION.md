# The all-live ERK10 two-pair cubic mean is impossible

Work over an arbitrary characteristic-zero field, with an actual
fourteen-stage ERK tableau of rooted order ten, every output weight
nonzero, and exactly two quadratic carriers at rows 2 and 13.
We close the one remaining subcase of the
[eight-label ten-active-row chart](ERK10-FORCED-TWO-ACTIVE-PAIR-SEAMS.md):
nonzero pooled \(br\), repeated clocks \(p,q\) off the endpoints,
and cubic \(br\)-weighted mean \(R\). The
[cubic endpoint exit](ERK10-CUBIC-MEAN-ENDPOINT-EXIT.md)
gives \(R(0)R(1)\ne0\).
This proof uses no ordering or positivity and alleges no unrestricted
change to the ERK10 14–15 interval. See the separate
[all-live completeness ledger](ERK10-ALL-LIVE-COMPLETENESS.md).

## A true two-read seam on the seven-row cut

Write \(t=c_3=p/2,\ p=c_4=c_5,\ x=c_6,\ y=c_7,\ z=c_8,\
w=c_9,\ q=c_{10}=c_{11},\ \tau=c_{12}=(1+q)/2\).
The eight distinct **active** clock labels are
\(t,p,x,y,z,w,q,\tau\); the two repeated groups differ in
amplitude. The first and last physical rows are inactive
at clocks 0 and 1, and the carriers have a common clock
\(\theta\) and cancelling weights. The carriers have \(r=0\).
An active label may numerically be an endpoint when not already
excluded by its separate guards; the proof does not cancel
\(a\) or \(a-1\) at any singleton.

The scalar \(R\) is the literal \(r\)-value at every singleton,
and the genuine grade-three mask
\(T=R(c)-r-R(\theta)s\), with model \(R\), is supported at
the physical endpoints and the two repeated groups.
Here \(C\) is the clock diagonal, \(s\) is the pure quadratic
carrier indicator and \(r=As\) is pure of grade three.
Put \(H_R(X)=(X-\tau)(X-w)(X-z)\) and
\[
              P_R=(X-q)[R(1)H_R-H_R(1)R].
\]
As in the base two-pair packet, its actual grade-four lift
\(P_R(c)+H_R(1)(C-q)r-P_R(\theta)s\)
vanishes on physical rows 8–14. The lift is zero at each
right singleton because \(R(c_i)=r_i\), at the q-pair by
its factors, at the carrier by its correction, and at
the endpoint by \(P_R(1)=0\). Both added terms are pure.

Now set \(B_L=X(X-t)(X-p)\) and
\(v=B_L(c)-B_L(\theta)s\) of grade three. It vanishes
through row 5, so its actual grade-five \(A^2v\) vanishes
through row 7. The corrected grade-four lift of \((X-x)B_L\)
vanishes through row 6; its \(A\)-advance vanishes
through row 7. Both advances have zero numerical product
with the right lift, at paid grade \(5+4=9\).
Write
\[
 U_p=JB_L=X^2(X-p)^2/4,\qquad
 H_p=J^2B_L=X^5/20-pX^4/8+p^2X^3/12 .
\]
The true two-step and one-step seams are
\(\int H_p P_R=0\) and \(\int [(X-x)U_p-H_p]P_R=0\).
They give \(\int F P_R=0\), with \(F=(X-x)U_p\).

To exploit the exact support, split the scalar seam using
\(P_R\) above. Since \(F(X-q)\) has degree six, the paid
pure \(r\) and \(s\) reads annihilate \(F(C)(C-q)r\) and
\(F(C)(C-q)s\), respectively. Testing the real mask \(T\)
now evaluates
\[
          \int F(X)(X-q)R(X)\,dX
             = b_{14}F(1)(1-q)R(1).
\]
Indeed \(F\) kills the physical origin and the p-pair,
\(X-q\) kills the q-pair, the carrier correction is exact,
and \(T\) vanishes at all other stages. Ordinary degree-nine
scalar quadrature for \(F(X)(X-q)H_R(X)\) likewise leaves
only physical singleton rows 3 and 7 plus physical row 14:
the other right singletons are killed by \(H_R\), row 6
by \(F\), the pairs by their factors, row 1 by \(F(0)\),
and the two carriers cancel. The two identical row-14
terms in the split \(\int F P_R\) cancel—even if a singleton
also has clock 1, since the cancellation is per physical row.
Divide by \(R(1)\ne0\) to get
\[
              \sum_{a=t,y} b(a)F(a)(a-q)H_R(a)=0 .
\]
Here \(b(a)\) is the output weight at the indicated
singleton physical row, not a pooled weight including an endpoint.

Write \(D\) for the monic hull of the eight active labels.
The paid \(br\)-moments give
\(b(a)R(a)=\kappa/D'(a)\) at the singleton, with \(\kappa\ne0\).
For \(a=t,y\), letting \(a'\) be the other of the two labels,
\[
        D'(a)=(a-p)(a-q)(a-x)H_R(a)(a-a').
\]
Every factor canceled here is nonzero by distinctness of
the active labels. The denominators \(R(t),R(y)\) are also
nonzero, being active amplitudes. Cancellation gives
\[
                  \frac{t^2(t-p)}{R(t)}
                    =\frac{y^2(y-p)}{R(y)} .
\]

## Literal central contacts in both directions

The real grade-four response is
\(Av=U_p(c)+(\alpha+\beta C)r+\gamma s\)
by the [common pure flag](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md).
At rows 4/5 it is zero and \(U_p(p)=0\); either nonzero
amplitude at \(p\) implies \(\alpha+\beta p=0\).
At the strict row 3, using \(t\ne p\), it gives
\(t^2(t-p)/4+\beta R(t)=0\). The new ratio therefore
gives \(y^2(y-p)/4+\beta R(y)=0\), hence \((Av)_7=0\).
It already vanished through row 6. This is a statement
about the genuine stage vector (and forces \(A_{76}=0\),
since \(B_L(x)\ne0\) and row 6 is its only possible read).

Apply the entire calculation to the actual weighted transpose
in reverse physical coordinates. Its order ten and the common
numerical/pure grades through four are already established.
The transformed clock is \(1-X\), the repeat labels are
\(1-q,1-p\) in left-to-right order, and its mean polynomial is
a nonzero constant multiple of \(R(1-X)\), since its pure
\(r\)-vector is a nonzero scalar multiple of the original
one. The required mean at its right endpoint is therefore
nonzero by \(R(0)\ne0\).
Writing \(A^\star=B^{-1}A^\mathsf{T}B\) in original physical
indices, the reversed input \(v^\star\) has
\(B_R=(1-X)(X-\tau)(X-q)\) as model and has its
actual carrier correction. The mirror contact is
\((A^\star v^\star)_8=0\), and its response is zero
at all physical rows 8–14. Its model in the original
variable is \(U_q^\star=(1-X)^2(X-q)^2/4\),
also its original grade-four model by the common flag.

The response \(Av\) is thus zero on the whole left half
and \(A^\star v^\star\) on the whole right half. Their
Hadamard product is identically zero, and remains zero
after multiplication by \(2C-I\). The further advance
\(A^2v\) is zero at least through physical row 8, so its
product with \(A^\star v^\star\) is zero too. These are
genuine original paid tests of total grades 8,9,9 respectively.
The reversed response is transferred at grade four before
making any higher-grade product, so no equality of the two
grade-five pure flags is presumed. Consequently
\[
  \int U_p U_q^\star
 =\int (2X-1) U_p U_q^\star
 =\int H_p U_q^\star=0 .
\]

## No characteristic-zero common zero

Let \(M_0,M_1\) be the first two integrals multiplied by
20160, and \(M_2\) the last multiplied by 201600.
Set \(p=1+m+h,\ q=m-h,\ k=m^2-h^2\)
(the first change is invertible over characteristic zero).
Direct exact integration gives
\[
\begin{aligned}
 M_0&=48h^2-84hk+18h+42k^2-12k+2,\\
 M_1&=2m(6h-6k+1),\\
 M_2&=100h^2-160hk+50h+70k^2-35k+7 .
\end{aligned}
\]
If \(m=0\), then \(k=-h^2\) and the first and third
polynomials reduce to
\(D_0=42h^4+84h^3+60h^2+18h+2\) and
\(D_2=70h^4+160h^3+135h^2+50h+7\).
Their exact Bézout identity is
\[
 5(6510h^3+9840h^2+5025h+914)D_0
 -6(3255h^3+3990h^2+1605h+217)D_2=26 .
\]
If \(m\ne0\), the middle moment forces \(6k-6h-1=0\).
The cleared remainders of \(6M_0,9M_2\) are
\(Q_0=36h^2+36h+7\) and \(Q_2=90h^2+105h+28\).
But \((-75h-35)Q_0+(30h+9)Q_2=7\).
Thus all three moments cannot vanish in any
characteristic-zero field, including unordered fields.
No ordering, completeness, positivity, or additional
arithmetic assumptions on \(p,q\) are used.

[ERK10CubicMeanCrossoverGate.lean](ERK10CubicMeanCrossoverGate.lean)
kernel-checks the integral coefficient grids, centered forms,
Bézout identities, and the generic characteristic-zero
no-common-zero theorem. The actual rooted-space and weighted
quadrature bridges are proved above. This completes the
stated eight-label, ten-active-row cubic chart; zero
output weights are not covered.
