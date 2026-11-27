# Three crossing pairs are impossible in the all-live ERK10 equality case

Assume a fourteen-stage ERK tableau of rooted order ten over a
characteristic-zero field with every output weight live. In the
[two-carrier equality branch](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md),
suppose the pooled \(br\) measure is zero and exactly five active
clock labels occur, each twice. Here \(s\) is the quadratic-carrier
indicator, \(r=As\), and \(C\) is the clock diagonal.
By the [carrier census](ERK10-THREE-CARRIER-EXCLUSION.md), every
pair has unequal, nonzero \(r\)-values and nonzero ordinary pooled
weight. The [one-crossing exit](ERK10-FIVE-PAIR-ONE-CROSSING-EXCLUSION.md)
closes one of the two possible ways these five pairs can meet the
physical \(7|7\) cut. **This note excludes the other way**, three
crossing pairs. Together these notes close the entire all-live
zero-pooled five-label chart over characteristic zero, without
an order or a completeness assumption on the field.

## 1. Actual clock layout and endpoint guard

The only inactive noncarrier rows are physical 1 and 14, at
clocks 0 and 1. The physical carrier rows 2 and 13 have a
common clock and cancelling weights. By the
[doubled literal entrance](ERK10-DOUBLED-ENTRANCE-TRIPLET-EXCLUSION.md)
there is one complete pair 4/5 at clock \(p=2t,\ t=c_3\ne0\)
and one complete pair 10/11 at clock \(q=2\tau-1,\ \tau=c_{12}\ne1\).
These pairs are separate, so \(p\ne q\). With three crossing
pairs, the three cross labels are exactly the labels on physical
3,6,7 on the left and on physical 8,9,12 on the right.
In particular \(t\) and \(\tau\) are cross labels; they may agree.
Write \(y=c_6,\ z=c_7\); then \(t,y,z\) are distinct, and also
distinct from \(p,q\).

All five active labels are off both endpoints. Otherwise the
ordinary clock support, after carrier cancellation and including
the anchor endpoints 0 and 1 even if their net mass cancels,
has at most six distinct sites. With at most five it is
impossible by the degree-nine anchored Beta Gram: multiply
the monic hull of the at most three other sites by \(X(1-X)\)
and test against all polynomials of degree at most three.
With exactly six, the four nonendpoint labels are the four roots
of \(L_4=42X^4-84X^3+56X^2-14X+1\), by the analogous
four anchored moments uniquely determining their monic hull.
If \(p=1\) or \(q=0\), one of \(t,\tau\) is \(1/2\),
where \(L_4=1/8\). If \(t=1\) or \(\tau=0\), then \(p=2\)
or \(q=-1\), where \(L_4=197\). The other endpoint cases
for \(t,p,\tau,q\) violate the literal entrance guards.
If the endpoint is instead at a different crossing label,
\(t,p=2t\) are both roots of \(L_4\), contradicted by the
checked \(L_4(X),L_4(2X)\) Bézout identity in the doubled
entrance note. No divisions by a potentially collapsed
endpoint factor will be needed below.

Let \(D\) be the monic hull of the five active labels,
and let \(\omega_x\) denote the ordinary pooled weight
at one such label. The four paid moments of \(br^2\),
with zero grade-six model, give
\[
 \mu_x=(br^2)_{\mathrm{pooled},x}=
                  \kappa/D'(x),\qquad \kappa\ne0.
\]
This is the one-dimensional five-node Vandermonde kernel.
At each cross label write \(r_L(x),r_R(x)\) for its actual
two nonzero amplitudes. From the two-point identity and
zero pooled \(br\),
\[
                 \omega_xr_L(x)r_R(x)=-\kappa/D'(x).
\]
These facts are exactly the five-label case in the cited
carrier census, not any assumption about ordering or sorting.

## 2. A two-read seam kills the literal row-7 response

The common grade-four pure flag is
\(\langle s,r,Cr\rangle\). Let \(Q_R\) be the cubic
interpolating \(0\) at 1 and \(-r_R\) at each cross label.
These are four distinct knots by the endpoint guard.
Put \(P_R=(X-q)Q_R\). Its actual grade-four lift
\[
           v_R=P_R(c)+(C-q)r-P_R(\theta)s
\]
vanishes on rows 8–14: at the three crosses by interpolation,
at 10/11 by the factor \(X-q\), at 13 by the carrier correction
(the carriers have \(r=0\)), and at 14 by the anchor.
Its scalar model is \(P_R\), since both added terms are pure.

Use \(B_L=X(X-t)(X-p)\) and its actual grade-three lift
\(v=B_L(c)-B_L(\theta)s\), zero through row 5.
Write \(U_p=JB_L=X^2(X-p)^2/4\) and
\(H_p=J^2B_L=X^5/20-pX^4/8+p^2X^3/12\),
where \(J=\int_0^X\); these formulas use \(p=2t\).
The actual grade-five \(A^2v\) is zero through row 7.
The actual grade-four lift of \((X-y)B_L\), corrected
at the carrier, is zero through row 6, so its advance
is likewise zero through row 7. Their respective products
with \(v_R\) are identically zero, each paid at grade \(5+4=9\).
Their scalar integrals, using
\(J[(X-y)B_L]=(X-y)U_p-H_p\), therefore give
\[
                      \int_0^1 (X-y)U_p P_R=0 .
\]
The scalar integrand has degree at most nine.
Its ordinary quadrature support reduces to exactly two
possible sites, \(t,z\): at the other active sites \(p,q,y\)
a displayed factor vanishes, the endpoints are killed by
\(U_p(0)\) and \(P_R(1)\), and the carrier pair cancels.
Consequently, up to a common nonzero sign or constant, the
two-read equation is
\[
 \sum_{x=t,z}\omega_x (x-y)x^2(x-p)^2(x-q)r_R(x)=0.
\]
For \(x=t,z\), use
\[
 \omega_x r_R(x)=-\frac{\kappa}{D'(x)r_L(x)},\qquad
 D'(x)=(x-p)(x-q)(x-y)(x-x'),
\]
where \(x'\) is the other of \(t,z\).
Every canceled difference is between distinct active labels,
both \(r_L\) are nonzero, and \(\kappa\ne0\).
It follows that
\[
 \frac{t^2(t-p)}{r_L(t)}=\frac{z^2(z-p)}{r_L(z)}.
 \tag{1}
\]

The genuine physical grade-four \(Av\) has model \(U_p\), so
\(Av=U_p(c)+(\alpha+\beta C)r+\gamma s\).
It is zero through row 6. At either active row with clock
\(p\) this gives \(\alpha+\beta p=0\), since \(U_p(p)=0\).
At row 3, \(t\ne p\) and the equation is
\(t^2(t-p)/4+\beta r_L(t)=0\).
Now (1) gives the same equation at row 7, hence \((Av)_7=0\).
In fact \(A_{76}=0\), because the stage-6 term is the only
possible contribution to that read and
\(v_6=y(y-t)(y-p)\ne0\).
In particular \(Av=0\) through row 7, and \(A^2v=0\)
through physical row 8.

## 3. The resulting grade-nine mixed zero

The actual reversed tableau has full order ten, and its
graded numerical spaces and pure spaces through grade four
are the original ones. In unpermuted physical coordinates
its unary operator is \(A^\star=B^{-1}A^{\mathsf T}B\),
strictly upper triangular. The original-clock scalar
primitive for it is \(\bar J=\int_X^1\).
Use \(B_R=(1-X)(X-\tau)(X-q)\) and the reflected carrier
correction. Its actual numerical grade-three lift vanishes
at rows 10–14, so its **strict reversed advance** is zero
at rows 9–14, including row 9 even though the input at
row 9 may be nonzero. Its reversed model is
\(U_q^\star=(1-X)^2(X-q)^2/4\), by \(q=2\tau-1\).
The original model is the same as the reflected model in
the original variable at grade four. Its product with
\(A^2v\) is zero, since one vanishes through row 8 and the
other from row 9 onwards. This is a true grade \(5+4=9\) test
and uses no equality of the original and reversed grade-five
pure flags. Thus
\[
        I(p,q):=201600\int_0^1 H_p U_q^\star=0.
 \tag{2}
\]
Direct coefficient integration gives
\[
 I=70p^2q^2-80p^2q+25p^2-60pq^2+75pq-25p
                    +15q^2-20q+7 .
\]
For real inputs (2) is already impossible: \(H_p\) is the integral of
\(X^2(X-p)^2/4\) from 0 to \(X\), and the second factor is another
nonzero square on \((0,1)\). The next section avoids ordering and
proves the contradiction in every characteristic-zero field.

## 4. Exact unordered scalar certificates

Put \(T=2t-1,\ U=2\tau-1\). Then \(p=1+T,\ q=U\).
We use the independent anchored quadrature condition on the active
hull: in centered coordinates \(Z=2X-1\) the hull is orthogonal
to \(1,Z,Z^2\) for \(1-Z^2\), because both endpoint anchors kill
the rest of the ordinary clock support. In each case every test
has degree at most nine, and carrier cancellation is exact.

**Equal cross clock, \(t=\tau\).** The common centered clock
\(T\ne0\), since \(T=0\) would make \(p=1,q=0\).
The active hull is \((Z-T)((Z-2T)^2-1)\) times a
monic quadratic for the other two cross labels. The identical
anchored determinant from the one-crossing note gives
\(F(T)=126T^6-138T^4+51T^2-5=0\).
Equation (2) becomes \(7 M(T)=0\), where
\(M(T)=10T^4-5T^2+1\).
The exact Bézout identity
\[
 (1475-450T^2)F+(11103-21960T^2+5670T^4)M=3728
\]
contradicts this.

**Different cross clocks, \(t\ne\tau\).** Define
\(m=(T+U)/2,\ h=(T-U)/2,\ k=m^2-h^2\).
Writing \(V\) for the fifth centered active label, the centered
hull is \((Z-V)Q\), where
\[
 Q=((Z-m)^2-h^2)((Z-2m)^2-(2h+1)^2).
\]
Let \(M_j=(315/4)\int_{-1}^1(1-Z^2)Z^jQ(Z)\,dZ\).
The paid conditions are \(M_{j+1}=V M_j\) for \(j=0,1,2\).
The coefficient calculation gives
\((M_0,M_1,M_2,M_3)=(12a,12mb,4c,12md)\), with
\[
\begin{array}{ll}
 a=35k^2-35kh+14k+14h^2-7h-1,& b=-21k+14h-1,\\
 c=21k^2-21kh+24k+18h^2-9h-1,& d=-9k+6h-1 .
\end{array}
\]
Also \(I(1+m+h,m-h)=E(k,h)=70k^2+e(h)k+f(h)\), with
\(e=-160h-35\) and \(f=100h^2+50h+7\).

If \(m=0\), \(M_2=V M_1=0\). Thus
\(C_0=c(-h^2,h)=21h^4+21h^3-6h^2-9h-1=0\).
Equation (2) gives
\(E_0=E(-h^2,h)=70h^4+160h^3+135h^2+50h+7=0\).
The exact identity
\[
 (-62335-376275h-772950h^2-526050h^3) C_0
 +(-8817-70920h+28980h^2+157815h^3)E_0=616
\]
excludes this case.

If \(m\ne0\), two anchored minors give
\(a c-3(k+h^2)b^2=0,\ 3a d-b c=0\), regardless of whether
any \(M_j\) or \(V\) vanishes. The two explicit
cleared remainders in the Lean companion now give
\(a_1(h)k+a_0(h)=b_1(h)k+b_0(h)=0\), with
\[
\begin{aligned}
 a_1&=1440h^3+47760h^2+45780h+7287,\\
 a_0&=-480h^4-62640h^3-84708h^2-33838h-4473,\\
 b_1&=-11520h^2-9660h-2331,\\
 b_0&=15600h^3+17460h^2+6622h+805 .
\end{aligned}
\]
For each such linear equation \(uk+v=0\), its division-free
norm \(70v^2-euv+fu^2\) vanishes with \(E=0\), by the exact identity
\[
70v^2-euv+fu^2=u^2 E-(70uk+eu-70v)(uk+v).
\]
The two norms are \(6272 R_1(h)\) and \(112 R_2(h)\).
The Lean companion specifies their integer coefficient lists
and checks an exact integer Bézout combination with a **nonzero**
constant. This excludes their common vanishing in characteristic
zero. The independent shorter mod-37 coefficient certificate is
also recorded; the exact integer combination does not require
any argument about good reduction. No slope, norm leading
coefficient, clock ordering or putative denominator is used as
a divisor in this last case.

## Verification scope

[ERK10FivePairThreeCrossGate.lean](ERK10FivePairThreeCrossGate.lean)
checks the mixed and anchored moment coefficient calculations
(on full degree-bounded integer grids), the two small Bézout
identities, the exact cleared minor remainders and norms, and the
full coefficient Bézout combination. It also proves the scalar
contradictions for both clock cases and an abstract strict
physical-cut lemma. The literal RK space, interpolation,
moment budgets, and supplying the actual stage masks above
are mathematical proofs using the previously earned equality
flags. This gives no unrestricted numerical change to ERK10
14–15. The all-live nonzero-pooled eight-label, ten-active-row
cubic mean and the general zero-output cases are separate.
