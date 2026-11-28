# Nine physical zero clocks: corrected cardinal and reverse Bézout identity

At the ten-stage strict SDIRK8 floor over a characteristic-zero field, suppose the only nonzero quadratic defect is at the individually weight-zero first stage. Assume the nine remaining physical clocks are pairwise distinct. Consider either nine physically active rows, or eight active rows with a unique further silent row \(\zeta\) whose actual reverse read \(w_\zeta\ne0\). No conclusion is asserted for repeated physical clocks or any unconditional stage bound. This is a nodal reduction, not an exclusion.

Use the [earlier active-four rank and nodal packet](../sdirk-eight-silent-one-eight-reverse-vanish/README.md) for notation \(A,B,C,M,N,\boldsymbol g,\boldsymbol h,\boldsymbol w\) and the paid flags. Let \(x=c_{10}=1-\gamma\), \(u=(x-c_9)/\gamma\ne0\), \(k=1+2u-u^2\). The actual reverse row vanishes at the first stage, \(w_1=0\), while \(w_{10}=-\gamma^2 b_{10}\ne0\). If \(k=0\), the actual \(\boldsymbol w(C-xI)=0\) confines its support to \(x\); distinctness on the nine zero rows leaves only the terminal entry and contradicts \(\boldsymbol w\boldsymbol 1=0\). Thus \(k\ne0\). The cubic defect is detected since at least one of the two literal front rows with nonzero \(h\) is active. Accordingly
\[
 \boldsymbol h^{\mathsf T}B=\boldsymbol wP_1(C)
\]
for a nonzero affine scalar polynomial \(P_1\), as the actual two reverse pure rows are \(\boldsymbol w,\boldsymbol wC\).

## Three scalar numerators

Let \(D\) be the monic polynomial of the nine pairwise distinct physical zero clocks, including an individually silent clock if present. Define degree-at-most-eight interpolation polynomials
\[
  T(c_i)=D'(c_i)w_i,\qquad
  S(c_i)=D'(c_i)w_i h_i,\qquad
  R(c_i)=D'(c_i)b_i.
\]
These definitions use actual rows on all nine sites, not weights normalized at the silent stage. The six vanishing scalar \(w\) moments and the three \(w h\) moments give \(\deg T\le2\) and \(\deg S\le5\), by the coefficient expansion of \(D(X)/(X-c_i)\). The other row, stage one, contributes zero to them. The actual identity \(S(c_i)=T(c_i)h_i\), ordinary precision through degree seven, and the paid defect moments through degree four imply
\[
  I(X^j S)=\sum_{i=2}^{10}b_i c_i^j T(c_i)h_i=0
  \qquad (0\le j\le2).
\]
Thus \(S\) belongs to the span of the shifted Legendre polynomials \(L_3,L_4,L_5\). The polynomial \(T\ne0\) by the terminal value. If \(S=0\) then nonzero active \(h_i\)'s can occur only at the at most two roots of \(T\), and the first two paid defect moments at those distinct physical stages force their signed masses to be zero. This contradicts defect detection, so \(S\ne0\).

Write
\[
 I(f)=\int_0^1 f(Y)\,dY,\qquad W_U(X)=I((U(X)-U(Y))/(X-Y)),
 \qquad \delta=\sum_i b_i c_i^8-1/9 .
\]
The polynomial \(D(Y)/(Y-c_i)\) is monic of degree eight. Its ordinary signed tableau read is \(b_i D'(c_i)\), whereas its true integral is \(W_D(c_i)\). The table pays only degree seven, and the missing leading moment contributes the **same constant** \(\delta\) at every site. Hence \(R=W_D+\delta\), not \(R=W_D\), including at an individually silent site.

## Exact scalar equation and support consequences

The actual affine reverse read gives \(R(c_i)S(c_i)=P_1(c_i)T(c_i)^2\). Separating the two divided differences and using \(I(Y^j S)=0\) for \(j\le2\) shows that
\[
 S W_D-D W_S
   =I\!\left(\frac{D(X)-D(Y)}{X-Y} S(Y)
             -\frac{S(X)-S(Y)}{X-Y}D(Y)\right)
\]
has degree at most five in \(X\). Both \(\delta S\) and \(P_1T^2\) also have degree at most five. Thus the nine physical evaluations give the exact identity
\[
 \boxed{\, S(W_D+\delta)-D W_S=P_1 T^2 \,}.
\]
This uses precisely the paid moments, not an extra precision-eight quadrature assumption. Its scalar weighted nodal product is the same identity verified in the [native eight-site receipt](../../lean/RKCert/ReviewedNative/SDIRK8EightActivePureSupport.lean).

At a separate silent \(\zeta\) with \(w_\zeta\ne0\), \(P_1(c_\zeta)=0\), \(T(c_\zeta)\ne0\), and \(W_D(c_\zeta)+\delta=0\); these facts do not force \(h_\zeta=0\). At an active stage \(h_i=0\) precisely when \(P_1(c_i)T(c_i)=0\). Hence with nine active stages there are at most three zero \(h_i\)'s, and with eight active stages and the contact root occupied by \(\zeta\), at most two on the active rows. Any active root of \(T\) is also a root of \(S\) and must use its actual amplitude \(h_i=0\), not a substituted value after rational cancellation.

Where \(\deg T\le1\), the fourth scalar \(h\)-probe gives \(I(X^3 S)+[X^5]S\,\delta=0\). Consequently if \(\deg S\le4\), then necessarily \(S\) is proportional to \(L_4\); if \(\deg S=5\), this determines \(\delta\) from \(S\). In the general chart, reduction of the boxed identity modulo \(S\) reconstructs \(D\bmod S\) whenever \(W_S\) is invertible there. Otherwise the exact necessary condition is \(\gcd(S,W_S)\mid P_1T^2\); the common-factor cases remain separate. Neither version assumes ordering or positivity of the ordinary weights.

The small exact scalar replay **python3 check_legendre.py** verifies the \(L_3,L_4,L_5\) basis and associated invertible moment matrices with the Python standard library. The flag and nodal deductions above are source mathematics.
