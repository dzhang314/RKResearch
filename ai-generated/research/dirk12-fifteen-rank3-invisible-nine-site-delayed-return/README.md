# DIRK12/15: the delayed return on the nine-site grid

Continue the genuine weighted reverse frame of the [nine-site early-return proof](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md): exactly four distinct truly dirty ghosts, nine distinct nonterminal live labels, and the unique live pair at the first nonzero reflected label \(d\). Here the second physical \(d\)-row has not occurred before the third distinct nonzero live label \(u\). Let \(v\) be the second such label, and normalize the actual clock and actual \(N=A^{\mathsf T}\) by \(1/d\); write \(r=v/d,t=u/d\). The true \(\mathbf G\) is local at \(1\) in these units, and the true rank-two grade-four head \(\mathbf H=N\mathbf G-\mathbf G/2\) is nonzero at every other nonterminal live label and at the second \(1\)-row. All row ratios below divide only by actual nonzero live weights.

The conclusions are:

- A zero-total-mass pair cannot return before the **fourth** distinct nonzero live label. This strengthens the earlier third-label result.
- If the second \(1\)-row has not appeared before the next nonterminal live row following \(t\), that row is not a numerical zero. Write it \(w\). Then
  \[
                     (r^2-4rt+t^2)w+rt(r+t)=0
  \]
  and the literal reverse diagonal at \(w\) is zero, including its exceptional vanishing leading pivot.
- If the pair has zero mass and completes after \(w\) and before the fifth distinct nonzero label, put \(z=t/r\). Then
  \[
                 r z(z+1)(3z^2-7z+3)
                            +2(z-1)^2(z^2-4z+1)=0 .
  \]
  Its coefficient of \(r\) cannot vanish, so the chronology fixes \(v/d=r\) in terms of \(u/v=z\). No claim is made here that all later returns are impossible.

These are exact restrictions on the literal real fifteen-stage order-twelve equality chart, with the interval still **15–16**.

## The third live head before a return

Put \(\sigma=1/6,\ \lambda=3(r-1)(r-2)\), the known coefficient of \(\mathbf H\) in the genuine cubic-input discrepancy \(\mathbf E_4=\frac32\mathbf G+\lambda\mathbf H\). The actual first \(r\)-row has tap \(r^3/[6(r-1)]\) to the sole earlier \(1\)-row, diagonal \(a_r=r(2r-3)/[6(r-1)]\), and normalized head \(h_r=r^3/[36(r-1)]\). Let \(h_t\) be the normalized head at \(t\). Its actual \(1\)-tap, using the scalar cubic node cardinal, is
\[
            T_1^{(t)}=\frac{t^3(2r-t)/12+\lambda h_t}{(1-r)(1-t)}.
\]
Since \(1\) has not returned, \(N\mathbf G=\mathbf H\) at \(t\) gives \(h_t=\sigma T_1^{(t)}\), and so
\[
                      h_t=\frac{t^3(2r-t)}{36(r-1)(2t-r)}.
\]
In detail the predivision equation is \(36(r-1)(2t-r)h_t=t^3(2r-t)\). If \(2t=r\), its right side is nonzero since \(r,t\ne0\); if \(t=2r\), the nonzero denominator would force \(h_t=0\). Thus both linear factors are nonzero. No assumption that \(\lambda\ne0\) is used; it might vanish when \(r=2\).

Suppose the next new live label were a numerical zero before any return. Its actual scalar taps to \(1,r,t\), divided by the nonzero normalized \(h\) at the zero row, are \(\lambda\) times the leading cubic coefficients of the scalar cardinals on \(0,1,r,t\), by the exact zero first two moments. Again \(h=\sigma T_1\). Hence \(6(1-r)(1-t)=\lambda\), exactly \(2t=r\), contradiction. Extra live numerical zero was already excluded through \(t\) in the earlier proof.

## A zero-mass pair requires more than three nonzero debuts

The earlier proof excludes a zero-mass return before \(t\). If such a pair completes after \(t\) and before the fourth nonzero label, its two normalized cubic amplitudes at \(1\) agree, equal to \(\sigma\), since the physical output weights are opposite and \(\mathbf G\) is centered. At the second \(1\)-row the normalized nonzero \(H\)-amplitude \(h\) satisfies \(T_1=1/2+6h\) by the genuine \(N\mathbf G\) relation. Subtract the diagonal baseline \(T_1=1/2\); write \(U_1=6h,\ U_r=T_r,\ U_t=T_t\). The true leading moments give zero changes at inputs \(X\) and \(X^2\); the true cubic input gives change \(\lambda h\). But the difference of the cubic action from baseline is
\[
   6h+r^3U_r+t^3U_t=6(1-r)(1-t)h ,
\]
because the two subtracted moment equations have \(r U_r+t U_t=r^2 U_r+t^2 U_t=-6h\). This again forces the impossible \(2t=r\). Any intervening live zero contributes to none of the three nonconstant reads and does not alter the conclusion.

## The exact fourth-clock equation without a return

Write \(\mathbf E_5=(9/5)\mathbf G+\varphi(Y)\mathbf H\) and \(N\mathbf H=\psi(Y)\mathbf H\). These true grade-five polynomials \(\varphi,\psi\) are affine, with the \(\mathbf G\) coefficients fixed on the first \(1\)-row as in the earlier proof. This time \(r,t\), both before the return, determine the affine interpolants. Their exact values are
\[
\begin{aligned}
 \varphi(r)&=(r^3/[6(r-1)]+a_r r^4-r^5/5)/h_r, & \psi(r)&=a_r,\\
 \varphi(t)&=(1+r+t)\lambda
                    -J[X(X-1)(X-r)(X-t)](t)/h_t,
 &\psi(t)&=T_t^{(t)}+h_r T_r^{(t)}/h_t .
\end{aligned}
\]
The taps at \(t\) are the usual cubic Lagrange integrals plus \(\lambda h_t\) times their leading cardinal coefficients. At \(t\), the only contributing earlier head is at \(r\), since the first \(1\) has zero \(\mathbf H\).

Let \(w\ne0,1,r,t\) be the next distinct nonzero live label, still without a return, with normalized head \(h\ne0\). Its scalar taps on \(1,r,t,w\) are affine in \(h\), via the quartic cardinals on \(0,1,r,t,w\): for \(x\) among the nonzero labels, with other labels \(p,q,s\),
\[
              T_x=\frac{J[X(X-p)(X-q)(X-s)](w)
                         +(\varphi(w)-\lambda(p+q+s))h}
                               {x(x-p)(x-q)(x-s)}.
\]
The actual row has \(h=\sigma T_1\). Write this as \(a h+b=0\). Its actual \(N\mathbf H\) equation is \(q_2h^2+q_1h+q_0=0\), the coefficient expansion of
\[
                   (T_w-\psi(w))h+h_rT_r+h_tT_t=0 .
\]
The exact replay, without dividing by \(a\), verifies
\[
 q_2 b^2-q_1ab+q_0a^2=
 \frac{w^3(r-w)(t-w)
         \big[(r^2-4rt+t^2) w+rt(r+t)\big]^2}
       {1200(r-1)(r-2t)(2r-t)^2(t-1)^2(w-1)^2}.
\]
Every denominator and external numerator factor is nonzero by the physical controls above. The common root makes the left side zero, proving the new ratio.

Let \(Q=r^2-4rt+t^2\) and \(P=r^2-3rt+t^2\). The ratio implies \(Q\ne0,r+t\ne0\), since \(r,t,w\ne0\). If \(P\ne0\), the linear equation has nonzero leading coefficient and gives
\[
 h_w=-\frac{r^3t^3(r+t)^2(2r-t)(5r^2-14rt+5t^2)}
                    {36(r-1)Q^4}.
\]
Its actual tap \(T_w\) vanishes. If \(P=0\), put \(z=t/r\); then \(z^2-3z+1=0\) and \(w=r(1+z)\). The exact replay in the quadratic coefficient quotient checks \(a=b=0\) and that the genuine quadratic is \(q_2(h-h_w)^2=0\) with the same \(h_w\). Here \(q_2\ne0\) even after the actual \(r\) is specialized. Its numerator, after clearing the explicitly nonzero cardinal denominators, reduces up to a nonzero constant to
\((r-1)(4rz-r-z)=(r-1)z(w-1)\ne0\).
Thus \(h=h_w\) and the actual diagonal is zero also in this exceptional branch. The cases use real or characteristic-zero field calculations; no clock ordering by sign is assumed.

## The next zero-mass return constrains \(v/d\)

Suppose the zero-mass pair completes after the fourth distinct nonzero label \(w\) but before the fifth. As before \(T_1=1/2+6h\) at the second \(1\)-row and \(h\ne0\). After subtracting the \(1/2\) baseline, the first four nonconstant degree reads on the four labels \(1,r,t,w\) have discrepancies respectively \(0,0,\lambda h,\varphi(1)h\). The cardinal at \(1\) therefore gives
\[
              6(1-r)(1-t)(1-w)=\varphi(1)-\lambda(r+t+w).
\]
Substitute the exact fourth ratio. The verified difference factors as
\[
 \frac{9(r-1)r^4}{5(2r-t)Q}
 \left[r z(z+1)(3z^2-7z+3)
                     +2(z-1)^2(z^2-4z+1)\right],
         \quad z=t/r.
\]
The prefactor is nonzero; thus the bracket vanishes. Its constant term is nonzero because \(z\ne1\) and \(z^2-4z+1=Q/r^2\ne0\). Therefore its coefficient of \(r\) is nonzero as well, and \(r\) is fixed by \(z\). A possible additional live zero before this return does not enter any of the four nonconstant reads; the literal row count does not require it to be absent.

The exact symbolic replay specializes only under the displayed quadratic relation and explicit literal denominators, not a reduction of arbitrary tableau entries. This note has no complete native exclusion. The [early-return native gate](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md) certifies its separate guarded resultant and scalar moments, not the larger identity here.

    python3 -B verify.py
