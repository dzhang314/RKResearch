# Opposite halves, different free labels: no opposite dormant edge

**Scope.** Continue the [opposite-halves finite atlas](ERK11-NINE-SITE-OPPOSITE-HALVES-FINITE.md)
and [pivot exclusions](ERK11-NINE-SITE-OPPOSITE-HALVES-PIVOTS.md):
four distinct calibrations, left extras \(\{e,t\}\), right
extras \(\{h,s\}\) with \(t\ne s\), and genuine nine-site
separation. At physical 8 dormant the opposite orientation is
\(c_8=z,c_9=s,c_{10}=t\). This excludes it and the reflected
physical-10 orientation over characteristic zero.
Together with the [central](ERK11-NINE-SITE-OPPOSITE-HALVES-CENTER-EXIT.md)
and [matched-edge](ERK11-NINE-SITE-OPPOSITE-HALVES-EDGE-MATCHED-EXIT.md)
exclusions this closes the whole opposite-halves different-free
geometry. In particular the asymmetric one-side-half crossing
geometry is not covered.

## 1. Actual front slope and two independent shifted rows

Put \(R_0=(h-d)(s-d)\), \(R_1=-(1-h)(1-s)\),
\(F_0=R_0+T_4(b)R_1\), and
\(F_1=T_4(a)R_0+U_{4,4}(a,b)R_1\).
The first Gram contact gives
\[
 T_D t=T_N,\qquad T_D=(a-e)F_0+eF_1,\quad
 T_N=a(a-e)F_0 .
\]
If \(T_D\) were zero, the equation would force \(T_N=0\),
hence \(F_0=0\) and then \(F_1=0\), since \(a,e,a-e\) are
all nonzero. But the map \((R_0,R_1)\mapsto(F_0,F_1)\)
has determinant \(abR_{33}\ne0\), and the original
\(R_0,R_1\) are literal nonzero clock products. This
earns \(T_D\ne0\). It is not a generic slope assumption.

The paid middle products give \(B(z,t)=0\) for the present
physical order. Set
\[
 Z_D=A_0T_N+B_0T_D,\qquad Z_N=-(C_0T_N+D_0T_D).
\]
Then \(Z_D z=Z_N\). If \(Z_D=0\) the affine consistency
test forces \(A_0D_0-B_0C_0=0\), contrary to the
separately proved nonzero width determinant. Thus
\(z=Z_N/Z_D\); no model amplitude is divided out.

Let \(m_j=\int X(1-X)P_4X^j\) as before and
\(M_j=Z_Dm_{j+1}-Z_Nm_j\), \(0\le j\le3\).
The two true shifted nodal tests at the remaining sites
\(t,s\) say
\[
 A_j=T_D(M_{j+2}-sM_{j+1})-T_N(M_{j+1}-sM_j)=0,\qquad j=0,1 .
\]
They are exactly the two paid degree-nine and degree-ten
scalar moments with \(X-z\) and \((X-t)(X-s)\), not a third
unpaid shifted row. The proof does not assume a positive weight
or the degree of a specialized polynomial in \(s\).

## 2. Weighted actual row-9 repeat

Now \(s\) is the **right-only** label, at physical 9, not 10.
Its reverse primitive is not presumed zero. At its earlier
front read in reverse chronology the actual primitive is zero.
As in the repeated-exclusive lemma, eliminating the pure response
direction in the two anchored rows gives
\[
 \sigma_s\langle\Phi_L,D_s^R\rangle_N+
          30Q_9\langle\Phi_L,r_d\rangle_N=0,\qquad
 (V_R)_9=\sigma_s V_b(s),
\]
where \(Q_9=(A^\star V_R)_9\).
The early and late pair responses and their difference are live
by true calibration and the literal pair law. The two rows can
be paired off-diagonally with the actual forward row 7;
the local sixth anchor is zero when it occurs there.

Put \(P_9=(AV_L)_9\), and let \(b_9\) be its physical output
weight. The already-paid grade-ten products with
\(AV_L,(C-t)V_R\) and with \(AV_L,A^\star V_R\) give
\[
 C_1-tH=b_9P_9(s-t)(V_R)_9,\qquad J_0=b_9P_9Q_9 .
\]
The first clock factor kills physical 10 and the primitive
supports confine both products to physical 9.
Multiply the actual repeat equation by
\(b_9P_9(s-t)V_b(s)\); then divide only the live clock factor
\((1-s)(s-d)\) by using the polynomial quotient defining
\(M_j^R(s)=K^R_j(s)\). The exact necessary mark is
\[
 \mathcal M=
 b(C_1-tH)\bigl(L_0 M_0^R(s)+L_1 M_1^R(s)\bigr)
 +30(1-s)(s-d)(s-t)J_0\langle\Phi_L,r_d\rangle_N=0 .
\]
Thus neither \(P_9\), \(Q_9\), nor a square-clock amplitude
is implicitly assumed nonzero in the multiplication.
Substitute \(t=T_N/T_D\), and clear its independently live
denominator in the two reflected derivative basis coefficients.
The matrix and cubic formulas are the same exact ones as in
the [central calculation](ERK11-NINE-SITE-OPPOSITE-HALVES-CENTER-EXIT.md).

## 3. Combine the true nodal and pivot-free projections

Take \(s\)-resultants of \(A_0\) against \(A_1,\mathcal M\);
here \(A_0,A_1\) in this sentence are the two nodal polynomials
\(A_j\) of Section 1, not a coefficient of \(B\).
Remove only factors dividing the known nonzero expressions
in the receipt: calibration separations, \(H,J_0,R_{33},U_F,\Omega\),
the two earned slopes, and the actual pairwise clock differences
after clearing them. If \(I(s,t)\) is used as a divisor,
it is independently live by the literal dormant-only product
of the two square-clock masks, whose models are nonzero at \(z\).
The resulting necessary width polynomials \(W_{AB},W_{AM}\)
have bidegrees \((44,44),(50,48)\) in \((b,a)\).

Use also the **pivot-free** width polynomial \(W_B\) from the
finite atlas for this physical order: the reduced dormant
resultant of the crossover \(X_c\) with the middle norm \(N_B\).
Its bidegree is \((64,60)\). This third width equation
is not obtained by specializing the first two to a vanished
derivative rank or dividing by any late response scale.

With primitive integral coefficient polynomials, take the
two \(b\)-resultants of \(W_{AB}\) with \(W_{AM},W_B\).
Modulo \(103\) their input \(b\)-degrees are preserved,
their \(a\)-degrees are \(4244,5432\), and their monic
common gcd is exactly \((a-2)^{16}\).
The checked entrywise integer Sylvester exponent bounds
are \(4312,5456\). The exact constant-row valuation at
\(a=1/u\) earns at least \(68,24\) powers of \(u\) for the
correspondingly scaled determinants. This proves, over
the rationals, precisely the upper bounds \(4244,5432\)
needed for degree preservation at the prime. In addition
the exact finite valuations at \(a=2+u\) earn at least
16 powers in each unscaled Sylvester determinant.

Thus the entire monic \((a-2)^{16}\) is a true common
characteristic-zero divisor. After removing it, both
degrees are still preserved and the reductions are
coprime. The
[constant-row method](ERK11-NINE-SITE-OPPOSITE-HALVES-CENTER-EXIT.md)
does not reduce a hypothetical tableau modulo the
prime or discard an algebraic fiber. A true width must
therefore have \(a=2\), which forces the forbidden
\(h=1\). Reflection of the paid mixed slots covers
the opposite dormant physical-10 choice without invoking
ordinary reverse order eleven.

The standalone replay uses exact Python rational and
modular arithmetic, with the declared determinant scales
and finite factor lift. Existing Lean gates cover the
cleared scalar row and shifted identities, not the
large resultant computation.
