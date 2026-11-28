# Excluding the omitted half-plateau clock in the two-carrier ERK11 chart

**Scope.** Continue
[the two-carrier Jacobi pool exit](ERK11-TWO-CARRIER-JACOBI-POOL-EXIT.md).
The actual maximal all-live half-clock chart has exactly two carrier
rows, both first-middle boundaries are new, and the pooled \(b_i r_i\)
charges vanish at every active clock. The remaining case with
at most five active clocks had four labels, three active triples,
and one omitted active pair clock. The two clean fifth responses
are now both nonzero. This final finite check excludes that case
over any ordered field. Together these packets thus exclude
the entire indicated zero-pool, at-most-five-active-clocks branch.
They do not exclude six active clocks, nonzero pools, repeated
boundaries or the entire 17-stage problem.

Only forward order eleven and the earned reverse order-ten modeling
flag are used. In particular, no square of a reverse grade-five pure
vector is tested. ERK11TwoCarrierOmittedPairGate.lean checks the exact
clock enclosures and interval exclusions; the actual tableau
and order-to-scalar transfers are the mathematical argument below.

## 1. Two pooled pure rows and the physical plateau calibration

Let \(\theta\) be the sole carrier clock. As in the two-front reduction
put \(F=\theta r\) for the left physical response scale, and use
the corresponding right scale \(G=\kappa F\), \(\kappa\ne0\).
Write \(a\) for the physical left plateau, \(d\) for the physical
right plateau, \(b=1-d\), \(t\) for the third triple label and
\(p\) for the active pair label omitted from the ordinary scalar support.
Write \(w_1,w_2\) for the two dormant inner middle clocks.
Then the eight labels \(0,1,a,d,t,p,w_1,w_2\) are distinct.
The ordinary scalar support leaves out just \(p\).

For any physical model \(P\) anchored on the left, \(P(0)=0\),
the actual grade-five lift \(L(P)\) with zero readings on the
first six has, at every noncarrier, the form
\[
 L(P)_i=P(c_i)+F_i S_P(c_i)+h_i P(a).
\]
Here \(S_P\) is a quadratic and \(h\) is one **actual pure
grade-five vector**: the coefficient of the extra fifth-stage
pure direction in the anchored lift is a fixed multiple of
\(P(a)\), by the distinct clean plateau states. Thus
\[
  h_4=0,\qquad h_5=F_5/F_4-1 .
\]
These identities follow directly by subtracting the zero
anchored row-four and row-five reads at clock \(a\).
The analogous right anchored formula uses \(Q(d)\) and
a fixed reverse pure grade-five vector \(\bar h\), with
\(\bar h_{14}=0,\ \bar h_{13}=F_{13}/F_{14}-1\).
Both \(h,\bar h\) vanish on the two carriers: they vanish at their
respective first carrier by strictness, and the paid product with
the actual forward carrier indicator \(s\) gives the other zero.
For \(\bar h\), this product uses
\(\bar F_5\subset E_5^{\perp_B}\), not ordinary reverse order eleven.

Put \(D_8=X(X-1)(X-a)(X-d)(X-t)(X-p)(X-w_1)(X-w_2)\), and
\(D_4=(X-a)(X-d)(X-t)(X-p)\). Write \(\eta(X)=X(X-1)(X-w_1)(X-w_2)\).
For each active label \(x\), \(D_8'(x)=\eta(x)D_4'(x)\).
The actual pooled signed rows
\[
 M_x=\sum_{c_i=x} b_i h_i,\qquad
 \chi_x=\sum_{c_i=x} b_i F_i h_i
\]
have six and three vanishing clock moments, respectively.
These are paid products of grades \(5+j\), \(3+5+j\le10\).
The mirrored statements \(\bar M,\bar\chi\) follow from
\(\bar h\in E_5^{\perp_B}\): the other factors have grades
at most five in the forward space. All nonzero \(\chi\)
or \(\bar\chi\) charges are on the four active labels.
Since \(h\) vanishes at physical 1 and \(\bar h\) at physical 17,
their endpoint pools at 0 and 1 respectively are zero.
Barycentric interpolation of the exact vanishing moments gives
\[
 M_x=\frac{U x}{D'_8(x)},\qquad
 \bar M_x=\frac{\bar U(x-1)}{D'_8(x)},\qquad
 \chi_x=\frac{U k}{D'_4(x)},\qquad
 \bar\chi_x=\frac{\bar U\bar k}{D'_4(x)},
\]
where \(k=F(p)p/\eta(p),\ \bar k=F(p)(p-1)/\eta(p)\).
The last constants are fixed by the equal actual pair responses
at \(p\): \(\chi_p=F(p)M_p\) and similarly on the right.

At the triple \(a\) let its three distinct nonzero responses be
\(F_4,F_5,F_R(a)\), with \(F_R(a)\) the right front's response
in the **same** physical scale \(F\). Interpolate \(h\) on those
three states as \(\alpha+\beta F+\gamma F^2\).
The first and second pure response pools are zero. If \(B_a\)
denotes the ordinary scalar pool and \(\tau_a\) the cubic pool,
then \(M_a=B_a\alpha,\ \chi_a=\gamma\tau_a\), with
\(\tau_a=B_a F_4 F_5 F_R(a)\) by the cubic hull. Subtract the
known row-four and row-five values, dividing only by the live
\(F_4\) and \(F_5-F_4\); this gives
\(1=-\alpha+\gamma F_4 F_5\). Therefore
\[
             B_a=-M_a+\chi_a/F_R(a).
\]
The same relation at \(d\) is
\(B_d=-\bar M_d+\bar\chi_d/F_L(d)\).
Here \(F_L(d)\) is the left front's literal response at that
clock. In particular no unknown overall cubic moment scale
survives these relations.

At each off-plateau active calibration site the left and right
responses in their own units are, respectively,
\(F_L(x)=x^2(a-x)/a\), \(G_R(x)=(1-x)^2(x-d)/b\).
The common pair at \(p\) fixes \(\kappa=G_R(p)/F_L(p)\).
Hence \(F(p)/F_R(a)=G_R(p)/G_R(a)\) and
\(F(p)/F_L(d)=F_L(p)/F_L(d)\), with all denominators live.
Substituting the pooled formulas gives
\[
 B_a D'_8(a)=U S_L,\qquad B_d D'_8(d)=\bar U S_R,
\]
where
\[
\begin{aligned}
 S_L&=-a+\frac{a(1-p)(p-d)(a-w_1)(a-w_2)}
                   {(1-a)(a-d)(p-w_1)(p-w_2)},\\
 S_R&=-(d-1)+\frac{p(a-p)(d-1)(d-w_1)(d-w_2)}
                       {d(a-d)(p-w_1)(p-w_2)} .
\end{aligned}
\]
All factors in these denominators are differences or live
nonendpoint clocks; no pole or equality fiber is discarded.

## 2. The two dormant clock tests

Let \(p_a(X)=X^2(X-a)^2\), \(P_a=Jp_a\), and
\(q_b(X)=(1-X)^2(1-X-b)^2,\ Q_b=\bar J q_b\).
The actual left grade-four quartic vector for \(p_a\) vanishes
through physical 7, so its literal forward primitive is zero
at physical 8, with model \(P_a\). If this row is dormant at
clock \(w\), the anchored formula says
\(h_8=-P_a(w)/P_a(a)\). This is the sole noncarrier stage at that clock
since \(w\) is neither active, endpoint nor the other dormant
clock (the carrier pair has zero \(h\) and zero net ordinary mass).
Its ordinary weight is the scalar pool \(B_w\), so
\(B_w h_8=M_w=U w/D'_8(w)\).
Reflecting gives
\(\bar h_{10}=-Q_b(w)/Q_b(d)\) at any dormant physical 10
and the weighted pool \(\bar U(w-1)/D'_8(w)\).
There is necessarily at least one such dormant row 8 or 10,
as only one of the three inner middle rows is active.

Let \(H_5\) be the monic hull of the five interior scalar support
nodes, and \(D_7=X(X-1)H_5(X)\).
For an interior root \(x\), ordinary degree-six quadrature gives
\(B_xD_7'(x)=\int D_7(X)/(X-x)\,dX\).
Multiplying that integral by \(R_4(x)\) gives a constant
independent of \(x\): replace \(R_4(x)\) by \(R_4(X)\)
inside the integral because the difference is divisible by
\(X-x\), leaving the exact Jacobi orthogonality against the
cubic quotient. Then the leading coefficient of \(H_5/(X-x)\)
pairs with the nonzero \(R_4\) norm. The result is nonzero by
the nonsingular Jacobi Gram, and \(R_4(x)\ne0\) by coprimality
of \(R_4,R_5\). Thus \(B_xD'_8(x)\) is a single common nonzero
constant times \((x-p)/R_4(x)\).

Combine this identity with the dormant row tests, and put
\(G_A(W)=6W^2-15AW+10A^2\). Using
\(P_a(w)=w^3 G_a(w)/30,\ P_a(a)=a^5/30\), and the corresponding
reflected formulas, the necessary left and right tests are
\[
\begin{aligned}
 0&=(a-p)a^5 R_4(w)+S_L(w-p) w^2 G_a(w)R_4(a),\\
 0&=(d-p)b^5 R_4(w)-S_R(w-p)(1-w)^2G_b(1-w)R_4(d).
\end{aligned}
\]
The first is required when physical 8 is dormant, the second
when physical 10 is dormant. The clock denominators in \(S_L,S_R\)
are cleared in the exact certificate. Either orientation's
required test pays at most the original mixed grade-ten budget.

## 3. Exhaustive finite ordered-field certificate

By reflection it suffices when just one half-plateau is omitted
to let \(p=a/2\). This only interchanges the two displayed
necessary tests and the paired pure-moment deductions, not an
assumption of full order eleven in the reverse tableau.
Then \(e=1-b/2\) is a root of the scalar Jacobi hull, and
\(e=a\) or \(e=t\). The right plateau \(b\) and \(b/2\)
are both roots of \(R_5-\lambda R_4\);
\(b\) thus solves the degree-eight doubling polynomial of
the earlier Jacobi packet. Its exact signed remainder sequence
has leading signs \(+,+,+,+,+,-,-,-,+\) at descending degrees
eight through zero. The variations at negative and positive
infinity are six and two, respectively, giving precisely
four real roots. Four disjoint rational boxes with endpoint
sign changes enclose them.

For each such \(b\), the hull written without denominators is
\(R_4(b)R_5(X)+R_5(b)R_4(X)\). The known pair of roots is
\(d,e\). Three further disjoint intervals each have endpoint
sign changes uniformly over the parameter box. They therefore
enclose all remaining roots of this degree-five hull. Choose
one of those three as \(a\) when \(t=e\), or as \(t\) when
\(a=e\); the other two are \(w_1,w_2\). There are 24 such
interval charts.

If both half-plateaus are omitted, \(a+b=2\) and the two
known hull roots are \(a,d=a-1\). The degree-eight polynomial
in \(u=a-1\) from the Jacobi exit has sign changes in eight
disjoint intervals, so these enclose all real possibilities.
The hull is now \(R_4(a)R_5(X)-R_5(a)R_4(X)\).
Its three other roots each have a verified disjoint sign
interval uniformly over the corresponding parameter box.
Any one is \(t\) and the other two are \(w_1,w_2\), again
giving 24 interval charts.

For each of the resulting 48 charts, the certificate evaluates
the two **denominator-cleared** tests at **both** \(w_1,w_2\)
by fixed-grid rational interval arithmetic. All 192 resulting
intervals strictly exclude zero. The parameter endpoints
are given on a \(10^{-24}\) grid, the additional root boxes
on \(10^{-16}\), and all computations use integer endpoints
on a \(10^{-36}\) grid, rounding multiplication outward.
For example the interval product bounds contain the products
of every input point because the four endpoint products bound
the ordered bilinear rectangle; rounding lower down and
upper up preserves containment. The signs are thus exact
rational checks, not floating-point estimates or samples.

The root enclosure completeness and test signs apply over the
real closure of any ordered coefficient field. They exclude
the necessary dormant eighth- or tenth-row test on every
possible chart. This closes the stated pooled branch together
with the earlier four-pair and Jacobi doubling exits.
