# Rational obstruction for the reflection-suffix Christoffel chart

In the [seven-distinct-active, two-zero-weight](../strict-sdirk7-two-ghost/README.md)
order-seven chart, assume that the affine second-adjoint numerator \(W\)
vanishes at an active site \(e\). This [Christoffel clock atlas](../strict-sdirk7-two-ghost-mass/README.md)
excludes the entire **reflection suffix \(v=4-u\) over \(\mathbb Q\)**:
no symmetry of the other four clocks and no particular first forward
clock are assumed. The arithmetic suffix is not excluded. The
result also does not address other weight masks, repeated clocks,
or virtual zeros coming only from the multiplier of \(W\).

## Clock pencil and fourth read

Write \(m=z/2\ne0,\ \eta=(e-m)/m\), where \(z\) is the reciprocal
diagonal. At \(1,u,v\) the ratios are \((-1/2,M/2,M/2)\),
\(M=u^2-4u+2\), and \(R_3(Y)=(Y-1)(Y-u)(Y-v)\).
All three ratios and clocks are admissible and distinct. For
every cubic \(f=\sum a_iY^i\), the functional
\(\nu(f)=\sum_{y=1,u,v} f(y)/(r_yR_3'(y))\)
equals \(2(a_0+a_1+2a_2+6a_3)/M\). This follows by the
commutative-ring reflection opener identity in the atlas.
Thus \(\nu\), up to nonzero scale, has moments \(1,1,2,6\),
independently of \(u\).

The previously constructed Christoffel residue condition says
\(\nu(g)=0\), where \(g\) is the uniform degree-three kernel at \(e\).
Use the polynomial normalization
\[
\begin{aligned}
 A&=35\eta(5\eta^2-3),& B&=15(3\eta^2-1),\\
 C&=15\eta(5-7\eta^2),& V&=9-15\eta^2,\\
 g(Y)&=A(Y-m)^3+B m(Y-m)^2+C m^2(Y-m)+V m^3 .
\end{aligned}
\]
This is \(4m^3\) times the uniform kernel. Write \(g_j\) for the
coefficient of \(Y^j\). The opener is
\(F=g_0+g_1+2g_2+6g_3=0\).
If \(\eta=0\), it becomes \(-6m(m^2-5m+5)=0\), already
impossible over \(\mathbb Q\). Otherwise \(g_3\ne0\), because
the remaining zeros of \(\eta(5\eta^2-3)\) are irrational.

The active Christoffel site cannot be among the final three
since their ratios are nonzero. If \(e\) is fourth, its fourth
read gives \(G(e)=0\), where the reflection polynomial
\(6G(Y)=Y^3-9Y^2+18Y-6\) is projectively rootless mod 5.
This case is native in
[no_late_reflection_mass](../../lean/RKCert/Research/SDIRKSevenChristoffelReflection.lean).

Otherwise \(e\) precedes the fourth site \(c\). Use the earlier
identity \(g-qL=\kappa R_3\) with \(q=1-2Y+Y^2/2\) and affine
\(L=L_0+L_1Y\). After clearing \(3M\), the fourth read is
\(2L(Y)+\kappa(5M-4+(4-M)Y)=0\) at \(Y=c\).
Coefficient comparison gives
\[
 D c=N,\quad
 D=2g_2+12g_3-g_0,\qquad N=-5g_0+6g_2+24g_3 .
\]
Both \(D=0\) and \(N=0\) would force
\(g/g_3=Y^3-9Y^2+18Y-6\), using \(F=0\).
This cannot occur for a scaled kernel. Indeed write
\(g_3=a,\ g_2=mb,\ g_1=m^2d,\ g_0=m^3v_0\);
then \(m=-9a/b\), with \(a,b\ne0\).
The two exact numerator equations
\(81da-18b^2=0\) and \(-729v_0a^2+6b^3=0\)
have constant gcd after removing powers of \(a,b\).
The supplied replay computes that gcd over the integers in
\(\eta\). If \(D=0\) and \(N\ne0\), the fourth read is already
impossible. Thus every candidate has \(c=N/D\) with \(D\ne0\).

## Exact residual split polynomial

For the fixed reflection moments, use the uniform cubic
representer with its denominators cleared by \(4m^6\):
\[
\begin{split}
 H(Y)={}&4m^6+12m^4(1-m)(Y-m)\\
 &+5m^2(6-6m+2m^2)(3(Y-m)^2-m^2)\\
 &+7(30-30m+12m^2-2m^3)(5(Y-m)^3-3m^2(Y-m)).
\end{split}
\]
This follows by expanding the four shifted Legendre polynomials
against the moments \(1,1,2,6\). The monic cubic for the other
three non-suffix clocks is proportional to
\(H(Y)g(c)-g(Y)H(c)\). In particular, it is a genuine cubic
and has \(c\) as one of its roots.

The following recurrence specifies the split test without storing
a large interpolated polynomial. Put
\[
 \widehat H=\sum_{i=0}^3 H_i N^iD^{3-i},\qquad
 \widehat g=\sum_{i=0}^3 g_i N^iD^{3-i},\qquad
 B_i=H_i\widehat g-g_i\widehat H .
\]
Here \(H_i\) are coefficients, and \(B_3\ne0\) in the chart.
Dividing the cubic by \(Y-c\), the numerator and denominator of
the quadratic discriminant are
\[
 \begin{split}
 Q_1&=B_2D+B_3N,\qquad Q_0=B_1D^2+B_2ND+B_3N^2,\\
 \Delta&=(Q_1^2-4B_3Q_0)/(B_3D)^2 .
 \end{split}
\]
The exact identity checked in [check-reflection.py](check-reflection.py)
is
\[
 Q_1^2-4B_3Q_0=(240m^2D^2)^2\, R(m,\eta),
 \qquad \operatorname{bideg}R=(22,18).
\]
All removed factors are squares of nonzero rational quantities
on the stated chart. Splitting the remaining two distinct clocks
would therefore make \(R\) a rational square.

## Exhaustion of the five-adic charts

Let \(v_5(5)=1\). The exact opener expands as
\[
\begin{split}
 F={}&(-70\eta^3+30\eta^2+30\eta-6)m^3\\
 &+(420\eta^3-90\eta^2-240\eta+30)m^2\\
 &+(-1050\eta^3+90\eta^2+630\eta-30)m\\
 &+1050\eta^3-630\eta.
\end{split}
\]
The replay checks this expansion. Its lowest terms force
exactly the following two necessary coordinate types.

- If \(m\) has negative valuation and \(\eta\) is integral, the
  coefficient of \(m^3\) is a unit and all other coefficients are
  multiples of 5, so that term uniquely minimizes valuation.
  If both valuations are negative, \(-70m^3\eta^3\) is uniquely
  lowest: every other non-\(m^3\) monomial of the displayed
  expression is also a multiple of 5 and has lower degree
  in at least one variable. The sole coefficient prime to 5
  is the term \(-6m^3\), higher by \(3(-v_5(\eta))-1>0\).
  Neither case can give \(F=0\).
- If \(m\) is a unit and \(\eta\) integral, \(F\equiv-6m^3\ne0\).
  For a unit \(m\) and \(v_5(\eta)=-h<0\), the leading
  \(\eta^3\) coefficient is \(-70(m^3-6m^2+15m-15)\).
  Unless \(m\equiv1\bmod5\), it has valuation one, so
  the term has valuation \(1-3h\), below those of all lower
  powers of \(\eta\). Hence the sole unit possibility is
  **B:** \(m\equiv1\bmod5,\ \eta\) nonintegral.
- Let \(v_5(m)=j\ge1\). If \(v_5(\eta)=-h<0\), the
  \(\eta^3\) coefficient has exactly valuation two, while
  the \(\eta^2,\eta,\eta^0\) coefficients have valuations
  at least \(1+j,1,1+j\), respectively. Then \(2-3h\)
  is uniquely lowest. If \(\eta\) is a unit instead,
  the constant-in-\(m\) kernel term \(6A\) has valuation
  one and all other contributions have valuation at least two.
- The remaining case has \(j=v_5(m)\ge1,\ l=v_5(\eta)\ge1\).
  In the centered-kernel form of \(F\), the \(A,B,C,V\)
  contributions have valuations \(1+l,1+j,2+l+2j,3j\);
  the last two are greater than \(1+j\).
  Thus \(l=j\). Dividing the two lowest contributions by
  \(5m\) gives \(-126\eta/m-6\equiv0\bmod5\).
  This is **A:** \(5\mid m,\ k=\eta/m\equiv4\bmod5\).

No assertion that all points in either residue type satisfy the
opener is needed. The following coefficient-level obstruction
holds uniformly throughout each type.

In A put \(m=5v,\eta=mk\). The polynomial
\[
 R_A(v,k)=\left.\frac{R(m,mk)}{5^7m^4}\right|_{m=5v}
\]
has integer coefficients and bidegree \((36,18)\).
Its reduction is \(3k^4+4k^3+2k^2+k+3\), which at \(k=4\)
equals 3 modulo 5. Therefore \(R/m^4\) has valuation 7,
and cannot be a square. In B put \(m=1+5k,\ s=1/\eta=5t\).
The polynomial
\[
 R_B(k,t)=\left.\frac{s^{18}R(1+5k,1/s)}{5^5}\right|_{s=5t}
\]
has integer coefficients, bidegree \((22,18)\), and constant
reduction 2 modulo 5. The homogenizing factor \(s^{18}\) is a
square, yet \(s^{18}R\) has valuation 5. These two odd
valuations contradict all rational splitting possibilities.

The computed residues are full integer coefficient comparisons,
not finite samples of rational coordinates. The native lemmas
also express both contradictions for cleared integer numerators:
the required denominator exponents \((36,18)\) and \((22,18)\)
are even, so clearing any unit denominators at 5 keeps a square.
The graded ingress and the valuation-chart exhaustion are written
mathematical proofs; they are not claimed as a new native
HasOrder wrapper.

## Replay

Run the standalone exact arithmetic check with python-flint 0.8:

    python check-reflection.py

Build the linked Lean module with the repository dependencies and
then run [proof-audit.lean](proof-audit.lean). The module and the typed
audit were checked under stock Lean 4.36.0.
