# A full arithmetic-suffix residue obstruction at five

Use the [seven-distinct-active, two-zero-weight Christoffel clock
atlas](../strict-sdirk7-two-ghost-mass/README.md), with \(W(e)=0\)
at an active site and arithmetic suffix \(v=2u-1\).
This packet proves that **no rational clock core has \(v_5(u)\ge1\)**
(with \(u=0\) included). Equivalently, a rational penultimate
reflected clock that is integral at five cannot reduce to zero.
All first-active clocks and all chronological locations of \(e\)
are included. This is not a global arithmetic exclusion.
A distinct-clock scalar control exists over \(\mathbb Q_5\)
in a different residue class, as checked below.

## No unresolved early fourth-slope exception

The [centered case](../strict-sdirk7-two-ghost-mass/README.md)
is already excluded. In a noncentered rational chart \(g\)
is cubic and irreducible, because the uniform Christoffel
kernel has no finite rational zero.
If the affine fourth polynomial is identically zero, then
\(GL+Eg=0\) as polynomials, and \(g\mid G\) since
\(L\) is a nonzero affine polynomial.
Thus \(g\) is proportional to the cubic \(G\).

Write \(g=(m^3v_0,m^2d,mb,a)\) in increasing coefficient
order, and the cleared \(G=(q_0,q_1,q_2,q_3)\) likewise.
Here \(a\ne0,\ q_3=2(u-3)(u-2)^2\ne0\), and
\(q_2=-6(u-3)(3u^2-9u+7)\ne0\).
Comparison gives \(b\ne0,\ m=q_2a/(q_3b)\), and then
\[
 daq_2^2-b^2q_3q_1=0,\qquad
 v_0a^2q_2^3-b^3q_3^2q_0=0 .
\]
The [exact pivot replay](check-arithmetic-pivot.py) eliminates
the normalized \(e\) after removing only known nonzero powers.
The resulting nonconstant factors in \(u\) have degrees 2 and 27,
projectively rootless modulo 2 and 23. Clearing leading degree
in those primes is checked unconditionally. Consequently a rational
candidate with early \(e\) needs a genuinely nonzero fourth slope.
A zero slope with nonzero constant is already inconsistent.

If \(e\) is fourth, use \(G(e)=0\) instead. When \(u=0\bmod5\),
the homogeneous cubic obtained from \(12T G(e)\) reduces to the
homogenization of \(e^3+e^2+3e+4\); it is rootless on
\(\mathbb P^1(\mathbb F_5)\), including infinity.
The native finite check is
[late_rootless](../../lean/RKCert/Research/SDIRKSevenChristoffelArithmeticAtFive.lean).

## Two exclusive early-site valuation charts

Let \(m=z/2\), \(\eta=(e-m)/m\), as in the
[reflection proof](../strict-sdirk7-mass-reflection/README.md).
In the same scaled kernel coordinates define
\[
 (a_0,a_1,a_2,a_3)=
 ((u-3)(2u^2-10u+11),(u-3)(u-2)(2u-3),
 4(u-2)^2(u-1),6(u-1)^2(2u-3)).
\]
The opener is \(F=\sum a_jg_j=0\).
When \(u=0\bmod5\) these reduce to \((2,2,4,2)\), all units.
Thus the five-adic chart exhaustion in the reflection proof
applies with the following explicit checks:

- If \(v_5(m)<0\) and \(\eta\) is integral, the coefficient
  of \(m^3\) is a unit (its constant-in-\(\eta\) term is
  \(-6a_0\)); other coefficients are multiples of 5.
  If \(m,\eta\) are both nonintegral, the uniquely low term is
  \(-70a_0 m^3\eta^3\). No such \(m\) is possible.
- If \(m\) is a unit and \(\eta\) integral,
  \(F\equiv-6a_0m^3\ne0\). If \(m\) is a unit and
  \(v_5(\eta)=-h<0\), the leading \(\eta^3\) coefficient,
  after division by 5, is congruent to
  \(a_0 m^3+4a_1 m^2\). When \(m\not\equiv1\), it is a unit
  and the valuation \(1-3h\) is uniquely lowest. Hence the
  only unit chart is **B:** \(m\equiv1,\ 1/\eta\equiv0\).
- If \(v_5(m)=j\ge1\) and \(\eta\) is nonintegral, the
  \(\eta^3\) coefficient has valuation two, from \(175a_3\).
  The coefficients of \(\eta^2,\eta,1\) have valuations at
  least \(1+j,1,1+j\), respectively, so that leading term
  again has strictly least valuation. If \(\eta\) is a unit,
  the \(m^0\) kernel term of valuation one is uniquely lowest.
- Otherwise \(j=v_5(m)\ge1,\ l=v_5(\eta)\ge1\).
  Group the kernel terms by their centered degrees \(3,2,1,0\);
  they have valuations \(1+l,1+j,2+l+2j,3j\) because
  the \(a_i\) are units. Equality of the two minima gives
  \(l=j\) and, modulo five,
  \(-21a_3\eta/m-3a_2=0\); hence \(\eta/m\equiv4\).
  This is **A:** \(m\equiv0,\ \eta/m\equiv4\).

The zero \(\eta=0\) was already excluded; the proof therefore
exhausts all finite rational coordinate types. The cube
\(G(e)\) separately handled the fourth placement without using
any of the early-site charts.

## Exact split calculation

For the early chart, the stopped recurrence in
[check-arithmetic-at-five.py](check-arithmetic-at-five.py)
uses \(H\) as the uniform degree-three representer of the
four \(a_i\) above (rather than \(1,1,2,6\)).
The kernel coefficients, \(H\) and \(G\) are formed directly
using the same shifted Legendre formulas as the reflection proof.
The fourth-affine coefficients are cleared exactly.
Their common factor \(2(u-1)(u^2-4u+2)\) is nonzero on the chart.
The remaining \(D,N\) give \(c=N/D\).
Cubic division leaves the exact discriminant numerator
\[
 Q_1^2-4B_3Q_0=(60 m^2D^2)^2 R(u,m,\eta)
\]
of multidegree \((34,22,18)\) for \(R\); the denominator
\((B_3D)^2\) is also a square.
Thus \(R\) must be square for two rational roots.

In A write \(u=5U,\ m=5V,\ \eta=5V(4+5K)\).
The full coefficient identity gives
\(R = 5^7(5V)^4 R_A(U,V,K)\), with
\(R_A\in\mathbb Z[U,V,K]\) of multidegree \((34,36,18)\)
and constant reduction 2. In B write
\(u=5U,\ m=1+5V,\ 1/\eta=5K\).
Then \((5K)^{18}R=5^5R_B(U,V,K)\), with \(R_B\)
integral of multidegree \((34,22,18)\) and constant reduction 3.
All denominators of \(U,V,K\) can be chosen prime to five,
and all homogenizing exponents are even.
Thus the normalized squares would have odd valuations 7 and 5
respectively. The native cleared-integer lemmas verify both
contradictions. The exact Python replay checks every coefficient
of the scalings and also the unscaled discriminant identity.

## The remaining class is not excluded by this local check

For example [check-p5-control.py](check-p5-control.py)
takes \(m=1,\eta=2\) and the unique Hensel root \(u\equiv3\bmod5\)
of the opener in that residue class.
It verifies \(u\equiv564230841913\bmod5^{17}\),
that the residual square class has valuation 4 and unit part
1 modulo 5, that the fourth slope is nonzero, and that
all seven scalar clocks are distinct. This is a split clock
control over \(\mathbb Q_5\), not a rational specialization
or a full tableau. No helper chronology claim is made for it.

## Replay

    python check-arithmetic-pivot.py
    python check-arithmetic-at-five.py
    python check-p5-control.py

These use python-flint 0.8 and SymPy 1.14.
The linked module and [typed audit](proof-audit.lean)
were checked with stock Lean 4.36.0. The valuation-chart
exhaustion, the symbolic recurrence, and the graded ingress
remain written or independently replayed proofs rather
than a native HasOrder wrapper.
