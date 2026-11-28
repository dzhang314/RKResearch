# A rational obstruction for the strong signed-triple order-ten port

This rules out one attempted 15-stage extension of the rational
[order-nine signed triple](../erk9-fourteen-rational-triple/README.md).
It does **not** rule out rational ERK10 with 15 stages, the same stage
chronology under weaker low-annihilator pressure, or other repeated
clock patterns.

## Exact chart and assumptions

The six opening rows contribute scalar output only at their origin.
The nine high rows have forward-clock labels, in **reverse** physical
chronological order,
\[
             1,\quad A,\ A,\ T,\ A,\ D,\ E,\ F,\ G.
\]
The eight scalar sites \(0,1,A,T,D,E,F,G\) are distinct. Write
\(a=1-A,\ t=1-T,\ d=1-D\), and assume the original triple's helper
placement \(t=3a/2\). On the high rows use the strictly lower
triangular reverse block \(L\), weights \(\boldsymbol w\), forward
clock vector \(\boldsymbol x\), and reverse clock vector
\(\boldsymbol y=\boldsymbol 1-\boldsymbol x\). The relevant
requirements are these:

* The scalar quadrature with grouped high weights and the opening
  origin is exact through degree nine.
* At the helper \(T\) and the first subsequent singleton \(D\),
  the raw first and second reflected primitives are exact:
  \((L\boldsymbol y)_i=y_i^2/2\) and
  \((L\boldsymbol y^{\odot2})_i=y_i^3/3\).
  At the three physical rows of \(A\) these two defects have zero
  weighted aggregate. Grouped weights and individual shares are
  allowed to vanish.
* The raw cubic reflected defect
  \(\boldsymbol k=L\boldsymbol y^{\odot3}-\boldsymbol y^{\odot4}/4\)
  obeys the **strong** five terminal tests
  \(\sum_i w_i k_i x_i^j=0\) for \(j=1,\ldots,5\).
  This is an imposed port design, not a consequence of arbitrary
  order-ten rooted equations.

No constraints are imposed on the other three singleton tap
patterns, apart from strict chronology. This arithmetic obstruction
does not need a specific six-opening decoder or a fourth-pressure
test. It allows signed weights, arbitrary rational clocks (including
outside \([0,1]\)), and every placement of \(E,F,G\) in their final
three slots.

## From the actual early taps to four polynomial moments

The endpoint has \(k_i=0\). Through the first singleton \(D\), the
only earlier reverse clock values are \(0,a,t\). On those values
\(y^3=(a+t)y^2-at y\). Hence the cubic defects at each of
\(z=t,d\), and the weight-summed defects at the triple \(z=a\),
come from the exact common formula
\[
 \kappa(z)=(a+t)z^3/3-at z^2/2-z^4/4
          =-z^2(3z^2-10az+9a^2)/12.
\]
In the triple, this means weight times \(\kappa(a)\) after grouping;
individual cubic defects need not equal it.

Let \(H(X)=\prod_{x\ne0,1}(X-x)\) over the six distinct offsites,
and \(S(X)=X(X-1)H(X)\). The five terminal tests on those six
sites have one-dimensional weight-kernel spanned by
\(1/(xH'(x))\). This follows from the leading coefficients in the
six-site Lagrange formula for polynomials of degree at most four,
after absorbing the factor \(x\) in the first test. Scalar exactness
gives the weight at each \(x\) as
\(\int_0^1 S(X)/(X-x)\,dX\,/\,S'(x)\).
Therefore, at the first three offsites,
\(\kappa(1-x)\int S(X)/(X-x)\,dX\,/(x-1)\) must all agree.
This uses no division by the quadrature weights or by the common
proportionality scalar.

In reverse coordinates \(Y=1-X\), let \(U(Y)\) be the monic
split cubic of the three remaining singleton reverse clocks. Let
\(\mu_z\) be the integral of the monic eight-site reverse nodal
polynomial with \(Y-z\) omitted. The preceding relation is
\(\rho(a)\mu_a=\rho(t)\mu_t=\rho(d)\mu_d\) with
\(\rho(z)=z(3z^2-10az+9a^2)/12\). The monic cofactor sign caused
by \(X\mapsto 1-Y\) is common and cancels. Since \(a\ne0\),
the first equality is \(16\mu_a=9\mu_t\).

Write \(R(Y)=Y(Y-1)\). For some nonzero split cubic \(U\) the
following four integrals \(\int_0^1 R(Y)p_i(Y)U(Y)\,dY\) must vanish:
\[
\begin{aligned}
p_0 &= (Y-a)(2Y-3a)(Y-d),\\
p_1 &= Yp_0,\\
p_2 &= (Y-d)(7Y-15a),\\
p_3 &= (5a-6d)Y^2+(15ad-9a^2)Y-9a^2d .
\end{aligned}
\]
The first two are the ordinary degree-nine nodal moments. The third
is \(16\mu_a=9\mu_t\). For the fourth, factor the other cofactor
relation by \(d-a\), getting the integrand multiplier
\[
 q=(2Y-3a)\big(-(3d-a)(d-2a)Y+ad(3d-7a)\big).
\]
Then \(2q-a^2p_2=(2d-3a)p_3\). Both canceled scalars are nonzero
in the rational chart, **before** reducing; their residues need not
be nonzero. Thus collisions after reduction are covered.

## Exact determinant and complete 19-adic split obstruction

Let \(M_{ij}=\int_0^1 R(Y)p_i(Y)Y^j\,dY\) for \(0\le i,j\le3\).
Its determinant is \(-P(a,d)/280052640000\) with
\[
\begin{aligned}
 P(a,d)&=A_0(a)d^2+B_0(a)d+6a^2,\\
 A_0(a)&=-8694a^4+11340a^3-4536a^2+630a-21,\\
 B_0(a)&=17010a^5-20412a^4+7560a^3-966a^2+25a.
\end{aligned}
\]
This and the following cofactor identities are checked by an
independent exact symbolic script.

Let \(v\) be the 19-adic valuation. If \(a,d\) are integral, the
14 possible affine residue pairs from \(P=0\) are exhausted in the
[replay log](exact-audit.txt). In every case three rows of \(M\)
already have rank three and their unique projective nullvector
represents a nonsplit monic cubic modulo 19. This remains valid
when any rational sites collide modulo 19. To see the obstruction
even if some of the three remaining rational clocks have poles,
choose primitive projective pairs for each, and take their product
of primitive linear factors. It reduces to a nonzero split
projective polynomial, of degree at most three, hence cannot lie
on the recorded nullvector line.

If \(a\) is integral and \(d\) has a pole, the quadratic term in
\(P\) has strictly least valuation: \(A_0\) has no root mod 19,
whereas \(B_0(a)\) and \(6a^2\) are integral. This is impossible.

Finally suppose \(v(a)=-n<0\) and put \(h=1/a\). The three term
valuations in \(P\) are exactly \(2v(d)-4n,\ v(d)-5n,\ -2n\):
the relevant leading coefficients are units at 19. Cancellation
can occur only when \(v(d)=3n\) or \(v(d)=-n\). Thus one may write
\(d=\eta h^3\) or \(d=\eta h^{-1}\) with a unit \(\eta\).
Use the alternating four cofactors of the first three rows of \(M\).
Their leading vectors in those two substitutions, in ascending
powers of \(Y\), are exactly
\[
   h^{-3}(5,-35,70,-42)/4939200,\qquad
   h^{-6}\eta^3(-1,9,-21,14)/117600.
\]
Every omitted term has strictly higher \(h\)-power and coefficients
integral at 19. Both displayed scales and the relevant leading
entries are units after factoring off the indicated \(h\)-powers.
Consequently the three rows have rank three in characteristic zero
and the normalized projective cubic must reduce to one of
\[
   42Y^3-70Y^2+35Y-5,\qquad (2Y-1)(7Y^2-7Y+1) .
\]
In characteristic 19 the first has an irreducible quadratic with
discriminant \(10\); the second has one with discriminant \(14\).
Both are nonsquares. This excludes both infinite boundary cases,
without a bounded search for rational points.

The same proof works over a characteristic-zero valued field with
residue exactly \(\mathbb F_{19}\), allowing arbitrary value group
and using primitive projective pairs, or over \(\mathbb Q\) as
stated. No claim is made over coefficient fields whose residue
extensions can split the recorded quadratics.

## Reproduce

The script uses only Python's standard library. It independently
constructs the integrals and determinant, exhausts projective
cubic factor reductions, and verifies both leading cofactor vectors.

    python3 -B audit.py
    # From the repository root: sha256sum -c ai-generated/research/erk10-fifteen-signed-triple-cubic-pressure/sources.sha256

The physical reduction and valuation argument above are
mathematical. The separate Lean Core arithmetic receipt verifies
the finite residue table and its nonsplitting checks, not those
reductions.

The four finite arithmetic endpoints were replayed on Lean 4.34.1,
4.35.0, 4.36.0 and 4.37.0-rc1 with only standard axioms. For the
literal rooted adapter that generically earns the cubic tests, see
[the actual-order adapter](ACTUAL-ORDER-ADAPTER.md).
