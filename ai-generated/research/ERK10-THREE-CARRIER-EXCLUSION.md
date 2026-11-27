# Three carriers are impossible in the all-live ERK10 equality chart

Continue the all-live constant-amplitude fork of the
[14-stage equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md)
over an arbitrary characteristic-zero field.
The only surviving carrier counts from the
[two-label exclusion](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md)
were two or three, with at least three distinct noncarrier
active clocks for \(r=As\).
Here we rule out **three carriers** and reduce the two-carrier
nonzero pooled cases. Combined with the independent and
nonconstant exclusions, any all-live 14-stage candidate
has exactly two carriers at physical 2 and 13, in the
literal ledger of the two-label note. The general 14–15
stage interval remains unchanged.

## Pooled rows, interpolation and the endpoint test

Write \(m\in\{2,3\}\) for the number of carriers.
The carrier values of \(r\) are all zero, as shown by
their first three moments and \(r_2=0\).
The physical endpoints are r-inactive.
Let \(n\) be the number of noncarrier r-active physical
rows, \(q\) the number of their distinct clocks,
and \(x_i\) the distinct clocks. At each active clock put
\[
 \nu_i=\sum_{c=x_i} b r,\quad
 \mu_i=\sum_{c=x_i} b r^2,\quad
 \sigma_i=\sum_{c=x_i} b r^3,
\]
with sums here over the active rows only. The paid tests are
\[
 \sum_i \nu_i x_i^j=0\ (0\le j\le6),\quad
 \sum_i \mu_i x_i^j=0\ (0\le j\le3),\quad
 \sum_i\sigma_i=0.
\]
If the pooled \(\nu\) row is nonzero it needs at least
eight active clock sites. Let \(D\) be their monic hull
(in the following high cases, all active clocks are included,
even if a repeated active group has zero pooled mass).
The generic eight- or nine-label cases are particularly sharp:
\[
 q=8:\ \nu_i=\kappa/D'(x_i),\ \kappa\ne0;\qquad
 q=9:\ \nu_i=P(x_i)/D'(x_i),\quad \deg P\le1 .
\]
These formulas are the Vandermonde nullspaces through
degree six. The one- or two-dimensional displayed families
are independent, using Lagrange's leading coefficient identity
\(\sum f(x_i)/D'(x_i)=[X^{q-1}]f(X)\) for
\(\deg f\le q-1\).

We will use this simple endpoint contradiction:
suppose the actual active values satisfy \(r_i=R(c_i)\)
for one polynomial \(R\ne0\) of degree at most three,
and the only other clean ordinary support is at the endpoints.
For \(Q\) of degree at most three, the paid \(br\)-moment
and the carrier cancellation convert the ordinary scalar read of
\(X(1-X)R(X)Q(X)\) into zero. (Both endpoints are killed.)
Thus \(R\) is orthogonal to all polynomials through degree
three for weight \(X(1-X)\), contrary to the paid Beta Gram.
It would also suffice that the weighted scalar and \(br\)
contributions agree on each active group after pooling.

If there is **one additional physical dormant** row besides
the endpoints and carriers, at clock \(\zeta\), the same
argument covers \(\zeta=0,1\). For \(\zeta\ne0,1\), test
\(X(1-X)(X-\zeta) R(X)Q(X)\) instead:
all degrees are still at most nine. It gives the exact
Lobatto relation \(R(X)(X-\zeta)\propto L_4(X)\),
where \(L_4\) is the four-interior-root Jacobi polynomial.
The resulting cubic \(R\) is a nonzero scalar times the
product of the other three fixed roots.
The actual grade-three vector
\[
            T=r-R(c)+R(\theta)s
\]
has model \(-R\) and is supported on just the three
physical clean rows \(0,\zeta,1\).
The unary \(A(CT)\) and \((C-1)T\) have disjoint support,
since \(CT\) starts at the middle dormant row, where a strict
unary read is zero. Their paid grade-nine product yields the
same cubic Lobatto mixed primitive as in the
[two-label scalar gate](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md),
with the sign of \(R\) immaterial. The checked nonzero
cubic Jacobi integral contradicts it.
This last argument requires **one** additional physical
dormant row, not just that several such rows share a clock.

## Eight active labels: one repeated pair cannot help

Assume pooled \(\nu\ne0\) and \(q=8\).
Every pooled \(\nu_i\) is nonzero. The eight means
\(R(x_i)=\mu_i/\nu_i\) have a global interpolant of
degree at most three: if its degree were \(e\ge4\),
the allowed test \(X^{7-e}\mu\) would give \(\kappa\)
times its nonzero leading coefficient.
At a singleton active clock this is its literal \(r\)-value.
If all sites are singletons, the endpoints/dormant-row
argument above applies whenever there is at most one
physical dormant interior candidate.

If exactly one active pair repeats, let their nonzero
weights for the mean be \(a=b_1r_1,b=b_2r_2\), so
\(a+b=\nu_i\ne0\), and note
\[
 \sigma_i-\nu_i R(x_i)^2
       = \frac{a b(r_1-r_2)^2}{\nu_i}.
\]
All singleton groups have zero difference.
But \(\sum\nu_i R(x_i)^2=0\) by degree at most six,
and \(\sum\sigma_i=0\) by the grade-nine pure test.
Thus the sole variance is zero, so \(r_1=r_2=R(x_i)\)
without needing any sign argument. The entire active chart
is again the cubic polynomial on its sites, and the same
endpoint/dormant argument applies.

## Nine singleton labels: the one-pole obstruction

Assume nine distinct active singleton rows, and no extra
active row. Then every \(\nu_i\ne0\).
Write \(\nu_i=P(x_i)/D'(x_i)\) as above.
The interpolant \(Q(x_i)=P(x_i)r_i\) has degree at most
four, by the four \(\mu\)-moments and the degree-eight
leading coefficient test.

If \(P\) is constant, \(r\) equals a polynomial \(R\)
of degree at most four on active rows. If its degree
is four, \(\sum b r^3=\sum\nu_iR(x_i)^2\) is its
nonzero leading square times the nonzero constant \(P\)
(degree exactly eight). Thus \(R\) has degree at most three.

Otherwise \(P(X)=a(X-\xi)\), where \(a\ne0\) and
\(D(\xi)\ne0\) because all \(\nu_i\ne0\).
Polynomial division gives
\[
       \frac{Q(X)^2}{P(X)}=U(X)+\frac{Q(\xi)^2}{P(X)},
                 \qquad \deg U\le7.
\]
The sum of \(U(x_i)/D'(x_i)\) is zero.
The remaining factor is nonzero since
\[
      \sum_i\frac1{P(x_i)D'(x_i)}=-\frac1{aD(\xi)}
\]
by the partial fraction formula for \(1/D\) at \(\xi\).
The paid \(b r^3\) test is the sum of
\(Q(x_i)^2/[P(x_i)D'(x_i)]\); hence \(Q(\xi)^2=0\),
so \(Q/P\) is a polynomial of degree at most three.
This again reduces to the same endpoint/dormant contradiction
if there is at most one additional physical dormant row.

## Three carriers close; exact surviving two-carrier census

If there are three carriers and \(\nu\ne0\), then
\(8\le q\le n\le9\). The cases are \(q=n=8\) (one
dormant), \(q=8,n=9\) (unique active repeat, no dormant),
or \(q=n=9\) (no dormant).
They were all excluded above.
If \(\nu=0\), every active group needs at least two
physical rows, hence \(q\le4\). The four \(\mu\)-moments
make \(\mu=0\) groupwise. Every active two-row group
then has equal \(r\) and opposite weights, no ordinary
scalar mass. With three carriers, the effective scalar
support is at most \(14-3-2q\); ordinary degree-nine
quadrature including the endpoint 1 needs at least
six distinct support labels. Thus \(q\le2\), already
excluded. This proves the three-carrier result.

With two carriers and \(\nu\ne0\), the cases
\(q=8,n=9\) and \(q=n=9\) leave exactly one dormant
row and are excluded above.
Thus the exact surviving cardinality possibilities are
\[
              (q,n)=(8,8),(8,10),(9,10),(10,10).
\]
In the first case the two additional dormant rows
cannot both be at endpoint clocks. The one-dormant
argument does not decide two physical dormant rows
sharing a nonendpoint clock.
In the second case, at least one repeated group must
have unequal \(r\)-values: if all groups were uniform
the same cubic mean holds at all active rows with
no further dormant site, a contradiction.
In the third case its unique repeated pair must also
have unequal \(r\)-values: if uniform with nonzero
pooled mass, it reduces to the nine-label polynomial
argument; if uniform with zero pooled mass, the
entire pair is ordinarily invisible and the remaining
eight singleton labels have the same cubic reduction.
The ten-label case is not touched.

If instead \(\nu=0\) and there are two carriers,
the only possible active label counts are three or
five by the earlier moments and support count.
For three labels the effective support bound is exactly
six. Every active group is a pair or a triple,
and every triple has nonzero ordinary mass and three
distinct \(r\)-values. A sole triple cannot pay its
nonzero cubic charge, and three triples are already
excluded by the preceding cubic Jacobi gate.
Thus only \((2,2,2)\) and \((2,3,3)\) remain.

In the \((2,3,3)\) chart, the four physical true clean
rows (including endpoints) and the two triple labels
are exactly the six ordinary Lobatto support sites.
The invisible uniform pair has clock \(a\), and the
triple labels are \(p,q\).
With \(G_2=(X-p)(X-q)\), the grade-two mask
\(T_2=G_2(c)-G_2(\theta)s\) is supported on the four
true clean rows and the invisible pair.
The pair must straddle both interior true clean rows:
if it had no row before the first nonzero true clean
\(u\), the actual \(A(CT_2)\) would be zero there,
paying the impossible fixed-four Jacobi first contact.
In particular its early member has \(a\ne0\), and the
literal tap from it to \(u\) is nonzero (it is the only
contributing term in the paid nonzero primitive).
Reflection gives \(a\ne1\) and the corresponding late
tap. This is a chronology restriction, not an exclusion.

For five active labels, exactly ten active rows occur
in five pairs. At each label \(x_i\), the two nonzero
amplitudes \(r_{i1},r_{i2}\) differ and the scalar mass
\(\omega_i=b_{i1}+b_{i2}\) is nonzero. Besides the
one-dimensional \(\mu\) nullspace through degree three,
\[
  \mu_i=-\omega_i r_{i1}r_{i2},\qquad
  \sigma_i=\mu_i(r_{i1}+r_{i2}).
\]
Therefore \(\sum \sigma_i=0\) makes the five-site
interpolant of the pair sums have degree at most three.
This gives a low exact input for the open five-label chart.

[ERK10BarycentricCarrierGate.lean](../lean/RKCert/Research/ERK10BarycentricCarrierGate.lean)
checks the scalar variance and two-point moment identities.
The polynomial degree/partial-fraction arguments and
pointwise temporal bridges are mathematical; the
cubic numerical exclusion reuses the prior native closed
integers and field formulas. No new unrestricted stage
floor is claimed.

The [three-pair hyperplane exclusion](ERK10-THREE-PAIR-HYPERPLANE-EXCLUSION.md) closes the pooled-zero case of three clocks with two opposing stages each. The other cases in the census remain separate.
