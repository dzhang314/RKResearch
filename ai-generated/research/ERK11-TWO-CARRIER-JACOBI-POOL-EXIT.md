# The Jacobi doubling obstruction in the two-carrier zero-pool chart

**Scope.** Keep the corrected
[four-pair census](ERK11-TWO-CARRIER-FOUR-PAIR-EXIT.md):
exactly two total carriers, both boundaries genuinely new, pooled
\(b_i r_i\) zero, and at most five distinct noncarrier active clocks.
This does **not** assume either clean fifth response is zero. Over
characteristic zero, only three active triples and one active pair
can remain, both clean fifth responses are active, the two dormant
middle clocks are distinct, and the unique active pair clock must
be absent from the ordinary scalar quadrature support. It must
also be at least one of the two half-plateau clocks. The surviving
clock choices are finite algebraic data. No ordinary stage interval
changes and no full two-carrier exclusion is asserted.

## Exact scalar support and the two-ended doubling gate

The earlier balanced census forces four active clock labels.
Four paired groups have already been excluded. For the remaining
support, the scalar mass of a pair is zero, each triple has live
scalar mass, the dormant clocks are distinct from each other and
from every triple label, and the ordinary clock quadrature has
exactly seven live scalar support sites including 0 and 1.
These are the saturating consequences of the weighted hull argument,
not a positivity hypothesis on individual weights.

Suppose all four active labels belong to that scalar support.
Then the interior five sites consist of these four and one more.
Their monic hull \(H_5\) is orthogonal to degree at most three
for the weight \(X(1-X)\): its product with \(X(1-X)\)
vanishes on all seven sites, and the ordinary scalar order pays
every degree through ten. Therefore, up to scale,
\[
 H_5=R_5+\lambda R_4,\quad
\begin{aligned}
R_4(X)&=42X^4-84X^3+56X^2-14X+1,\\
R_5(X)&=132X^5-330X^4+300X^3-120X^2+20X-1.
\end{aligned}
\]
These two polynomials span the two-dimensional kernel of the
four moments by the weight-\(X(1-X)\) Gram; the companion
checks their moments and their reflection parity. Reflection
gives \(R_4(1-X)=R_4(X),\ R_5(1-X)=-R_5(X)\).

In physical variables the two fronts have active labels
\(a,a/2\) and \(1-b,1-b/2\), where \(a,b\ne0\) are the
left plateau and the reflected right plateau. They are among
the four active labels because the first two clean rows at each
end are calibrated, whether or not the next equal-clock row is
active. Therefore \(R_5+\lambda R_4\) has roots \(a,a/2\),
and \(R_5-\lambda R_4\) has roots \(b,b/2\).
The finite certificate below proves this impossible
without dividing by a Jacobi polynomial at a node.

More generally, the same contradiction applies as long as
both half-plateau labels are in the scalar support and both
plateaus are in it. In the triple cases both plateaus are
indeed in the support: if their fifth row is active, that
label is a triple, and if dormant, it contributes its own live
weight at the pair clock.

## Why only the stated clock cases survive

If all four active groups are triples, their four labels are
all in the ordinary scalar support, impossible by doubling.
If there are three triples and one pair, but one clean fifth
row is dormant, that dormant row is at the unique pair clock.
Its live ordinary mass puts that clock into scalar support,
again impossible. Thus both fifth responses are nonzero:
their two distinct same-clock states make both plateaus triple
labels, and the third triple is the label of the unique active
inner middle row (physical 8, 9 or 10). The other two such
inner rows are dormant. If a dormant shares the pair clock,
it puts the pair clock in the scalar support, also impossible.
The scalar support is therefore exactly the endpoints, three
triple clocks and two distinct dormant middle clocks, with
the pair clock not among them. If both half-plateau labels
were among the three triple clocks, the same doubling
contradiction would apply. At least one half-plateau must be
the omitted pair clock.

If exactly one half-plateau is omitted, the other still gives
one of the degree-eight conditions \(V(\lambda)=0\) or
\(V(-\lambda)=0\) below. For any such parameter there are
only finitely many roots of the interior hull to assign, and
the omitted clock is fixed by the chosen opposite plateau.
If both half-plateaus coincide with the omitted pair clock,
then \(a/2=1-b/2\), so \(a+b=2\) and the plateaus
\(a,a-1\) are both roots of \(R_5+\lambda R_4\).
Eliminating \(\lambda\) between those two roots gives
\[
 2772(a-1)^8-3528(a-1)^6+1212(a-1)^4-104(a-1)^2+1=0.
\]
Each allowable \(a\) fixes \(\lambda\); \(R_4,R_5\) are
coprime by the displayed
[integer identity in the earlier Jacobi packet](ERK11-ARBITRARY-PREFIX-JACOBI-GATES.md#3-the-full-tableau-polynomial-ambiguity-at-every-grade-610).
These are exact finite clock charts, not numerical examples
of full RK methods.

## The degree-eight parameter exclusion

For a nonzero \(x\), a common pair of roots \(x,x/2\)
of \(R_5+\lambda R_4\) gives the second polynomial equation
\(Q(x)=0\), since
\[
 8[R_5(X)R_4(X/2)-R_5(X/2)R_4(X)]=XQ(X),
\]
where
\[
 Q=1386X^8-8316X^7+20496X^6-27090X^5+20973X^4
                  -9720X^3+2632X^2-384X+24.
\]
For \(P=R_5+\lambda R_4\), form the eight-by-eight coefficient
array of \((Q(X)P(Y)-P(X)Q(Y))/(X-Y)\).
At any common root \(x\) this matrix annihilates the nonzero
column \((1,x,\ldots,x^7)\), so its determinant vanishes.
The exact determinant is \(14575336896282624\,V(\lambda)\)
with
\[
\begin{split}
 V={}&17849034\lambda^8+72404556\lambda^7+7089124\lambda^6
       -15432746\lambda^5+78459211\lambda^4\\
    &-114018492\lambda^3+211271046\lambda^2
                 -150701166\lambda+31138569.
\end{split}
\]
Its degree is at most eight because the determinant rows
depend linearly on \(\lambda\). The companion verifies exact
integer determinant values on \(\lambda=0,\ldots,8\), which
suffices by interpolation.

The reductions of \(V(\lambda),V(-\lambda)\) modulo 13 both
retain their degree eight, with leading coefficient 8.
Their ascending coefficient lists are
\[
  [7,8,12,10,12,9,3,3,8],\qquad [7,5,12,3,12,4,3,10,8].
\]
The corresponding ascending coefficient vectors of a Bezout
combination yielding 1 are
\([1,4,3,7,11,4,6,10]\) and \([1,9,3,6,11,9,6,3]\).
Thus the rational polynomials are coprime by Gauss's lemma,
since any nonconstant primitive common factor would retain
its degree modulo 13. They have no simultaneous root in a
characteristic-zero field. The determinant check does not
discard any specialized fiber.

ERK11TwoCarrierJacobiGate.lean checks the polynomial moments,
reflection and doubling identities, exact integer determinant
samples, and degree-preserving Bezout residue arithmetic.
The actual rooted census, interpolation and field transfer
are the mathematical arguments above.
