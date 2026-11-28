# Four equal-response pairs are impossible in the two-carrier ERK11 chart

**Scope.** Continue the characteristic-zero
[sole-late-carrier two-front reduction](ERK11-SOLE-LATE-CARRIER-TWO-FRONT.md)
with exactly two physical carriers (2,16), all weights live,
and both seventh boundary clocks genuinely new. Let \(r=As\)
be the actual grade-three pure response to the carrier indicator.
Assume the pooled ordinary charges \(b_i r_i\) vanish at every
distinct active noncarrier clock, where active means \(r_i\ne0\).
If there are at most five distinct active clocks, then there
are exactly four, with either **three active triples and one
active pair**, or **four active triples**. The all-four-pairs
subchart is impossible. A dormant clean fifth row on one
front forces its plateau to be an active pair, and at most
one of the two fifth rows can be dormant in a surviving
case. Neither fifth response is assumed zero. The argument
is characteristic zero after its conditional premises; it changes
no ordinary stage bound.

## 1. Exact pooled census

Write \(q\) for the number of active noncarrier clock labels and
\(n\) for the number of active sites. The two front calibrations
supply four distinct active noncarriers on each front (rows
3,4,6,7 and 11,12,14,15). Thus \(q\ge4,n\ge8\).
Of the 15 noncarriers, the endpoints 1,17 are dormant, so
initially \(n\le13\). No dormancy at physical 5 or 13 is assumed.

Every active label has multiplicity at least two, since all
\(b_i,r_i\) there are nonzero and its first response pool vanishes.
The five paid moments of \(r^2\), grades \(6+k\le10,\ 0\le k\le4\),
force the second response pool zero at each label when \(q\le5\).
At an active pair these two local equalities with nonzero
amplitudes force identical responses and opposite weights:
the pair contributes zero ordinary scalar mass.

The carriers likewise contribute zero pooled mass at their
common clock by \(b(s)=0\). Thus possible nonzero ordinary scalar
mass is supported on the \(15-n\) dormant sites and on the active
labels with multiplicity at least three. There are at most
\(n-2q\) latter labels. This potential set includes 0 and 1.
Its number of distinct labels must be at least seven: a set of
at most six containing 0,1 has a degree-six hull
\(X(1-X)U_4(X)\), padding with arbitrary factors as necessary.
Its products with all degree-four clock polynomials are paid,
contradicting the nonsingular weight-\(X(1-X)\) Gram and
\(U_4\ne0\).

Consequently \(7\le15-2q\), so \(q=4\) and this count
is exactly saturated. Each group is a pair or triple, the
dormant clocks are all distinct, and no dormant clock is
shared with a triple clock. All triple groups have nonzero
ordinary scalar mass. A triple has three distinct response
values (otherwise Vandermonde on one, two and their nonzero
scales would force a singleton weight or pooled scalar mass zero).
On such a triple with responses \(r_1,r_2,r_3\), its third-response
pool equals \(r_1r_2r_3\) times its ordinary pool by the cubic
hull and the zero first/second-response pools, hence is nonzero.
Pairs' third-response pools vanish. The true zero total and
first-clock moments of \(r^3\) (grades nine and ten) exclude
one or two triple groups.

Thus the only options are four pairs (\(n=8\)),
three triples and one pair (\(n=11\)), or four triples
(\(n=12\)). The two clean fifth rows are physical 5 and
13. If one of them is dormant, its clock is shared with
an active fourth row and hence that active group must be
a pair (no dormant clock can coincide with a triple).
If a clean fifth row is active, its response is distinct
from its fourth-row partner. Those two live unequal
responses cannot form a complete pair, so the group
must be a triple. In the \(n=11\) case both fifth rows
cannot be dormant: there is only one pair, and the
dormant labels must be distinct. In the \(n=12\) case
both must be active. In the \(n=8\) case both are dormant
by the already accounted eight active sites.

## 2. Both-ended profiles in the four-pair subchart

Now let \(n=8\). Each active group consists of exactly one
of the four named left active sites and one of the four
named right active sites, with equal ordinary response \(r\).
There are no other active sites. In particular both clean
plateau clocks \(a=2c_3=c_4=c_5\) and \(d=c_{13}=c_{14}\)
occur at dormant sites 5 and 13, respectively; they are distinct.
Write \(b=1-d\), with \(b\) a clock scalar, not the output row.

The common grade-four spaces in the two fronts are polynomial
clock representatives and pure \(\langle s,r,Cr\rangle\).
Thus matched active sites have identical readings on all
actual grade-four vectors. The left quartic \(V_L\) is zero
through physical 7, and the right quartic \(V_R\) is zero
from physical 11 onward, by the new-boundary gate. Hence both
quartics vanish at **all eight** active sites.

Use the ordinary response scales \(F=\theta r,\ G=(1-\theta)A^\star s\);
so \(G=\lambda' F\), \(\lambda'\ne0\).
In physical variable \(X\) the two quartic model terms are
\(X^2(X-a)^2\) and \((1-X)^2(X-d)^2\). Their exact actual
noncarrier corrections in (2) of the two-front note rescale
to \(a(C-a)F\) and \(-b(C-d)G\). Thus at every active label
\(x\ne a\) the left zero gives \(F(x)=x^2(a-x)/a\); at
every active \(x\ne d\) the right zero gives
\(G(x)=(1-x)^2(x-d)/b\).
The actual front values at the two plateaus and half-plateaus
are
\[
             F(a)=-a^2/2,\quad F(a/2)=a^2/8,\qquad
         G(d)=-b^2/2,\quad G(1-b/2)=b^2/8.
\]
These are literal row calibrations, unaffected by the
weights or by whether either plateau lies in \([0,1]\).
Each active label occurs on each front, hence avoids both
endpoint clocks 0,1. In particular \(a,b,d,1-a\ne0\).

Write \(w=a+b-1=a-d\ne0\). Comparing the two plateau reads gives
\[
   \lambda'=-\frac{2(1-a)^2w}{a^2b}
             =-\frac{ab^2}{2(1-b)^2w},\qquad
   Q(a,b)=(ab)^3-4(1-a)^2(1-b)^2w^2=0.                  \tag{1}
\]
If neither half-plateau is the other plateau, the half-plateau
reads impose
\[
\begin{aligned}
 L(a,b)&=2(1-a)^2w+(2-a)^2(a+2b-2)=0,\\
 L(b,a)&=2(1-b)^2w+(2-b)^2(2a+b-2)=0.                   \tag{2}
\end{aligned}
\]
The first follows by substituting the first \(\lambda'\) from
(1) into \(G(a/2)=\lambda'a^2/8\); the second is its reflection.

If both half-plateaus collide with the other plateaus, the
two ratios would be \(-4b^2/a^2\) and \(-b^2/(4a^2)\),
incompatible in characteristic zero. If only the left half
collides, then \(b=1-a/2\). Equation (1) reduces after removing
the live \(a^3\) to \((3a-4)(a^2-2a+2)=0\). The available
reflected half equation gives \(5a^3+10a^2+4a-8=0\).
Their exact integer Bezout combination is the nonzero 18928
(as checked in the companion), contradiction. The reflected
single-collision case is identical with \(a,b\) interchanged.

## 3. Noncolliding arithmetic has no characteristic-zero solution

The difference in (2) factors
\[
 L(a,b)-L(b,a)=(a-b)\big(3(a+b)^2+ab-12(a+b)+8\big).
\]
If \(a=b\), use \(L(a,a)=7a^3-24a^2+28a-10\) and
\(Q(a,a)=a^6-4(1-a)^4(2a-1)^2\). Their explicit integer
Bezout combination is 22448, nonzero.

Otherwise write \(S=a+b,P=ab\).
The difference gives \(P=-3S^2+12S-8\).
The sum in (2) is \(3S^3-5SP-12S^2+28S-20\);
substitute to obtain \(9S^3-36S^2+34S-10=0\).
Equation (1) becomes
\[
 (-3S^2+12S-8)^3-
          4(1-S-3S^2+12S-8)^2(S-1)^2=0 .
\]
The exact integer Bezout combination of these two scalar
polynomials is 347816, nonzero. Both subcases fail, so the
four-pair chart is impossible.

ERK11TwoCarrierPairGate.lean checks the symmetric differences,
collided substitutions and the three polynomial Bezout identities
over characteristic-zero fields. The actual grade/census and
profile bridge is the mathematical argument above. The three- and four-triple
cases, six active labels with pooled br zero, nonzero pools and
repeated boundaries are not asserted excluded.
