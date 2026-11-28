# Pure-donor signed triple: a true quartic gate and a mirror exclusion

The generic canonical six-opening signed triple is ruled out by the
[actual order adapter](../erk10-fifteen-signed-triple-cubic-pressure/ACTUAL-ORDER-ADAPTER.md).
Here a last opening donor \(r\) pure through size five is allowed.
We derive one more unavoidable scalar quartic gate on the **actual**
15-row tableau. It closes the entire rational reflection-symmetric mesh in the
stated chart: both when \(A,T\) form one pair and when they belong to
different pairs. The non-symmetric chart remains open.

Keep all hypotheses of the linked chronological chart and literal
adapter, including grouped exactness of the first and second raw
reverse defects, but do not assume the strong five cubic tests.
In particular the high reverse order is \(1,A,A,T,A,D,E,F,G\)
in forward-clock labels, with \(t=3a/2\) in reverse ordinates.
Signs and zero weights are allowed exactly as in the adapter.

## The true quartic gate

Let \(U=X(X-r)\mathcal P_2\). This entire space is realized by
actual rooted combinations of sizes through five whose old six
derivative coordinates are zero. To see this, take the joint
image of actual six opening profiles and their ideal polynomial
models, normalized as in the linked adapter. Polynomial projection
is onto \(\mathcal P_4\) by the bushes. Its kernel has at least
four independent directions in the actual coordinates:

1. The size-three tall minus bush has a nonzero entry at \(e\).
2. The size-four tall minus bush has a nonzero entry at \(s\)
   and vanishes on all three donors.
3. The same-degree size-five differences on the donors give
   \(\boldsymbol Q,\boldsymbol V\), whose \(p,q\) minor is
   nonzero.

Thus the joint image has dimension at least nine and the part
with zero opening profile has dimension at least three. Its
model must vanish at \(0,r\), since those two opening rows are
pure through size five, giving precisely \(U\). This is the
same early-null mechanism as in the
[six-opening singleton analysis](../erk10-six-opening-singleton/README.md),
here applied in seven distinct high scalar sites and a different
chronology.

Every such source has actual high profile \(E f\) for its
\(f\in U\), because those high rows are locally pure through
size five. Apply one actual unary primitive followed by four
same-root leaf marks. This uses only rooted trees through size
ten. The opening remains zero by causal closure, so its high
output is tested against \(L\boldsymbol x^{\odot4}\). By
scalar exactness, integration by parts for
\(\int X^4 Jf=\int (1-X^5)f/5\) is exact through the required
degree nine. Consequently the grouped error tested on \(U\)
is the corresponding combination of the raw first, second,
cubic and quartic reverse defects. The first two have zero
weighted aggregates, and the cubic error kills
\(X(X-r)\mathcal P_3\supset U\) by the linked adapter.
Thus the true quartic defect alone annihilates \(U\).

Set \(H(Y)=Y(Y-a)(Y-t)(Y-d)\), and write
\(J_Y H(Y)=\int_0^Y H(Z)\,dZ\). Taking a linear combination of
the first four raw reverse defects now gives
\[
 \sum_i w_i f(x_i)\big[(L H(\boldsymbol y))_i-J_YH(y_i)\big]=0
 \quad(f\in U).
\]
In reverse chronology, only the last two rows \(F,G\) can
read a value of \(H(\boldsymbol y)\) outside its four zero
labels. Choose the literal blind test
\(f=X(X-r)(X-F)(X-G)\). It kills those two rows, leaving
only the exactly integrated scalar condition
\[
 \int_0^1 X(X-r)(X-F)(X-G)\,
                 J_YH(1-X)\,dX=0.
\]
The integrand has degree nine and vanishes at the old output
origin, so no other quadrature support assumption is needed.
No generic fourth reflected co-order is assumed.

## Exact elimination when the first two sites mirror each other

Suppose the eight scalar sites are reflection-invariant and
\(T=1-A\). Then \(a=2/5,\ t=3/5\). In reverse ordinates the
sites are \(0,1,a,t,d,1-d,e,1-e\), where \(e\) designates
one of the other mirrored ordinates. Put \(v=e(1-e)\).
The degree-nine nodal identity, integrating the entire hull,
gives
\[
        v=\frac{27d^2-27d+4}{3(70d^2-70d+9)} .
\]
The denominator cannot vanish at a solution: \(70\) times
the numerator minus \(27\) times \(70d^2-70d+9\) is 37.
The second nodal test follows by reflection; we use only the first.

Use \(R=1-r\) for the old donor's reverse ordinate.
For \(z=a,t,d\), write \(\mu_z\) for the integral of the reverse
axis hull with the monic factor \(Y-z\) omitted, and put
\(w(z)=z(3z^2-10az+9a^2)\mu_z/12\). The relaxed cubic equation
from the linked adapter says that \((R-z)w(z)\) is affine in
\(z\) on these three nodes. This is true even if the old donor
is coincident with one of these three nodes, since no factor
\(R-z\) is divided out. The first equation on \(R\) is therefore
\[
  (t-a)(R-d)w(d)+(a-d)(R-t)w(t)+(d-t)(R-a)w(a)=0 .
\]
The quartic blind equation in reverse coordinates is linear in
\(R\) as well. Its integrand is
\((Y-1)(Y-R)M(Y)\,J_Y H(Y)\), with the following exhaustive
possibilities for \(M\):

- If the fourth singleton \(E\) is the mirror of \(D\),
  the two blind labels are the whole other pair and
  \(M(Y)=Y^2-Y+v\).
- Otherwise \(E\) has reverse ordinate \(e\) in the other pair
  and the two blind labels are \(1-d,1-e\), giving
  \(M(Y)=(Y-1+d)(Y-1+e)\).
  Both signs of \(e-1/2\) are included.

Eliminate \(R\) by the two-row determinant of the linear
equations, with no pivot division. In the first case the exact
numerator is a nonzero scalar times \((5d-2)(5d-3)\) times
\[
 711210d^5-1803594d^4+1765173d^3
                    -800550d^2+148396d-8325 .
\]
In the second case use the same determinant and the equation
\(3(70d^2-70d+9)e(1-e)-(27d^2-27d+4)=0\).
The exact resultant in \(e\), up to sign, is
\((5d-2)^2(5d-3)^2\) times the degree-twelve polynomial in the
[exact replay](exact-audit.txt). A common root forces the
resultant even if the first equation's linear coefficient in
\(e\) vanishes. The two visible factors are prohibited
collisions with \(a,t\). The remaining quintic has nonzero
leading coefficient and no affine root modulo 7. The remaining
degree-twelve factor has the same property modulo 19.
Thus neither has any rational root, including rationals whose
denominators vanish in the respective residue field.


## Exact elimination when the first two sites belong to different pairs

Now set \(t=3a/2,\ b=1-a,\ c=1-t\) in reverse ordinates.
The four other singleton sites are \(b,c,e,1-e\). Use the last two
test factors as before, assigning \(d\) to the first new singleton
and \(u\) to its immediate singleton successor. Up to exchanging
\(e\) and \(1-e\), the possibilities for \((d,u)\) are exactly
\[
 (b,c),\ (b,e),\ (c,b),\ (c,e),\ (e,b),\ (e,c),\ (e,1-e).
\]
The symmetric pair containing \(e\) is encoded by \(v=e(1-e)\).
The scalar eight-site nodal condition is affine in \(v\), with
\[
 v=\frac{378a^4-630a^3+369a^2-90a+8}
          {6(315a^4-525a^3+301a^2-70a+6)}.
\]
The two coefficients of the original affine equation are coprime
in \(\mathbb Q[a]\), verified in the replay. Thus a zero denominator
cannot make the equation solvable.

For each choice take the same two exact equations affine in \(R\)
from cubic cofactor collinearity and the quartic blind gate.
Evaluate them with this rational expression for \(v\), preserving
the **same denominator scale on both coefficients in each equation**.
Reduce all polynomials in \(e\) by the monic equation
\(e^2-e+v=0\). Then form the two-by-two determinant in \(R\), take its
remainder again, and clear its denominator. The nonconstant
denominators in these steps are powers of the displayed node
denominator only. If the determinant still involves \(e\), take
the resultant with the original quadratic after clearing that
quadratic's denominator; if not, use the determinant directly.
These are necessary tests without any assumption on a nonzero
pivot in \(R\) or in \(e\).

The [seven-choice exact replay](exact-different-audit.txt)
gives every polynomial and factor, with these residual degrees
and rootless residue primes. Multiplicities are shown when needed.

| Pair \((d,u)\) | Nonlinear factor degrees and exclusion primes |
| --- | --- |
| \((b,c)\) | \(12\bmod11\) |
| \((b,e)\) | \(26\bmod13\) |
| \((c,b)\) | \(13\bmod11\) |
| \((c,e)\) | \(26\bmod17\) |
| \((e,b)\) | \(5\bmod11,\ 6\bmod13,\ 26\bmod19\) |
| \((e,c)\) | \(5\bmod11,\ 6\bmod13,\ 26\bmod13\) |
| \((e,1-e)\) | \(4\bmod11\) (twice), \(5\bmod11,\ 6\bmod13,\ 12\bmod29\) |

Every linear factor has root in \(\{0,1/3,2/5,1/2,2/3\}\).
At \(a=0\) there is an endpoint collision; at \(1/3\) one has \(t=1-t\).
At \(2/5\) the first two labels are one mirror pair (already
handled) rather than different pairs; \(1/2\) gives \(a=1-a\)
and \(2/3\) gives \(t=1\). Thus all seven assignments are
excluded over \(\mathbb Q\) without a height cutoff.

## Reproduce and native scope

    python3 -B audit.py
    python3 -B audit-different.py
    # From the repository root: sha256sum -c ai-generated/research/erk10-fifteen-pure-donor-mirror/sources.sha256

The symbolic replay uses exact SymPy polynomial arithmetic; it
reconstructs the nodal moments and all determinants and checks
the full residue sets. The separate Core source
ERK10FifteenPureDonorMirrorMod.lean checks the projective
residue enumerations. The rooted-source adapter, elimination,
and full conditional no-tableau statement are mathematical,
not native HasOrder endpoints.

The residue receipts were checked on Lean 4.34.1, 4.35.0,
4.36.0 and 4.37.0-rc1 with only standard axioms. For the open
asymmetric branch, the [five-pressure construction criterion](ASYMMETRIC-PRESSURES.md)
identifies sufficient and necessary reverse tests in the
balanced signed-triple subchart.
