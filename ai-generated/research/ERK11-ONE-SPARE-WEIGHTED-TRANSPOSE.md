# Weighted transpose of the all-live maximal ERK11 chart

Continue the
[all-early-live maximal rank-two chart](ERK11-ALL-LIVE-ENDPOINT-REDUCTION.md)
and its [actual adjoint identities](ERK11-ADJOINT-PURE-DUALITY.md).
Thus \(A\) is 17-row strict explicit and ordinarily exact
through order eleven, \(bA=bY\), every \(b_i\ne0\), and all
the measured exact rank and stage premises in those notes
hold. This argument concerns the actual weighted transpose
of this chart only, not the transpose of arbitrary RK methods.

**Theorem.** Let \(B=\operatorname{diag}(b)\), and reverse
stage order in \(A^\star=B^{-1}A^\mathsf{T}B\) and \(b\).
This defines a strictly explicit method of order at least
ten. It has order at least eleven **if and only if**
original physical row 17 is individually exact through
rooted grade five. When that condition holds, the two
methods have precisely the same actual elementary and
pure spaces through grade five in original coordinate order.
In the half-clock branch with both late quadratic carriers
13 and 16 present this endpoint condition already holds.
Assuming characteristic zero, the two physical prefixes
(earliest eleven and latest eleven) are then both dense
through grade five, with exactly four quadratic carriers
in the whole tableau. These new restrictions do not
yet give a 17-stage exclusion.

## Graded orthogonal flag and primitive transfer

Work before the final permutation and write
\(\langle x,z\rangle=x^\mathsf{T}B z\).
The matrix \(A^\star\) is strictly upper triangular, so
after stage reversal it is strictly explicit. Its clock
is \(A^\star\mathbf1=Y\mathbf1=1-c\), by \(bA=bY\).
Use \(Y\) also for its physical diagonal multiplication.
The reverse origin is original row 17.

Define
\[
                 H_j=E_{10-j}^{\perp_B}
                              \cap\{z:z_{17}=0\}
                    \qquad(0\le j\le10).
\]
These are nested. The earlier exact fits give \(H_j=F_j\)
for \(j=0,1,2,3,4\). Indeed \(E_9,E_{10}\) are full,
\(\operatorname{Ann}_B(E_8)=F_2\),
\(\operatorname{Ann}_B(E_7)=F_3\), and
\(\operatorname{Ann}_B(E_6)=F_4\).
Those low pure spaces vanish in row 17 by its paid
grade-four point exactness.

For \(x\in H_j\) and \(z\in E_{9-j}\), the two rows
\(\langle A^\star x,z\rangle=\langle x,Az\rangle=0\)
and \(\langle Yx,z\rangle=\langle x,Yz\rangle=0\)
prove the unary and reflected-clock advances, using
\(AE_k,YE_k\subset E_{k+1}\).
They retain the last-coordinate-zero condition because
\(A^\star\) is strictly upper triangular and \(Y_{17}=0\).
For any \(f\in F_i\) in an **original** pure flag and
\(x\in H_j\) with \(i+j\le10\),
\(\langle f\odot x,z\rangle=\langle x,f\odot z\rangle=0\)
for \(z\in E_{10-i-j}\), since the original product
\(f\odot z\) belongs to \(E_{10-j}\).
Thus \(f\odot x\in H_{i+j}\).
Any pair of grades with sum at most nine has at least
one grade \(\le4\), so this handles every product of
reverse pure factors through grade nine.
The same is true through grade ten except for the
pair \((5,5)\).

For every \(0\le k<10\),
\[
                 A^\star Y^k\mathbf1-
                    \frac{Y^{k+1}\mathbf1}{k+1}
                            \ \in H_{k+1}.                \tag{1}
\]
Here its evaluation at 17 vanishes by strictness and
\(Y_{17}=0\). Pair against any actual pair \((z,P)\)
of original grade \(9-k\). The left primitive terms have
the same exact integral because
\[
  \int_0^1 (1-X)^k(JP)(X)\,dX
       =\frac1{k+1}\int_0^1(1-X)^{k+1}P(X)\,dX .
\]
Indeed the original rooted tests of degree ten pay
\(Y^k\odot(Az)\) and \(Y^{k+1}\odot z\).
The polynomial identity follows from the moment of
each monomial \(P=X^i\):
both sides equal \(i!k!/(i+k+2)!\).
Thus (1) is true for actual vectors, requiring no
extrapolation to a larger RK order.
Also \(bY^j\mathbf1=1/(j+1)\) by scalar reflection.

Now induct on the ordinary rooted pair operations for
the reversed tableau (using the reflected model variable).
A pure deviation stays in \(H_j\); scalar polynomial
parts use (1) for unary operations; products of a pure
part and a polynomial clock part use that the diagonal
clock advances \(H\); and products of two pure parts
use the preceding mixed product rule.
Each \(H_j\) is killed by \(b\), since \(\mathbf1\in
E_{10-j}\).
Consequently reverse rooted order **ten** always holds,
and all reverse pure differences through grade five
are in \(H_5\).

## The single missing product is exactly the endpoint condition

The full \(E_5\) has dimension eleven, and \(e_{17}\notin
E_5\) by injectivity from the first eleven. Hence
\(\dim E_5^{\perp_B}=6\) and the row-17 zero condition
cuts it to a five-dimensional \(H_5\): a failure to cut
would put \(e_{17}\) in the double orthogonal \(E_5\).
The original \(F_5\) is the radical of the restricted
form on \(E_5\), since the original mixed product of
grade five with grade five gives the nonsingular
ordinary polynomial Gram through degree five on the
model quotient. It follows that the radical of
\(E_5^{\perp_B}\) is also \(F_5\). Thus after quotienting
by the original \(F_5\) the six-dimensional orthogonal
complement has one nondegenerate symmetric line.

If original row 17 is exact through grade five, then
\(F_5\subset H_5\), hence equality by dimension.
The missing product \((5,5)\) is then a product of two
actual original pure vectors and the same induction
proves reverse order eleven.

Conversely the reverse order-ten method already has
\(\dim\bar F_5\ge5\) by the [paid grade-five surplus](../lower-bounds/paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md),
applied to the reversed tableau with ordinary order \(r=10\)
and weight exponent \(m=0\). Model separation holds at its even midpoint.
Since \(\bar F_5\subset H_5\), it equals \(H_5\).
If reverse order eleven holds, this five-dimensional
space is totally isotropic by the exact product of
grade-five pairs. A one-dimensional nondegenerate
symmetric space over a field has no nonzero isotropic
vector, so \(H_5\subset F_5\), and equality follows.
Thus row 17 vanishes on all original pure grade-five
differences, which is precisely its point exactness
through that grade.
If the endpoint condition fails, the same argument
identifies a genuine obstruction on the \((5,5)\)
root product: some \(h\in H_5=\bar F_5\) has nonzero
\(\langle h,h\rangle\). Its nominal pure product is
zero but its ordinary reverse read is nonzero.
The obstructing product cannot first appear below
grade ten because the reversal is already order ten.

When the endpoint condition holds, \(\bar F_5=F_5\),
and their degree-five ordinary polynomial summands
span the same numerical columns (the clocks \(c\) and
\(1-c\) generate the same polynomial span).
Thus the actual reverse \(E_5\) equals the original
\(E_5\) as well. For grades two through four, the initial
strict-growth argument in the [same paid proof](../lower-bounds/paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md#the-two-polynomial-calculations-behind-the-count)
gives \(\dim \bar F_j\ge j-1=\dim F_j\). The containment
\(\bar F_j\subset H_j=F_j\) is therefore equality, and adjoining
the common clock-polynomial spans gives \(\bar E_j=E_j\).
The grades zero and one consist only of clock polynomials.
This does not identify higher-grade flags.

## Four quadratic carriers in the half-clock two-carrier branch

Assume also characteristic zero, \(p=1/2\), and
the late carriers at both 13 and 16 are present.
The [half-clock calculation](ERK11-ALL-LIVE-ENDPOINT-REDUCTION.md)
already proves endpoint grade-five exactness and the
actual space
\[
             F_5=\langle \delta,\delta\odot f,
                                  f,Zf,Z^2 f\rangle ,
                  \qquad f=A\delta .
\]
All quadratic carriers have one physical clock and
one nonzero value of \(\delta\); also
\(f_{13}\ne f_{16}\).
The exact polynomial model or any pure direction
above has a profile on the carrier support
which is affine in \(f_i\). Therefore at most **two**
carrier coordinates can be independently read in
any literally dense 11-coordinate copy of \(E_5\).

By the order-eleven reversal theorem and the
[rank-free cutoff](ERK11-RANK-FREE-FIRST-ELEVEN-CUTOFF.md)
applied in both directions, both the original first eleven
and the original last eleven (the reversed first eleven)
have full numerical image of the same \(E_5\).
The last eleven contain the carriers 13 and 16, so
there is no carrier on rows 7–11. The first eleven
have one or two carriers, all in the first six.
Thus globally there are either three or four carriers.

There must in fact be four.
The three paid products
\[
                   b(\delta\odot f^{\odot j})=0,
                                \qquad j=0,1,2
\]
(cost respectively 2,5,8) force the first three scalar
moments of the carrier \(f\)-values to vanish.
If there were only three carriers, grouping equal
values and applying the three-site scalar Vandermonde
would give pooled \(b\)-mass zero at each group.
All \(b_i\ne0\), so each group needs two carriers;
but there are already at least two distinct \(f\)-values
from 13 and 16. This contradicts three carriers.
With four carriers the same argument excludes exactly
three distinct \(f\)-values and gives: either two
distinct values each with two opposing weights, or four
distinct values.

The two early carriers are the first nonzero clock
stage and one of rows 5,6.
For exact literal indexing, row 1 is the origin and
a zero-clock row before the first nonzero stage would
duplicate its entire data, so full first-eleven \(E_5\)
forces that first carrier at row 2.
Normalize its clock to 1 by dilation; its quadratic
defect equals \(-1/2\) and this is the common carrier
value. A third row with that clock and defect would
have \(A c=0\), so \(A_{32}=0\), and would literally
duplicate row 2. A third row with zero clock would
likewise have \(A_{32}=A_{31}=0\), duplicating the
origin. Hence row 3 is a noncarrier with clock \(N\ne0\).
At a proposed carrier row 4, with \(a=A_{42}, B=A_{43}\),
the first two moments give
\(a+NB=0\) and \(3(a+N^2B)=(3-2N)a\).
For the second equation use the actual pure grade-three
span \(\delta,-2A\delta\), evaluating
\(Ac^2-c^3/3\) on the first carrier and the noncarrier
at \(N\): the coefficients are \(2/3,\ 1-2N/3\),
and \((-2A\delta)_4=a\).
Those equations give \(Na=0,\ NB=0\), so this
would again be a duplicate. Only rows 5 or 6 remain.

The characteristic-zero premise here is used to earn
the literal reversed first-eleven dense cutoff.
The reversal theorem and its conditional paid-field
kernel transfer require no ordering and only \(11!\ne0\)
after their initial premises. ERK11ReversalGate.lean
checks unary and mixed product closure for an abstract
dual flag, the scalar midpoint line, the early fourth
carrier test, and the finite paid primitive integrals.
Identification of the actual rooted flags and the
ordinary cutoff are the mathematical part of this proof.
