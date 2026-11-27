# One outgoing clock forces the single invisible ERK10 ghost to read late

Work over a characteristic-zero field with a fourteen-stage
strict explicit rooted-order-ten tableau with just one zero
output weight and with every quadratic defect invisible.
All stage indices in this note are **physical, one-based**;
the Lean quotient theorem uses arbitrary distinct finite indices,
not a renumbered RK14 tableau.

The [single-ghost ledger](ERK10-SINGLE-INVISIBLE-GHOST.md)
gives the ghost at physical row 2, its indicator \(e=e_2\)
pure of grade two, and \(r=Ae\) pure of grade three.
Here **assume \(r\) is nonzero at only one numerical clock**
\(t=c_3\), with \(r_3=t^2/(2\theta)\ne0,\ \theta=c_2\ne0\).
Let \(j\) be the largest physical index at which \(r\ne0\).
Then **\(j\in\{11,12,13\}\)**, because \(r_{14}=0\).
If \(j=11\), the following conditions are necessary:
* rows 12 and 13 have a common clock \(v=c_{13}\ne1\),
  different from every earlier **live** clock (in particular
  \(v\ne0,t,3t/2\));
* \(b_{12}=-b_{13}\); \(A_{13,12}=0\) and
  \(A_{14,12}/b_{12}=A_{14,13}/b_{13}\);
* stages 12 and 13 agree on all actual \(E_6\) profiles,
  and \(e_{12}/b_{12}-e_{13}/b_{13}\) is an actual pure
  grade-four vector in the span described below.

This eliminates every \(j\le10\) chart and rules out any
other late pattern at \(j=11\). It does not claim to decide
the resulting \(j=11\) pattern or \(j=12,13\).

## 1. Paid flags and forward contact under \(j\le11\)

Let \(I=\{1,3,4,\ldots,14\}\) be the live set and
\(A^\vee=B_I^{-1}(A_{I,I})^\mathsf{T}B_I\) on the original
indices (strict upper triangular). Its true clock is \(Y=1-C\)
by \(bA=b(1-C)\). It is **not** assumed to have full order ten.
Write
\[
 W_i=B_I^{-1}(E_{8-i}^{\perp}|_I),\qquad i=1,2,3
\]
with the original ordinary row annihilator before restriction.
The earlier single-ghost proof gives ranks 1,2,3, all their
rows fully supported on the live set (since \(e\in E_2\)),
and \(W_{i+1}=W_i+Y W_i+A^\vee W_i\) for \(i=1,2\).
Here \(u=A^\vee Y-Y^2/2\) is the actual reduced reverse
quadratic defect and spans \(W_1\), with \(u_{13}\ne0\).
The actual reverse linear primitive deviations through grade
four belong to \(W_3\); the reverse pure rank-two space
through grade three is \(W_2\). Crucially \(W_3\) is not
\(C\)-invariant, by the reviewed linear incoming Hermite
argument in that ledger. We also have \(r|_I\in W_2\).

Suppose \(j\le11\). Then \(r_{12}=r_{13}=0\) and
\(u,r|_I\) are independent, since \(u_{13}\ne0\).
Thus \(W_2=\langle u,r\rangle\); it is \(C\)-invariant
as \(Yu\in W_2\) and \(Cr=tr\).
The original \(F_3\) must have rank two. Indeed, if its
rank were three, its restriction would fill \(W_2\):
restriction kills the one ghost indicator, and the paid
grade-three pairing places the rest in \(W_2\).
Since \(e\in F_3\), this would make the whole original
\(F_3\) clock-invariant. The reviewed outgoing gain
would give \(f_4\ge3+2=5\), impossible because \(f_5=5\)
and the pure ranks rise strictly. So \(F_3=\langle e,r\rangle\)
is instead stable of rank two, and the same outgoing
gain gives \(f_4\ge2+2=4\). Consequently \(f_4=4\),
and the paid restriction \(F_4|_I=W_3\) is exactly
surjective by rank (its kernel is the line \(Ke\)).

The genuine forward cubic defect is thus
\[
 Ac^2-c^3/3=-\theta^3 e/3+
                    (\theta^2-2\theta t/3)\,r.
\]
Its coefficients are obtained at physical rows 2 and 3.
Subtracting the paid quadratic and cubic reads at row 4,
with \(x=c_4\) and no other ghost, gives
\[
 r_4=\frac{x^2(3t-2x)}{2\theta t},\qquad
 A_{43}=\frac{x^2(x-t)}{t^2}.
\]
The clocks \(x=0,t\) make row 4 a literal duplicate
of row 1 or 3, respectively, by these equations and the
clock sum. That is impossible by the independent 14-stage
floor. Since \(r\) is supported only at \(t\), \(r_4=0\).
It follows that \(c_4=3t/2\), distinct from 0 and \(t\).

## 2. The legal reverse duplication and its signed E5 lift

Since \(A^\vee u\in W_2\), its coefficient of \(u\)
is zero: its value at physical 13 is zero by upper
strictness (\(u_{14}=0\)), while \(u_{13}\ne0\) and
\(r_{13}=0\). Thus \(A^\vee u\) is a multiple of \(r\).
At physical 12 this implies
\(A^\vee_{12,13}u_{13}=0\), hence \(A^\vee_{12,13}=0\).
Consequently reverse row 12 reads only the reverse origin
(physical row 14), just as reverse row 13 does, and has
\(u_{12}=-(1-c_{12})^2/2\).

If \(c_{12}\ne1\), then \(u_{12}\ne0\).
On indices where \(r\) is zero the actual \(u\) is supported
at a single clock: write \(Cu=\alpha u+\beta r\)
in \(W_2\); then every nonzero \(u_i\) at an \(r_i=0\)
satisfies \(c_i=\alpha\). Physical 13 is one of them.
Hence \(c_{12}=c_{13}\) in this case, and rows 12 and 13
are literally identical incoming rows of the live reverse.
If \(c_{12}=1\), reverse row 12 is zero and duplicates
physical 14 instead. Let \(k\in\{13,14\}\) be the actual
duplicated comparison row.

All \(W_3\) profiles agree at 12 and \(k\):
the genuine seed \(u\) agrees there, and so do the
operations \(Y,A^\vee\) used to produce \(W_2,W_3\).
Thus the actual numerical vector
\[
                 z=e_{12}/b_{12}-e_k/b_k
\]
belongs to \(E_5\), since its weighted pairing with \(W_3\)
is the difference at these two coordinates and \(V_3\)
has no ghost component. It has the **zero grade-five model**:
the numerical \(bC^a\) reads vanish for \(0\le a\le4\)
at the two equal clocks. Its model \(P\) has \(P(0)=0\)
because its physical origin coordinate is zero. Thus
\(P=XQ\) with \(\deg Q\le4\), and the five paid moments
\(\int X^a P=0\) are the nonsingular anchored \(X\)-Gram
on \(Q\). Hence \(z\in F_5\), not merely a numeral in
\(E_5\).

### If its grade-five line is new

If \(z\notin F_4\), then \(F_5=F_4+Kz\) because
\(f_4=4,f_5=5\). On the literal prefix through row 11,
\(F_4\) and \(F_5\) restrict equally and this restricted
space is invariant under \(C\) and the strict principal
submatrix of \(A\). It contains the restriction of \(d\).
The nominal quadratic equation gives
\(C c=2 A c-2d\) there. Multiplying by the diagonal partial
inverse of \(C\) yields \(c=2 C^\dagger A c-2 C^\dagger d\);
the partial inverse is a polynomial in \(C\) and the
left-diagonally-scaled explicit matrix is nilpotent.
Consequently \(c\) belongs to the restricted pure space.
Clock multiplication and Vandermonde then put each
indicator of a **nonzero** prefix clock in it. Restricting
further to the live prefix cannot give dimension more
than 3, because \(F_4|_I=W_3\). So at most three distinct
nonzero live prefix clocks occur.

The ordinary quadrature is supported on the potential
zero clock, these at most three other prefix live labels,
and the at most two suffix labels \(c_{13},1\), because
row 12 duplicates one of the latter clocks. It needs
at least six distinct sites, even allowing cancellation
at a label; the endpoint-anchored Gram rules out at most
five. Thus all six potential labels are distinct, and
the four internal ones are exactly the roots of the fixed
Lobatto polynomial
\[
                 L(X)=42X^4-84X^3+56X^2-14X+1 .
\]
The supported prefix labels \(t,3t/2\) are among those
four nonendpoint roots. This is impossible: let
\(M(X)=16L(3X/2)=3402X^4-4536X^3+2016X^2-336X+16\).
The exact integer certificate is
\[
 (-12308436X^3+13451508X^2-3902094X+273591)L
 +(151956X^3-267372X^2+136374X-16519)M=9287 .
\]

### If its grade-five line already belongs to \(F_4\)

The case \(k=14\) is impossible, since the last stage is
point exact through grade four and \(z_{14}\ne0\).
Thus \(k=13\), their common clock is \(v=c_{13}\ne1\),
and \(z\in F_4\). The equal \(W_3\) values at 12 and 13
force \(1/b_{12}=-1/b_{13}\), hence \(b_{12}=-b_{13}\).
The vector is a \(C\)-eigenvector of \(W_3\); if it were
outside the already invariant \(W_2\), it would make
all of \(W_3\) invariant, impossible. Thus \(z|_I\in W_2\).
Since \(W_2\) is the weighted annihilator of \(E_6\), the
two actual forward stages agree on \(E_6\). The literal
reverse duplicate gives both
\(A_{13,12}=0\) and \(A_{14,12}/b_{12}=A_{14,13}/b_{13}\).
In particular \(A(e_{12}+e_{13})=0\) and
\(b(e_{12}+e_{13})=0\).

## 3. The unseen repeated clock and the exclusion of \(j\le10\)

Suppose there is an earlier live stage \(a\) at clock \(v\).
Properties in §2 imply it agrees with the pair on \(E_2\):
the quadratic defect is zero at all live stages, and
the forward \(E_2\) is the span of clock polynomials
through degree two plus \(e_2\).
There is an actual strict **thirteen-stage quotient**:
drop row 12 and replace the numerical coordinate at
row 13 by
\[
                        f_a+f_{13}-f_{12}.
\]
The kernel is \(K(e_{12}+e_{13})\); it is annihilated by
both \(A\) and \(b\), so the linear stage operator and
output descend. For explicit strictness one may lift a
kept vector by assigning physical coordinate 12 value
zero and coordinate 13 its new value minus coordinate \(a\).
Both the quotient and the lift are causal as \(a<12<13\);
their composition around the strict \(A\) is strict.
The transformed unit is still identically one on the
kept 13 coordinates.

The quotient is multiplicative on every pair of actual
expressions with total grade at most nine. If both inputs
have grade at most six, each has equal values on the late
pair, so the new coordinate of their product is simply
\(f_ag_a\), equal to the product of the new coordinates.
Otherwise at most one factor has grade greater than six
and the other has grade at most two. That other factor
has equal values at the two late rows **and** the anchor
\(a\), making the same product rule true. The unary
and multiplication recursion therefore transports every
rooted test through grade nine into the 13-stage quotient,
contradicting the independent lower floor. Thus no earlier
live clock can equal \(v\).

Finally still assume \(j\le11\) in the only surviving
opposing-pair case. The two independent vectors \(r,z\)
span \(W_2\); \(A^\vee u\in W_2\) and \(Y W_2\subset W_2\),
so
\[
                         W_3=\langle r,z,A^\vee r\rangle .
\]
If \(j\le10\) this space is zero at physical 11. In the
actual live reverse row 11 the only preceding clocks are
zero at row 14 and \(w=1-v\ne0\) at rows 12 and 13.
Let \(a\) be the sum of the two reads at \(w\) and
\(y=1-c_{11}\) the row clock. The genuine linear
quadratic, cubic and quartic primitives through grade four
then give \(aw=y^2/2,\ aw^2=y^3/3,\ aw^3=y^4/4\).
For \(y\ne0\) they imply \(y=3w/2=4w/3\), impossible.
So \(c_{11}=1\). Both rows 11 and 14 annihilate \(W_3\);
the same preceding E5-model argument now gives
\(e_{11}/b_{11}-e_{14}/b_{14}\in F_5\setminus F_4\).
The new-line proof gives at most three nonzero live
prefix labels through physical 10. The only other
scalar support sites are then 0 and 1: the 12/13
ordinary contribution vanishes by opposition. At most
five scalar support clocks contradict exactness.
Thus \(j=11\) whenever \(j\le11\) is possible.

[ERK10SingleGhostLatePairGate.lean](../lean/RKCert/ReviewedNative/ERK10SingleGhostLatePairGate.lean)
checks the rational Lobatto exit and an exact rooted-word
signed-pair quotient, including the causal coordinate
formulas. The paper rank, physical matching, and moment
bridges above reuse the earlier invisible-ghost ledger.
No reverse ordinary order, ordered field, or unrestricted
15-stage claim is used.

The [fifth-row calculation](ERK10-SINGLE-INVISIBLE-GHOST-FIFTH-ROW-EXCLUSION.md)
subsequently excludes the remaining tap-at-11 pattern by forcing a
literal duplicate physical stage. The one-clock case still allows taps
ending at 12 or 13 in the current analysis.
