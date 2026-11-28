# Low active cubic support and a grouped reverse debit for normalized DIRK11/13

This note concerns **only** the hypotheses of the [normalized DIRK11/13
signed census](dirk-order11-thirteen-signed-cubic-census.md): actual rooted
order eleven over the reals, thirteen literal lower triangular stages,
forward `C(2)`, two genuine reflected identities `D(1),D(2)`, and the stated
grade-six surplus. No assertion is made here for arbitrary unnormalized
tableaux. The numerical real interval is still **13–14**.

Let \(g=Ac^2-c^3/3\), \(r\) count the distinct numerical labels with an
active dirty row (\(b_i g_i\ne0\)), \(d\) count all distinct physical
numerical dirty labels (\(g_i\ne0\)), and \(z\) count the physical dirty
zero-weight rows. Write \(k\) for the number of physical active dirty rows.
The new conclusions are:

* **All \(d=4\) cases with \(r=0\) or \(r=1\) are impossible.**
* An \(r=1,d\ge4\) candidate must have \((d,z,k)=(5,4,2)\): a single
  equal-defect opposite-weight active pair, four ghost dirties at distinct
  labels outside the active pair's label, and seven clean physical rows
  at distinct numerical labels, including 0 and 1.
* If \(r=0,d\ge4\), only \((d,z)=(5,5),(6,6)\) survive. In the first,
  eight clean physical rows lie on seven labels, with a unique clean
  duplicate pair at a nonzero reflected clock. The genuine reflected
  cubic is a nonzero multiple of that contrast. In the second there are
  seven distinct clean rows and six distinct ghost dirty rows.

The previously excluded \(d=2,3\), and the still separate case \(d=1\),
are not inferred from the new grouped cut.

## 1. The ordinary ledger and the exceptional four actives

All genuine forward defects are paid at their actual grades. In particular,
\(\sum b_i g_i^a=0\) for \(a=1,2,3\), by graded products of the cubic
zero-profile seed (degrees 3, 6, 9). If at most three nonzero \(g\) values
occur on a one-label active dirty fiber, a square Vandermonde after
factoring the nonzero value out of each column kills its ordinary weight
sum separately at each value. Therefore two or three active dirty rows on
one clock must all have the same defect: with two or more value classes
one has a lone nonzero weight. Their aggregate weight is zero.

Any set of possible support labels for the ordinary degree-ten rule,
augmented by the actual 0 and 1, has at least seven elements. Otherwise
\(X(1-X)\) times the square of the product over its non-endpoint sites has
strictly positive real integral, degree at most ten, and all weighted
readings zero. This counts **possible** labels; it does not assert nonzero
weights at the physical origin or every individual row. At exactly seven
possible labels each of the five non-endpoint labels has nonzero aggregate
weight by the same test omitting that one factor. A site may be outside
\([0,1]\); no positivity of tableau weights is used.

If \(r=1,d\ge4\), then \(z\ge3\), since \(d\le1+z\). If \(k\ge5\)
there are at most five physical clean rows (including the actual
endpoints), hence at most six possible labels, contradiction. For \(k=4\)
we must have \(z=3,d=4\), six distinct clean labels, and the active dirty
label different from all of them with nonzero ordinary aggregate weight.
The four active defects must be distinct, or the first three defect
moments would zero their aggregate as above.

The rank census gives \(\dim F_6=5\). Since there are four physical dirty
labels, \(g\mathcal P_3(c)\) has dimension four; because the dirty fiber
has distinct live defect values, \(g^2\) is outside that space. Thus
\(F_6=g\mathcal P_3(c)+K g^2\) vanishes at every clean row. The known
terminal cardinal \(e_T\in E_6\) has profile
\(H_T(X)=30b_T X\Phi_4(X)\) with
\(\Phi_4=42X^4-84X^3+56X^2-14X+1\). Therefore the four nonendpoint
clean sites are exactly the four roots of \(\Phi_4\). Testing the ordinary
rule against \(X(1-X)\Phi_4(X)\) gives zero integral, zero at all six clean
sites and a nonzero paid read at the only dirty aggregate. The integral
identity is the usual quartic orthogonality, or direct integration of the
six coefficients. This contradiction excludes \(k=4\).

For the remaining \(r=0,1\) cases the entire ordinary measure is on the
clean labels, so it has at least seven possible labels including the
endpoints. Physical clean rows may be unweighted or share a numerical
clock with a dirty class.

## 2. Sixth and seventh rank at the physical colour classes

Retain \(d\ge4\). The true grade-six space is
\[
 E_6=\mathcal P_5(c)+g\mathcal P_3(c)+K e_T.
\]
Indeed every summand is genuine. A relation first vanishes on at least six
nonterminal distinct clean clocks, which kills the degree-five polynomial;
then the actual terminal kills its cardinal coefficient, and the \(d\ge4\)
distinct dirty clocks kill the degree-three multiplier. This gives all
11 dimensions. Taking the actual column \(c^6\) in this decomposition
forces every nonterminal clean label to be a root of a monic degree-six
polynomial. There are thus exactly six such labels, and the clean
terminal clock 1 occurs only at the true terminal: a further clean row at
1 would put all seven distinct clean labels in the same sextic. In
particular the clean output aggregate at 1 is the nonzero terminal
weight. The aggregate at 0 is not assumed nonzero.

The true column \(g^2\in E_6\) vanishes at every clean row. Its
polynomial-plus-cardinal components are zero by the same degree-five
argument. Thus \(g_i=U(c_i)\) for every physical dirty row with
\(\deg U\le3\), by division by the nonzero \(g_i\) only at such a row.
Consequently members of any one colour-clock class (clean or dirty)
have equal evaluations on all of \(E_6\), even when a different colour
class has the same numerical clock. There are exactly \(7+d\) classes,
one of which is the singleton terminal. The space \(L\) of all covectors
with zero sum on **each** physical class has dimension \(6-d\) and is a
subspace of \(E_6^\perp\).

For \(d=4\), equality of dimension gives \(L=E_6^\perp\). For \(d=5\)
we can replace \(g\mathcal P_3\) by \(g\mathcal P_4\) above. The resulting
12-dimensional subspace is all of \(E_7\), by the true rank and the
five-node Vandermonde. Thus all of \(E_7\) is class-constant and
\(L=E_7^\perp\). In the latter case the one actual repeated class is a
physical pair, and the genuine reflected cubic detects that contrast.
For invisible \(r=0,z=6,d=5\), the repeated class would be a dirty ghost
pair, so the reflected cubic would be zero at every active stage. This
is impossible by its nonzero pivot at the latest active nonunit clock
from the signed census. For \(r=0,z=d=5\) the repeat is instead clean, at
that nonzero reflected pivot. In the remaining visible \(r=1,d=5\) chart,
counting gives exactly \(z=4,k=2\). For \(r=0\) the bound \(z\le6\) follows
from the seven physical clean labels; for \(r=1\), \(z\le4\) follows from
the same count and \(k\ge2\). This proves the stated surviving inventories
once \(d=4\) is removed.

## 3. Two full class sums give an impossible reverse debit at \(d=4\)

Use the actual transpose \(N=A^\mathsf{T}\) in reverse chronology and
\(y=1-c\). Define \(W(P)=b P(y)\),
\(U_0=E_6^\perp=L\) and
\(Z=E_5^\perp\cap\{v:v_T=0\}\). The ranks and the true terminal
cardinal give \(\dim U_0=2,\dim Z=3\), \(U_0\subset Z\), and
\(NU_0\subset Z\). The last inclusion uses the unary grade increase on
\(E_5\) and the actual zero terminal column of \(A\). For \(\deg P\le4\),
\(NW(P)-W(IP)\) is a genuine paid row in \(Z\), with
\(IP(x)=\int_0^x P(t)\,dt\). Its terminal is zero both by the true column
identity and \(IP(0)=0\).

In **each** clean class move its weight to its last chronological member
in reverse, carrying the whole ordinary aggregate, and call the resulting
vector \(b'\); put \(b'=0\) on every dirty class. The dirty class aggregate
of \(b\) is already zero (all ghosts, or the one signed active fiber).
It follows that \(M(P)=(b-b')P(y)\) has zero sum on every class, since
\(y\) is constant within a class. Thus \(M(P)\in U_0\) for every
polynomial, **not** just for low degrees. This is a bookkeeping
subtraction from a paid row, not a change of tableau or of its order.

Choose the first two nonzero reflected clocks \(u,v\) of the reverse
representatives carrying nonzero ordinary mass. Enough exist by the
five distinct live non-endpoint labels. They are distinct and their
class sums \(m_u,m_v\) are nonzero. Set
\(P=Y(Y-u)(Y-v)Q\) for \(\deg Q\le1\). The corrected numerical input
\(W(P)-M(P)=b'P(y)\) vanishes through the second representative
inclusively. In particular **every member of each sampled class** is
within that inclusion, by choosing the last member as representative.
Repeated classes not yet represented, zero-mass classes, and dirty
classes contribute zero to this support check.

Hence
\[
 D_Q=N(W(P)-M(P))-W(IP)\in Z
\]
has class sums \(-m_u IP(u),-m_v IP(v)\) at the two samples. Both
class sums kill every element of \(U_0=L\). If \(D_Q\in U_0\), the
primitive \(IP\) has roots at \(0,u,v\); its derivative \(P\) already
has those three roots, so it must be zero (degree at most five). Thus
the two-dimensional space of \(Q\)'s injects into the one-dimensional
quotient \(Z/U_0\), contradiction. Equivalently the scalar determinant
is \(u^3v^3(u-v)^3/120\), nonzero under the displayed pivot guards.
This proves the exclusion for every \(d=4\) counted skeleton, without
any ordering assumption on repeated physical slots.

## Native scope

[`DIRKOrderElevenThirteenGroupedReverse.lean`](../../lean/RKCert/ReviewedNative/DIRKOrderElevenThirteenGroupedReverse.lean)
checks the grouped, inclusive weighted reverse contradiction from
actual `HasOrder 11`, literal lower triangulation, explicit normalized
hypotheses and a `GroupedReverseCut` containing the actual weight mask,
class time inequalities and annihilator class-sum conditions. The real
ordinary-support ledger and the derivation of the mask from that ledger
are the mathematical arguments above. The native adapter is over
any characteristic-zero field; it requires no weight sign or any
order of a transposed tableau. The existing signed census and the
normalization/surplus inputs retain their own stated scope.
