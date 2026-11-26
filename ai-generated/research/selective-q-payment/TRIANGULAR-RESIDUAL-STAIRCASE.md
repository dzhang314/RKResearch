# A triangular stage budget for actual residual ranks

Let \(A\) be lower triangular over a field \(K\), with \(s\) stages,
\(\mathbf c\coloneqq A\mathbf{1}\), and weights \(\mathbf b\).
Assume the literal rooted-tree equations through order \(p\ge3\).
The bushes make all integers \(1,\ldots,p\) units in \(K\).
There is no sign, skipped-edge, layer-width, distinct-clock, or
terminal-output premise.

For a rooted tree \(t\), put
\[
 \mathbf N_t\coloneqq
 \operatorname{forestFactorial}(t)\boldsymbol{\Phi}_t(A).
\]
For \(j\ge0\), let \(Z_j\) be the actual span of
\(\mathbf N_t-\mathbf N_u\) with \(|t|=|u|\le j+1\).
Let \(F\coloneqq\{i:b_i\ne0\}\), and set
\[
 R_j\coloneqq\dim Z_j,\qquad r_j\coloneqq\dim(Z_j|_F).
\]
Thus \(R_j\) counts all stage directions and \(r_j\) counts only
the directions witnessed on live coordinates. No rank is counted
from formal distinctness of the trees.

**Tradeoff.** For \(2q+1\le p\), put \(a=p-1-q\). Then
\[
 \boxed{\quad s\ \ge\ R_a+q+1+r_q.\quad}
\tag{1}
\]
If all diagonal entries equal \(\gamma\), then
\[
 \boxed{\quad s\ \ge\ p-1+r_q.\quad}
\tag{2}
\]
More quantitatively, for every \(2\le d\le a\), the common-diagonal
case gives
\[
 \boxed{\quad
 s\ \ge\ p-1+\bigl(R_d-(d-1)\bigr)+r_q.
 \quad}
\tag{3}
\]
For strict ERK, add one to the right sides of (1)–(3)
if \(2q+2\le p\), or if the first stage has weight zero.
These are lower bounds, not asserted to be sharp.

## 1. The dimension payment

Write \(C\) for multiplication by \(\mathbf c\), and
\(P_q\coloneqq\operatorname{span}\{\mathbf{1},\mathbf c,\ldots,
\mathbf c^{\odot q}\}\). The normalized tree span through
order \(q+1\) is exactly \(P_q+Z_q\): subtract the bush of
the same order, and note that all these bushes supply
the powers of \(\mathbf c\).

The reviewed root join gives
\(\mathbf N_{t\mathbin{\#}v}=\mathbf N_t\odot\mathbf N_v\)
and \(|t\mathbin{\#}v|=|t|+|v|-1\).
Thus multiplying a same-order difference in \(Z_a\) by a
normalized tree column through order \(q+1\) stays in
\(Z_{a+q}\). Each such difference has scalar readout zero:
the order-\(m\) equation gives
\(m(\mathbf b\cdot\mathbf N_t)=1\) with the same unit \(m\)
for the two trees. In particular
\[
 \sum_{i\in F}b_i z_i v_i=0
 \qquad
 (z\in Z_a,\ v\in P_q+Z_q,\ a+q+1\le p).
\tag{4}
\]

The two summands \(P_q|_F,Z_q|_F\) are disjoint and
\(\dim(P_q|_F)=q+1\). Indeed, if \(P(\mathbf c)|_F\in Z_q|_F\)
for a polynomial of degree at most \(q\), test it against
the clock powers of exponents \(0,\ldots,q\). By (4) the
result is zero. The bush moments give the ordinary
Hilbert matrix \(1/(i+j+1)\) with \(0\le i,j\le q\) in this
test. It is invertible in the actual field: clear the
denominators as a polynomial in the row index. A column
relation would give a polynomial of degree at most \(q\)
with \(q+1\) distinct roots. Evaluating the zero polynomial
at the \(q+1\) negative poles then detects each coefficient;
all differences and denominators are paid units.
This also proves injectivity of \(P\mapsto P(\mathbf c)|_F\)
by taking the zero element of \(Z_q|_F\).

The form \(\sum_{i\in F} b_i x_i y_i\) on \(K^F\) is
nondegenerate. Orthogonality (4) gives
\[
 |F|\ \ge\ r_a+(q+1)+r_q.
\tag{5}
\]
The restriction \(Z_a\to K^F\) has kernel of dimension
\(R_a-r_a\), supported only on the zero-weight stage
coordinates. Thus \(s-|F|\ge R_a-r_a\). Adding this
zero-weight bound to (5) proves (1). In particular no
direction is counted both as a dark coordinate and as a
live direction of the same \(Z_a\). Also \(a\ge q\), so
\(|F|\ge q+1+2r_q\) follows separately.

## 2. Two primitive seeds prevent triangular plateaus

In the notation
\[
 \mathbf E_2\coloneqq2A\mathbf c-\mathbf c^{\odot2},
 \qquad
 \mathbf E_3\coloneqq3A\mathbf c^{\odot2}-\mathbf c^{\odot3},
\]
the seeds lie in \(Z_2\) and \(Z_3\) respectively. They are
the normalized single-branch differences from the same-order
bush, for bush children of orders two and three. Multiplication
by \(C\) sends \(Z_j\) into \(Z_{j+1}\) by adjoining one leaf.
The actual \(A\) does likewise whenever \(j+1\le p\):
for a tree of order \(m\),
\(\mathbf N_{[t]}=m A\mathbf N_t\), and \(m\) is a unit.

Here is the triangular step in a form that also handles
noncommon diagonals. If a subspace \(U\subseteq K^s\) is stable
under \(A,C\) and contains both seeds, then
\(\mathbf c\in U\). To prove this, start with the zero vector
in \(U\). Maintain \(u\in U\) agreeing with \(\mathbf c\)
in the rows already processed and vanishing on every
zero-clock coordinate. At the next row \(i\), both vectors
\[
 C\bigl(\mathbf E_2-(2A-C)u\bigr)
    =C(2A-C)(\mathbf c-u),\qquad
 C\bigl(\mathbf E_3-(3A-C)Cu\bigr)
    =C(3A-C)C(\mathbf c-u)
\tag{6}
\]
belong to \(U\), vanish on processed rows by triangularity,
and vanish on all zero-clock coordinates. If \(c_i=0\),
the row already agrees. Otherwise their coefficients on
the error \(c_i-u_i\), writing \(\gamma_i=a_{ii}\), are
\[
 c_i(2\gamma_i-c_i),\qquad
 c_i^2(3\gamma_i-c_i).
\]
They cannot both vanish: equality
\(c_i=2\gamma_i=3\gamma_i\) would give \(\gamma_i=c_i=0\).
Correct the row by a scalar multiple of the corresponding
vector in (6). No division is used at a zero clock.
All rows can thus be corrected. For a common diagonal
one can equally write everything with
\(B=A-\gamma I\), since stability under \(B,C\) implies
stability under \(A,C\).

For \(2\le j\le p-2\), a plateau \(Z_j=Z_{j+1}\)
would be such a stable subspace: it contains both seeds,
including \(\mathbf E_3\) when \(j=2\).
But \(\mathbf b\cdot Z_j=0\), whereas the order-two bush
gives \(\mathbf b\cdot\mathbf c=1/2\). This proves strict
growth at every such step, so
\[
 R_a\ge R_d+(a-d)\qquad(2\le d\le a\le p-1).
\tag{7}
\]
For a nonzero common diagonal, the first stage has \(c_1=\gamma\)
and \((E_2)_1=\gamma^2\ne0\). For strict ERK, take the first
nonzero clock, which exists by the order-two bush. Its
predecessors have zero clocks, so \((E_2)_i=-c_i^2\ne0\).
Thus in either common-diagonal case \(R_2\ge1\) and
\(R_a\ge a-1\) for \(a\ge2\). If \(a=1\), the latter is just
\(R_a\ge0\). Insert this and (7) in (1) to prove (2)–(3).
For arbitrary DIRK with a possibly changing diagonal (1)
and (7) still hold; they give \(s\ge p-2+r_q\) without
a nonzero quadratic seed, and (2)–(3) if it is nonzero.

## 3. The extra strict origin dimension

For strict ERK every \(Z_j\) vanishes at the first stage,
whose clock is zero. If its weight is zero, the kernel
used to prove (1) misses that extra dark coordinate.
If its weight is nonzero, the unit vector at that stage
in \(K^F\) is orthogonal to \(Z_a|_F\).
It is not in \(P_q|_F+Z_q|_F\) when \(2q+2\le p\):
otherwise writing it as \(P(\mathbf c)|_F+z|_F\) and testing
against clock powers \(1,\ldots,q+1\) makes
\(P=0\) by the same Hilbert argument with the denominators
shifted by one. This leaves the unit vector in \(Z_q|_F\),
contrary to the vanishing at the first stage.
In either of the stipulated cases there is one more
dimension in (1). No extra probe at the odd exact
midpoint is claimed if the first stage is live.

## 4. Consequences for normalized packets and near-minimum room

The root-product expansion identifies \(Z_q\) with the span
of paid-cost residual products times clock powers before any
output argument. In particular, for a nonempty product
\(E_M=\bigodot_{u\in M}\mathbf Q(u)\) of cost
\(d(M)=\sum_{u\in M}|u|\le q\), the homogenized column
\(\mathbf c^{\odot(q-d(M))}\odot E_M\) lies in \(Z_q\).
On \(F^\times=\{i:b_i c_i\ne0\}\), multiplying all those
columns by the same invertible row diagonal \(c_i^{-q}\)
recovers the projected residual products
\(\prod_{u\in M}Q(u)_i/c_i^{|u|}\).
Thus the dimension of any such projected family, also
after restriction to representatives of effective
profiles, is at most \(r_q\). Independent ratios are not
assumed, and there is no division at \(c_i=0\).

For example, a donor-ratio packet alphabet of size \(N\le q\)
whose actual mass matrix on the effective projection has
rank \(h\) earns at least \(h-1\) such residual directions
by the finite packet test. The common-diagonal floor is then
\(s\ge p+h-2\). Independently, (5) gives a live-coordinate
floor; these inequalities are not added a second time.

Equivalently, if a common-diagonal table has
\(s=p-1+\delta\), then for every \(2\le d\le a\)
\[
 r_q+\bigl(R_d-(d-1)\bigr)\le\delta .
\]
Thus the actual excess in the forward defect staircase and
the observed packet rank share a single quantified budget.
If the baseline is attained, every affordable \(Z_q\) has
zero live projection, even though the full-stage staircase
is strictly growing. More precisely, (1) and (5) are equalities:
\(R_a=a-1\), \(Z_a|_F=(P_q|_F)^\perp\) in the live pairing,
and \(Z_a\) contains the entire coordinate subspace on
zero-weight stages. These are necessary statements, not
assertions that the baseline is attainable. In particular,
if \(\gamma\ne0\), \(p\ge5\), and the first weight is nonzero,
the first entry \((\mathbf E_2)_1=\gamma^2\) already
certifies \(r_2\ge1\) and forces \(s\ge p\).
At the other extreme, if every stage weight is nonzero and
\(q\ge2\), then \(r_q=R_q\ge q-1\), giving
\(s\ge p+q-2\) for common diagonal, with the proved ERK
origin refinement when applicable.

The proof uses full order through \(p\) for the same-order
differences and scalar Gram plateaux. It makes no claim that
a single fixed-order family pays the same staircase. The
projected packet bound can be used without any finite ratio
alphabet, and the field hypothesis may be applied separately
in residue fields, using the actual ranks that survive there.

## A single triangular operator and the odd-midpoint origin

The two seeds can also be combined in one operator.
Put

    H = C(6(CA-AC)-C^2),
    W = {v : v_i=0 whenever c_i=0}.

Then H c = 3C^2 E_2 - 2C E_3. H is triangular, its rows at
zero clocks are zero, and its diagonal equals -c_i^3:
the diagonal commutator vanishes identically. Its
restriction to W is a triangular bijection (keep precisely
the nonzero-clock rows and columns). If U is stable under
A,C and contains the two seeds, H carries U∩W into U∩W and
is injective there, hence surjective there by finite
dimension. Since Hc lies in U∩W, uniqueness of its W
preimage gives c∈U. This works in any field, even where
the scalar 6 happens to vanish, and avoids any choice of
a global generic pivot parameter. In the strict case
C(2A-C) alone has nonzero diagonal on W and uses E_2
alone, though two seeds are convenient for general DIRK.


An origin test using only 2q+1<=p.
If such a representation of e_1 exists, the first
coordinate gives P(0)=1. With P(X)=sum_j x_j X^j,
x_0=1, tests against c^i for i=0,...,q then give

    sum_j x_j/(i+j+1) = b_1 * 1_{i=0}.

Use the same cleared numerator F(X) of degree <=q.
It vanishes at X=1,...,q, and F(-1)=q! because x_0=1.
Consequently F(X)=[(-1)^q/(q+1)] product_(i=1,...,q)(X-i),
including the constant case q=0. At X=0 this gives
F(0)=q!/(q+1), while the i=0 equation gives
F(0)=b_1(q+1)!. Cancellation yields

    b_1 = 1/(q+1)^2.

All factorials and differences are in the exact paid
range; this is not a real-positivity proof. Thus over
any paid field the extra origin credit holds whenever
b_1 differs from this exceptional value (zero weight
uses the separate dark argument). At the odd midpoint
p=2q+1, b_1<=0 over an ordered field is a sufficient
special case. A nonzero exceptional value is only
necessary for the origin vector to lie in the old
span; it is not sufficient, and no method attaining
that exception is proved. Sign has no analogous use
for a nonzero common diagonal, since the first row
and c_1 do not vanish there.
