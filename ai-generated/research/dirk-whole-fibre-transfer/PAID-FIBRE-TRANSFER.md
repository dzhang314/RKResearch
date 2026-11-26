# Paid support ranks, actual fibre equality, and stage counts

The inclusion hypothesis concerns the actual physical support. See [the support clarification](ERRATUM.md) for the optional argument deriving it from stability.

These are conditional, order-parametric bounds for the reviewed algebraic
order conditions. They use the genuine stage coordinates and do not assume that
an artificial quotient is a Runge–Kutta method. The reasoning applies over a
field with the small integer units paid by the achieved order. It transfers to
a nonzero commutative unital ring if the specified fibre/support evidence holds
after reduction to a residue field; ranks and fibre labels need not survive
an arbitrary reduction.

## A real forward gain from actual whole-fibre inclusion

Let \(F_j,E_j\) denote the native defect and numerical tree spans and put
\(f_j\coloneqq\dim F_j\). Let \(S\) cover the physical support of \(F_H\).
Write \(L(S)\) for the subspace of stage vectors supported on \(S\), zero
at zero clocks, and constant on the part of each nonzero clock fibre in
\(S\). Let \(\nu\coloneqq\dim L(S)\), the number of distinct nonzero clocks
represented in \(S\).

Use \(m\coloneqq H-k\). Given \(H\le p\), let \(r,d\) satisfy
\[
  1\le r\le m-1,\qquad 2(k+r-1)+1\le p,\qquad
  d+1\le k,\qquad d<r(m+1-r).
\]
The simultaneous marking theorem gives
\[
  d+1+\dim(F_k\cap L(S))\le\nu,\qquad
  d+1+f_k\le |S|.
\]
If the actual inclusion \(L(S)\subseteq F_H\) is known, both \(L(S)\)
and \(F_k\) lie in \(F_H\). The dimension of their sum gives
\[
                         f_H\ge f_k+d+1.
\]
It is not necessary for \(F_k\) itself to be constant on fibres. The
intersection accounts for the actual overlap. Two useful ways to certify
the extra inclusion are:

- Prove that the columns of \(F_H\) are actually constant on each
  indicated fibre, zero at zero clocks and off \(S\), then prove
  \(\dim F_H\ge\nu\). Since \(F_H\subseteq L(S)\), this gives equality
  of the subspaces, not just equality of their dimensions.
- Prove that \(F_H\) is stable under clock multiplication and under
  coordinatewise products. The actual support indicator belongs to
  \(F_H\), and the clock projections split it into each nonzero fibre
  indicator. These indicators span \(L(S)\). Stability under clock
  multiplication alone does not suffice.

### Numerical consequence at the ordinary midpoint

Let \(q=\lfloor p/2\rfloor\) and assume \(L(S)\subseteq F_q\).
For the paid ERK count the existing forward rank \(f_5\ge5\), its
strict increases, and the ordinary two-ended budget give
\(s\ge\lceil3p/2\rceil-2+f_q-(q-1)\). For DIRK the existing paid
grade-six inequality is \(f_6\ge f_3+4\). Its two-ended count gives
\(s\ge3q-4+e\) at order \(2q\) and \(s\ge3q-2+e\) at order \(2q+1\)
whenever \(f_q\ge f_3+(q-3)+e\).

- At orders 16 and 17 take \((k,H,r,d)=(5,8,2,3)\).
  This gives \(f_8\ge f_5+4\ge9\) for ERK. The conditional paid
  lower bounds are **24 and 26** instead of the unconditional
  arbitrary-ring counts 23 and 25. For DIRK the same interval may
  spend the already-known grade-six surplus and gives no added
  uniform rank from the ordinary inputs.
- At orders 18 and 19 take \((6,9,2,3)\), giving \(f_9\ge f_6+4\).
  The resulting ERK counts 27 and 29 and DIRK counts 25 and 27
  already match the strongest paid published endpoints. The
  criterion simplifies a proof if its inclusion is independently
  verified, but does not raise the endpoints.
- At order 20 take \((6,10,2,5)\), giving \(f_{10}\ge f_6+6\).
  ERK therefore needs **31** stages on this architecture, compared
  with paid 30 and ordered 32. DIRK needs **29**, compared with
  paid 28 and characteristic-zero/ordered 29.
- For orders at most 15, the same ordinary seed inputs and
  midpoint windows do not produce an improvement on the published
  counts. For strict SDIRK at any of these orders, invertible
  Volterra already implies \(f_H\ge\dim E_{H-2}\) without any
  fibre assumption. Choosing the largest allowed backward window
  in the support theorem does not improve that existing rank step.

These comparisons use only the published generic rank inputs and
public numerical table, not any held higher-order chart.

## An independent numerical family from late exact receivers

A row \(i\) with nonzero clock \(c_i\) that is zero on all \(F_H\)
exports a genuine order-\(H\) prefix method. The denominator-cleared
stage residual for every rooted tree of order at most \(H\) is zero
at row \(i\). Rescale the leading tableau and the literal output row
of \(A\) by \(c_i^{-1}\). Homogeneity of the reviewed tree weights
then gives the reviewed \(\mathrm{HasOrder}\ H\) on that prefix.
For ERK, or for an actual marked row with zero diagonal, the
prefix ends strictly *before* \(i\). Otherwise it includes \(i\).
Lower triangularity is preserved; a common nonzero diagonal
stays common and nonzero under this scaling. The native provider is
the point-probe specialization of the inclusive/exclusive affine
receiver theorem, not a new proof of tree scaling.

In particular \(r\) distinct nonzero Volterra marks in an order-\(p\)
tableau with carrier grade \(k\) and endpoint \(H\) require
\[
                       s\ge L_{\mathcal C}(H)+r,
\]
where \(L_{\mathcal C}(H)\) is any proved lower bound for that
coefficient setting and method class. This statement needs actual
marks, not a proposed interpretation of a rank profile. Conversely,
if the available stage cap leaves fewer than \(r\) slots after an
order-\(H\) prefix, it excludes a matched carrier even in a degree
not ruled out by the scalar multiplicity comparison, provided all
\(r\) nonzero/paid mark steps are valid up to that point.

For the following quantitative specialization, assume \(H+1\le p\),
and let \(S\) be a union of whole physical clock fibres covering
\(F_H\). Assume the aggregate output weight at every nonzero clock
in \(S\) is zero. This last assumption follows if \(L(S)\subseteq F_H\):
each full nonzero fibre indicator is pure and \(b\) kills \(F_H\).
Other paid evidence of zero aggregate mass is equally sufficient.

The ordinary shifted quadrature Gram forces at least
\(N\coloneqq\lfloor p/2\rfloor\) distinct contributing nonzero clocks.
For example, if \(W\) is the monic product of the \(a<N\) supposed
contributing nonzero factors, the quadrature gives
\(I(X W R)=0\) for every \(\deg R\le a\); the square shifted Cauchy
test costs only \(2a+2\le p\) and forces \(W=0\).
All \(N\) sites must be off \(S\), and there must be \(N\) different
actual rows at or after the first omitted nonzero receiver.
The order-\(H\) export at that first row therefore gives
\[
 s\ge L_{\mathcal C}(H)+N-\delta,\qquad
 \delta=\begin{cases}
 0 & \text{if the first omitted nonzero row has zero diagonal},\\
 1 & \text{otherwise}.
 \end{cases}
\]
ERK always uses \(\delta=0\), and general DIRK and strict SDIRK
can use \(\delta=1\) without an explicitness premise. This count
does not require the marking argument or a rank-saturated
midpoint: it pays a different actual endpoint certificate. It
also combines with the supported-row count as
\(s\ge\max(f_k+d+1+N,\ L_{\mathcal C}(H)+N-\delta)\) when both
sets of hypotheses hold; the \(N\) omitted rows are disjoint
from \(S\).

For \(H=p-1\), using the published paid class floors \(L(p-1)\),
this gives the following conditional architecture floors:

| p | ERK | ordinary DIRK | strict SDIRK |
|--:|--:|--:|--:|
| 11 | 19 | 15 | 19 |
| 12 | 22 | 18 | 23 |
| 13 | 24 | 20 | 26 |
| 14 | 26 | 23 | 31 |
| 15 | 28 | 25 | 34 |
| 16 | 30 | 27 | 39 |
| 17 | 31 | 28 | 43 |
| 18 | 34 | 31 | 49 |
| 19 | 36 | 33 | 53 |
| 20 | 39 | 36 | 59 |

All entries are conditional; they do not establish a new unrestricted
stage lower bound. For comparison the unconditional order-20 paid
floors are 30 / 28 / 55. In particular this exact saturation
architecture cannot be imposed on arbitrary near-minimal tableaux.

## A general omitted-coordinate nullity bound

Let \(T\) be the complement of the actual support cover \(S\).
Write \(z(T)\) for the number of zero diagonals on \(T\).
Suppose \(k+L+2\le H\le p\) and the ordinary polynomial/defect
separation holds through \(q=k+L\), for example \(2q+1\le p\)
(or \(2q\le p\) with the native zero-row anchor). Let
\(U=E_k\cap\{v:v|_S=0\}\). Then
\[
             \dim U\le\max(0,z(T)-L),\qquad
             |S|\ge\dim E_k-\max(0,z(T)-L).
\]

Indeed \(U,C U,\ldots,C^L U\) are genuine supported vectors of
\(E_q\). Their Volterra images lie in \(F_H\), so restriction to
\(T\) sends their sum injectively into the kernel of the actual
principal submatrix \(D_{TT}\), \(D=CA-AC-A^2\).
That triangular submatrix has nullity at most \(z(T)\), by taking
the principal minor on its nonzero diagonals. The paid polynomial
model is injective on any part of \(E_q\) supported on \(T\):
its kernel is \(F_q\), whose vectors are supported on \(S\).
In the polynomial model \(C\) is multiplication by \(X\); for a
nonzero polynomial subspace the span grows at each such shift, as
a vector of maximal degree acquires a larger degree. If \(U\ne0\),
the actual shifted span consequently has dimension at least
\(\dim U+L\).

There is also an exact fibre version. Let \(\tau\) be the number
of clock labels on \(T\) detected by at least one vector of \(U\);
pure stage equality makes each vector in \(U\) constant on each
such fibre. If \(L\ge\tau-1\), interpolation of each particular
detecting vector yields the literal indicator of its fibre on \(T\)
among the shifted columns. Each such fibre's earliest row in \(T\)
must have zero diagonal by the same triangular pivot. No single
vector with all its fibre values nonzero is needed, including over
a finite field. If there are at most \(L\) total distinct labels on
\(T\), their monic vanishing polynomial would kill any \(U\) vector,
contradicting the injective paid model; hence \(U=0\) in that case.

## Why ordinary size and fibre dimensions alone do not force a gain

Exact equality of the numbers \(\dim F_H\) and \(\nu\) does not
imply actual fibre membership. An honest order-two ERK tableau
with \(A_{21}=1,\ A_{31}=1/3,\ A_{32}=2/3\) and
\(b=(1/2,1/2,0)\) makes the point. Its clocks are \((0,1,1)\);
\(F_2\) is spanned by the quadratic residual \((0,-1/2,1/6)\).
Its rank and its occupied nonzero fibre count are both one, and
it is clock invariant. Yet it does not contain the actual full
clock-one indicator \((0,1,1)\). The aggregate output weight at
that fibre is \(1/2\ne0\). Neither the whole-fibre nor the mass
certificate may be inferred from this rank equality.

Likewise a codimension-one whole-fibre subspace can kill all its
paid scalar observables while the aggregate-mass vector is nonzero
at every site: for the one available moment at \(H=p-1\), use the
hyperplane orthogonal to a full-support mass vector. This describes
a linear rank obstruction, not an RK tableau. With more paid
moments the same example uses the intersection of the corresponding
weighted Vandermonde row kernels. Counting independent relations
does not count individually zero masses.

Finally, even when every stage clock is distinct, a support cover
containing every row except the mandatory explicit origin need
not be small enough for a new absolute result. Ordinary separation
already gives \(s\ge f_k+k+1\). The supported count, with only this
one guaranteed omitted row, is \(s\ge f_k+d+2\le f_k+k+1\).
For a general DIRK there is not even a guaranteed omitted origin;
for strict SDIRK the full-diagonal rank is already stronger.
Further physical holes, an actual whole-fibre inclusion, or actual
late receiver/mass information are essential to this transfer.

## Independent comparison with the strict zero-through companion

The strict theorem transfers to the actual full-cover carrier with
no extra prefix observation: at the first nonzero \(z_a\) row of
clock \(u_a\), multiplying by \(C-u_a I\) makes the input zero
through that very row. The paid readouts give all centered moment
powers 1 through \(n-1\) for \(n=m-a+1\). Thus
\(T_a=J_0^n(B_{a-1}W)\) has multiplicity at least \(n-1\) at
\(u_a\). In the transition
\((X-u_a)T_a'-(n-1)T_a\) the lowest term cancels, so each earlier
center carries its same full exponent as in the diagonal-refunded
proof. Only the last center loses one. This gives
\(d\ge r(m+1-r)-1\) for a nonzero strict carrier.

It applies when the displayed primitive-error outputs really are
cut off. It does **not** follow just from a sent or nominal profile
of those observations, and a separate gauge recovery must be paid
if the error outputs can leak. This one-degree deficit removes the
midpoint table gains at 16, 17 and 20 if the strict method is used
alone. It still gives a seven-clock/row addition at
\((k,H,p)=(8,13,19)\) with two marks, versus eight under full
diagonal refunds. The late output-mass family is independent of
this choice of marking. For ERK itself the literal strict
triangularity makes the unshifted \(A z\) reading valid at the
mark and there is no need for the weaker shifted construction.

## Source boundary

The staged Lean drafts contain the rank-to-genuine-gain adapter,
native inclusive/exclusive point receiver and basic paid fibre
mass adapter. The new numerical families, conceptual nullity
bound, and strict comparison are paper arguments, not Lean
certificates. No compiler, solver, replay, repository write, or
held path was used.
