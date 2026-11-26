# When an output-silent DIRK cohort can be removed

An invariant line for \(A\) and the clock is not in general invisible
to rooted products. There is an exact causal test using the retained
tableau, and a counterexample of arbitrary achieved order, even
with \(C(2)\) and a cohort indicator in the actual \(F_4\).

## 1. A finite causal test on the retained tableau

Let \(A\) be lower triangular on the original ordered stage set.
Let \(D\) be a nonempty set of stages and \(J\) its complement.
Write \(\mathbf u\coloneqq\mathbf1_D\), the physical indicator
of \(D\), and assume
\[
A\mathbf u=a\mathbf u,\qquad \mathbf b\cdot\mathbf u=0.
\tag{1}
\]
The first identity says that every retained row has total coefficient
zero into \(D\) and that every row in \(D\) has the same total
coefficient \(a\) into \(D\). If \(D\) has one numerical clock, (1)
makes the line silent for every word in \(A\) and \(C\), where
\(C\) is the diagonal clock matrix. No rooted assertion follows
from the clock alone.

Let \(B\coloneqq A_{J,J}\), with the inherited physical order,
and take \(i_0\) to be the earliest row in \(D\). Define the
external row difference for \(i\in D\) by
\[
\boldsymbol\Delta_i\coloneqq A_{i,J}-A_{i_0,J}.
\]
For every integer \(q\ge0\), the following conditions are equivalent:
\[
\begin{split}
&\boldsymbol\Delta_i\cdot\boldsymbol\Phi_t(B)=0
       &&(i\in D,\ |t|\le q),\\
&\boldsymbol\Phi_t(A)_i=\boldsymbol\Phi_t(A)_{i_0}
       &&(i\in D,\ |t|\le q+1).
\end{split}
\tag{2}
\]
When they hold, the retained stage profiles agree one order further:
\[
\boldsymbol\Phi_t(B)=\boldsymbol\Phi_t(A)|_J
       \qquad(|t|\le q+2).
\tag{3}
\]
Here and below the tree order is the number of vertices, not the
degree index of the reviewed bounded tree space.

To prove the forward direction, start from
\(\boldsymbol\Phi_\bullet=\mathbf1\). In the reviewed recursion, a
branch of any tree of order at most \(q+1\) has order at most \(q\).
For such a branch, assume that its entries agree on \(D\) with common
value \(z\) and that its retained entries agree with the corresponding
entries for \(B\). On a retained row the omitted sum over \(D\) is zero
by (1). On a row of \(D\), the internal sum is \(az\), independent
of the row, and its external sum is independent of the row by the
first line of (2). The coordinatewise product at the root preserves
both agreements. This is an induction on the reviewed recursion.
For a tree of order \(q+2\), every branch has order at most \(q+1\);
the same retained-row argument now proves (3) without needing
agreement on \(D\) at order \(q+2\).

For the reverse direction, suppose the second line of (2) holds.
Induction on the retained rows uses only the vanishing of the omitted
sum and proves (3) as before. For a tree \(t\) of order at most \(q\),
the extension \([t]\) has order at most \(q+1\). Its two entries on
\(D\) agree. The internal sums cancel in their difference, and the
retained entries of \(\boldsymbol\Phi_t(A)\) are those of \(B\).
The remaining difference is precisely
\(\boldsymbol\Delta_i\cdot\boldsymbol\Phi_t(B)\).

In particular, the first profile that distinguishes two rows of
\(D\) can be taken to be a unary extension. If the first nonzero
external test occurs on \(t\) of order \(k\), the first separation
on \(D\) is at order \(k+1\), whereas the retained profiles are
still equal at least through order \(k+1\).

### Full-series and finite-order consequences

Let \(\mathcal R(B)\) denote the span of all reviewed tree columns
of \(B\). If each \(\boldsymbol\Delta_i\) annihilates
\(\mathcal R(B)\), the principal restriction \((B,\mathbf b|_J)\)
preserves every scalar rooted output. Indeed (2) and (3) apply at
every order, and the common entry on \(D\) has total weight zero
by (1). This check is on the proposed retained tableau, not on
a quotient presumed to be correct. Literal equality of the
external incoming rows is one sufficient special case.

There is also a finite prefix test for that same all-order result.
For each \(i\in D\), its external row difference is supported only
at retained rows earlier than \(i\), by lower triangularity and
the choice of \(i_0\). Restrict to that literal prefix of \(B\).
A measured space of actual tree columns that contains \(\mathbf1\)
and is closed under its \(A\) and coordinatewise multiplication
is its full tree span: the reviewed recursion gives one inclusion
and the other follows from how the space was obtained. Thus it is
enough to test the external row differences on bases of those
actual closed prefix spaces. Equality of two adjacent grades
alone is not a certificate of closure under products.

For finite order \(p\), the exact joint test for *both* retained
stage agreement through order \(p\) *and* scalar output agreement
through order \(p\) is
\[
\begin{array}{ll}
 A_{J,D}\bigl(\boldsymbol\Phi_t(A)|_D\bigr)=0,
            & |t|\le p-1,\\[2mm]
 \mathbf b|_D\cdot\bigl(\boldsymbol\Phi_t(A)|_D\bigr)=0,
            & |t|\le p.
\end{array}
\tag{4}
\]
Sufficiency again follows from the recursion and the separate
output sum. Necessity of the first line under retained agreement
follows by comparing \(\boldsymbol\Phi_{[t]}\) at the retained
rows. Under that agreement, necessity of the second follows
by subtracting the output sums. This is not a claim that (4)
is necessary if only scalar outputs, with arbitrary accidental
cancellations at retained stages, are required to agree.

By (2), agreement on \(D\) through \(p-1\) guarantees the first
line of (4), but not the top-order instance of the second.
There is a convenient equivalent last-order output test under that
agreement, also independently derived by the audit reviewer.
For \(p\ge2\), write
\[
\mathbf g\coloneqq\mathbf b|_D\,A_{D,J}.
\]
All individual \(\boldsymbol\Delta_i\) should kill the retained
tree columns through order \(p-2\). Under precisely this
assumption, principal deletion preserves scalar outputs through
order \(p\) if and only if \(\mathbf g\) kills the retained tree
columns through order \(p-1\). For extension \([t]\) with
\(|t|\le p-1\), its internal contribution on \(D\) is common
and cancels against \(\mathbf b|_D\). Its remaining weighted
read is \(\mathbf g\cdot\boldsymbol\Phi_t(B)\).
The test for \(|t|\le p-2\) already follows from the individual
ones and \(\sum_{i\in D}b_i=0\). Every root with two or more
branches at order at most \(p\) has branches of order at most
\(p-2\), so its profile on \(D\) is already common. Only a
unary root at the last order can contribute anything new.

If the actual \(\mathbf u\) belongs to the reviewed \(F_h\),
the rooted-product lemma implies that the second line is automatic
for \(|t|\le p-h\), since
\(\mathbf u\odot\boldsymbol\Phi_t(A)\in F_{h+|t|-1}\).
One cannot drop the \(h\) in this degree budget.

In the paid tight-floor application, the actual omitted nonzero
clock cohort has \(\mathbf u\in F_{m-2}\) (on the two-unit branch),
up to a nonzero common amplitude. If it consists of two rows
with nonzero output weights, those weights are opposites.
The previous paid product therefore gives agreement on that
pair through \(p-m+2\) and kills its external tests through
\(p-m+1\). This is a genuine input to (2). It still leaves
higher exterior tests and the top output in (4) open.
An actual closed-prefix certificate would remove that gap.

## 2. The full rooted invisibility test and physical merging

Classify stages by equality of \(\boldsymbol\Phi_t(A)_i\) for
every tree \(t\). The reviewed full tree span is a unital
coordinatewise algebra stable under \(A\). If two classes differ,
some tree column separates them; multiplying suitably normalized
pairwise separating columns gives the indicator of each class.
This works over a field without a single generic separating
element. Hence the full tree algebra consists exactly of
functions constant on the actual profile classes.

The action of \(A\) on a class indicator is in this algebra.
Thus the sum of coefficients from any receiver in class \(Q\)
into source class \(P\) is independent of the particular
receiver in \(Q\). Aggregate on these classes, using the
earliest physical representative of each and ordering those
representatives increasingly. A source class represented later
than a receiver has no row early enough to occur in its sum:
the class tableau is lower triangular. Moreover, only the
earliest row itself can occur in its own diagonal sum, so the
new diagonal at that class is exactly the old representative's
diagonal. In particular this construction preserves strict
explicitness or a common diagonal when either holds. The
weights are the sums of original weights in each class, and
the reviewed recursion carries every scalar rooted output to
the class tableau.

For a stage vector in the full tree span, consider contexts
formed by applying \(A\) and multiplying by actual tree
columns, then pairing against \(\mathbf b\). It is invisible
to all these rooted contexts if and only if every profile
class where it is nonzero has no directed path to a class of
nonzero aggregate output weight. An edge runs from a source
class to a receiving class if its aggregated coefficient is
nonzero. Indeed the classes not reaching output are stable
under \(A\), under coordinatewise multiplication, and are
killed by the output. Conversely, along a path to output,
successive class indicators isolate the input and each
following class. The nonzero path factors and final weight
give a nonzero observation. The indicators are linear
combinations of actual tree columns; expansion yields an
actual rooted-product context with nonzero observation.

Thus a repeated cohort with full profile agreement and (1)
can be deleted directly, or merged by an earliest representative
and then deleted as a silent class. If it splits into several
profile classes, invisibility requires the graph condition on
each class separately, not just cancellation in their
arithmetic sum. Graph-invisible classes can all be pruned
after coalescing without changing scalar rooted outputs.
This is the existing reviewed coalescing/pruning machinery
plus the elementary physical-order and diagonal adapter,
not a new arbitrary linear quotient on stages.

## 3. A rational paid counterexample, with a true \(F_4\) mask

There are genuine rational \(C(2)\) DIRK tableaux of any
order \(p\ge6\) with a physically repeated clock cohort \(D\)
such that
\[
\mathbf1_D\in F_4,\qquad
A\mathbf1_D=0,\qquad
C\mathbf1_D=\mathbf1_D,\qquad
\mathbf b\cdot\mathbf1_D=0.
\tag{5}
\]
Every tree profile agrees on \(D\) through order \(p-1\).
Nevertheless deleting \(D\), or merging it into one stage
with its summed weight, breaks an actual order-\(p\) condition.

### A rational \(C(2)\) baseline of every order

Use \(N\)-step trapezoidal composition. Its stages are indexed
\(0,\ldots,N\), with first row zero and row \(i>0\) summing with
weights \(1/(2N)\) at \(0\) and \(i\), and \(1/N\) at the
interior indices. Its output weights are those of row \(N\).
Write \(\mathcal T P\) for the polynomial satisfying
\[
(\mathcal T P)(0)=0,\qquad
(\mathcal T P)(X+1)-(\mathcal T P)(X)
       =\tfrac12\bigl(P(X)+P(X+1)\bigr).
\]
Such a polynomial exists over \(\mathbb Q\) by descending on
degree; the operation increases degree by one and divides the
leading coefficient by the new degree. Its values at nonnegative
integers are the ordinary trapezoid summations. In particular
\(\mathcal T1=X\) and \(\mathcal T X=X^2/2\), proving \(C(2)\).

For every tree \(t\) of order \(r\), the stage profile at index
\(i\) in this block is \(N^{1-r}P_t(i)\), where \(P_t\) is the
polynomial from the reviewed recurrence using \(\mathcal T\)
in place of \(A\). Its leading coefficient is \(r/t!\), by
induction on that recurrence and the tree factorial.
The output is \((\mathcal T P_t)(N)/N^r\). This is a polynomial
in \(1/N\) of degree at most \(r-1\), with constant \(1/t!\),
because \((\mathcal T P_t)(0)=0\). Taking finitely many disjoint
blocks for distinct positive \(N\) and interpolating their
outputs to \(1/N=0\) therefore gives a rational \(C(2)\)
DIRK baseline of any prescribed order \(p\). This uses the
algebraic reviewed order conditions only.

### The two extra cohorts

For a desired first separating tree order \(L\ge6\), choose
\(N_0\coloneqq L-1\) distinct nonzero rational clock values
\(x_l\). Add an independent driver block consisting of a zero
row and one row for each \(x_l\), with coefficient \(x_l/2\)
on that zero row and \(x_l/2\) on itself. The driver clock
is \(x_l\), and the block satisfies \(C(2)\).
At driver \(l\), the tree profile is
\(\kappa_t x_l^{|t|-1}\) with \(\kappa_t\ne0\) independent of
\(l\). This follows by induction, since extending a nonleaf
tree multiplies by \(x_l/2\), and extending a leaf multiplies
by \(x_l\).

Choose a coefficient row \(\boldsymbol\eta\) on the drivers
such that
\[
\sum_l\eta_l x_l^k=0\quad(0\le k\le L-3),\qquad
\sum_l\eta_l x_l^{L-2}=1.
\tag{6}
\]
This is the leading-coefficient row of interpolation on the
distinct drivers. Add two pairs \(D,E\) of stages, each having
zero diagonal and no input except from the drivers. If the
first row on either pair is \(\mathbf w\), make its second row
\(\mathbf w+\boldsymbol\eta\). Define \(M_k(\mathbf w)\coloneqq
\sum_l w_l x_l^k\). For both pairs choose \(M_0=1\),
\(M_1=1/2\) and \(M_2=0\). Choose \(M_3=0\) for \(D\) and
\(M_3=-1/4\) for \(E\). These moments are realizable by
Vandermonde interpolation, and unchanged by (6).
Both pairs have clock \(1\) and satisfy \(C(2)\).

Within either pair the profiles agree through \(L-1\), by
(6) and the reviewed recursion. At order \(L\), only a unary
root can distinguish them: otherwise each branch has order
at most \(L-2\). For a unary tree \([t]\) of order \(L\), the
second entry minus the first equals the same nonzero
\(\kappa_t\) in both pairs.

The physical indicator of \(D\) is the actual pure column
\[
\mathbf u
  =4A\mathbf c^{\odot3}
       -6\mathbf c\odot(A\mathbf c^{\odot2})
       +\mathbf c^{\odot4}\in F_4.
\tag{7}
\]
The three terms are given by order-five trees: the extension
of the four-vertex bush, the root with a three-vertex bush and
a leaf, and the five-vertex bush. Their forest factorials
are \(4,3,1\), respectively. With the stock normalization,
(7) is one normalized column minus twice the second plus
the third, so it is pure. It vanishes on every trapezoidal
baseline row because
\(\mathcal T X^2=X^3/3+X/6\) and
\(\mathcal T X^3=X^4/4+X^2/4\), and it vanishes on every driver
row by its two coefficients \(x_l/2\).
On the pair rows it equals \(4M_3-6M_0M_2+M_0^4\), which is
\(1\) on \(D\) and \(0\) on \(E\). All these are symbolic
identities over \(\mathbb Q\).

### Two distinct failures of deletion

First take \(L=p\). Give the rows in \(D\) weights \((-1,1)\),
those in \(E\) weights \((1,-1)\), and the drivers weight
zero. Retain the original order-\(p\) baseline weights.
The two extra pairs cancel exactly on all trees through
order \(p\), so the whole tableau achieves order \(p\).
Their columns feed no other retained stage, so (5) holds.
All retained profiles in this first example agree at every
order, since there is no outgoing entry from \(D\) to \(J\).
The individual exterior tests in (2) pass through \(p-2\),
but \(\mathbf g=\boldsymbol\eta\) first reads a retained child
at order \(p-1\). At each corresponding unary tree of order
\(p\), the weighted read on \(D\) alone is nonzero. Hence the
rooted product with the actual pure \(\mathbf u\) is observed,
whereas no \(A,C\) word observes \(\mathbf u\).
Deleting \(D\) or merging it into one zero-weight stage removes
that contribution on only one side of the cancellation,
breaking an order-\(p\) condition. This is solely an output
failure, not a failure of retained stage agreement.

There is a second version, for \(p\ge7\), refuting deletion
based only on zero output weights at every omitted row.
Take \(L=p-1\) and give both pairs and the drivers weight zero.
Append two retained receivers, each with zero diagonal and no
input except coefficients \((-1,1)\) to its respective pair.
Their clocks and their \(A\mathbf c\) entries are zero, and
(7) also vanishes there. The receivers are equal through
order \(p\), since the two contrasts first appear at the same
order and with the same coefficient. Give the two receivers
opposite nonzero weights. This preserves full order \(p\);
also \(A\mathbf u=0\) still holds because the outgoing
coefficient sum into each receiver is zero. But after
deleting \(D\), its receiver loses the nonzero unary
order-\(p\) profile, while the other retains it. Thus now
the individual external contrast first reads a retained child
at order \(p-2\), the pair first splits at \(p-1\), and the
first line of (4) fails at branch order \(p-1\).
The aggregate \(\mathbf g\) is identically zero, as is the
direct weighted output of every omitted stage; it is the
retained receiver that first changes at order \(p\).

These constructions are not counterexamples to the
dimension-tight stage floor. They show that the actual
\(F_h\) membership, \(C(2)\), linear word silence, and the
stated bounded rooted-profile agreements cannot replace a
true exterior-transfer or rooted-output test. In the
dimension-tight application the remaining positive route is
to obtain that test from the actual physical cut and its
closed retained tree span, or to identify genuinely
invisible split classes by the stronger rooted contexts.
