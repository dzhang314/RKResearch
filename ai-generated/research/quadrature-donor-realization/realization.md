# Every paid scalar quadrature has a triangular RK realization on its support

## Statement

Let \(R\) be a nonzero commutative unital ring and \(p\ge1\). A finite
scalar rule has reviewed quadrature order at least \(p\) if
\[
 (k+1)\sum_x \mu_x x^k=1 \qquad (0\le k<p).
 \tag{1}
\]
Here \(x\) ranges over its distinct contributing sites, after grouping
repetitions and removing zero aggregate weights. Write \(m\) for that
count. Every such rule admits a lower-triangular tableau satisfying
the actual reviewed `HasOrder p A b` **with exactly the prescribed
contributing sites and masses**. Each of the \(m\) sites has one active
row. All helper rows have output weight zero. For \(p\ge2\) one can
use \(\binom p2\) helper rows, and for \(p=1\) one helper suffices.
The diagonal entry of **every** row can be prescribed.

In particular, prescribe zero diagonal for ERK, arbitrary diagonal
for DIRK, or a chosen common nonzero diagonal over a field (common
unit over a ring) for strict SDIRK. For rational input and rational
prescribed diagonals the construction is entirely rational. The
number of physical rows in this construction is not a stage
minimum. No signs on the entries of \(A\) or stability conditions
are asserted; the actual output weights are precisely the chosen
masses and zeros.

## 1. The donor step, on the actual tree columns

Write \(|T|\), \(T!\), and \(\operatorname{ff}(T)\) for reviewed tree
order, factorial, and forest factorial. They have
\[
 \operatorname{ff}(T)=\prod_{t\in\mathrm{ch}(T)} t!,\qquad
 T!=|T|\operatorname{ff}(T).
\]
These are also the identities for the reviewed binary presentation:
starting with the leaf, `base ◂ branch` multiplies the forest
factorial by the new branch factorial and the stage response by the
new branch contribution. Thus the actual column at row \(i\) is
\(\Phi(T)_i=\prod_{t\in\mathrm{ch}(T)}(A\Phi(t))_i\), including the
empty product \(1\). A row of clock \(x\) is called *pure through tree
order \(g\)* here if
\[
      \Phi(T)_i=\frac{x^{|T|-1}}{\operatorname{ff}(T)}
               \qquad (|T|\le g).
 \tag{2}
\]
This is a statement about all the actual tree columns, not just about
monomial input stage conditions.

The integers \(1,\ldots,p\) are units in \(R\) by (1). In particular
all factors used in the tree and forest factorials through order \(p\)
are units. Let \(2\le g\le p\), and take \(g-1\) prior rows
\(D=(j_1,\ldots,j_{g-1})\), pure through tree order \(g-1\), with
clocks \(z_j\) whose pairwise differences are units. Append a
row with desired clock \(x\), prescribed diagonal \(d\), and
strictly lower entries only at these donors. Choose their coefficients
\(a_j\) by
\[
 \sum_{j\in D} a_j z_j^k=\frac{x^{k+1}}{k+1}-d\,x^k
                       \qquad (0\le k\le g-2).              \tag{3}
\]
This is a square Vandermonde system with unit determinant, hence an
exact solve over \(R\) itself. The donor stage-response vectors
are independent already on the \(g-1\) bush columns of orders
1 through \(g-1\), which form that same Vandermonde block.
Alternatively, for the Lagrange basis
\(\ell_j(X)=\prod_{r\ne j}(X-z_r)/(z_j-z_r)\) use
\[
 a_j=\mathcal I_x(\ell_j)-d\,\ell_j(x),\qquad
 \mathcal I_x(X^k)=x^{k+1}/(k+1).
\]
No coefficient of \(b\) enters these row solves. The \(k=0\) equation
makes the row sum \(x\). Causality leaves all old rows unchanged.

Induct on the order of \(T\) to prove (2) at the new row. The leaf is
automatic. A child \(t\) of a tree of order at most \(g\) has order
\(r\le g-1\), so the donor rows are pure for it, and the diagonal
uses the induction value \(x^{r-1}/\operatorname{ff}(t)\) at the
same new row. Therefore the actual matrix action on this child is
\[
 (A\Phi(t))_i
   =\frac{\sum_j a_j z_j^{r-1}+d x^{r-1}}{\operatorname{ff}(t)}
   =\frac{x^r}{t!}.
\]
Multiplying the child identities gives \(x^{|T|-1}/\operatorname{ff}(T)\)
as desired. This is well founded even for a nonzero diagonal:
the diagonal contribution always evaluates a strictly smaller tree.

## 2. One universal zero-output donor bank

Use one diagonal-only first row as the order-one bank; its
clock is its prescribed diagonal, and every row is pure at the
leaf. For each \(g=2,\ldots,p-1\), append \(g\) rows using just the
bank at order \(g-1\) and (3). Choose clocks with pairwise unit
differences within the new bank. This is always possible over \(R\):
\(0,1,\ldots,g-1\) have pairwise unit differences by (1).
There is no need for a unit difference or any distinctness
**between** the banks. Over an infinite field the clocks can even
be chosen fresh globally and away from the contributing sites, apart
from an unavoidable coincidence if the first prescribed diagonal is
itself a contributing site. None of these choices affects earlier rows.
If the optional avoidance of target sites is not needed, a single bank
can be fixed once, independently of any target quadrature.

Give every bank weight zero. Append one row of grade \(p\)
per contributing site \(x\), using (3) with the last bank and
putting \(b_i=\mu_x\) in this row. There are no dependencies between
different active rows. If \(p=1\), instead use the one leaf bank and
the single row sum equation \(a=x-d\); only the leaf response is
needed. In all cases the output sees exactly its original sites and
masses, with the helper bank entirely invisible to scalar quadrature.
For each reviewed tree of order \(r\le p\), (1) and (2) give
\[
 (T!)\sum_i b_i\Phi(T)_i
    =r\sum_x \mu_x x^{r-1}=1.
\]
This proves literal `HasOrder p A b`. There are \(1+2+\cdots+(p-1)\)
helpers for \(p\ge2\). For rational data, solve (3) over \(\mathbb Q\)
with rational donor clocks and the fixed rational diagonal. More
generally, if only the contributing clocks and diagonal entries are
rational, \(A\) can still be rational independently of whether \(b\)
is rational; only the prescribed aggregate masses enter \(b\).

The construction requires no bound on the allowed set of *contributing*
sites. It does not require every zero-output helper clock to be
among the given sites. A repeated helper clock has no effect on
the grouped output; in particular a forced first-row coincidence
does not add a contributing site.

## 3. Exact order and a one-extra-helper refinement

If the original scalar rule pays (1) through \(p\) but fails the
moment of degree \(p\), the constructed tableau is **exactly** order
\(p\). The next reviewed bush has response \((A\mathbf1)^p\)
and factorial \(p+1\), and sees the same nonzero moment defect.
No other tree of order \(p+1\) need be checked.

There is also an exact-order refinement even when the next bush
passes. For \(p\ge2\), enlarge the last bank from \(p-1\) to \(p\)
donors. For \(p\ge3\) this just adds one more row made from the
prior bank; their new clocks can be \(0,\ldots,p-1\) with unit
differences. For \(p=2\) append to the leaf bank a second pure
leaf row with clock \(z+1\), where \(z\) was the initial clock;
the row sum equation achieves it with the prescribed diagonal.
In each output row preserve (3) for \(k=0,\ldots,p-2\) and use
the extra independent row of Vandermonde data
\[
 \sum_{j\in D} a_j z_j^{p-1}
        =\frac{x^p}{p}-d x^{p-1}+\xi_x .
 \tag{4}
\]
Nothing of tree order at most \(p\) changes in the output.
Take the order-\(p+1\) tree with one child that is itself the
order-\(p\) bush. That child has response \(c^{p-1}\) on *all*
rows regardless of donor purity. At active row \(x\), equations
(4) and the diagonal term make its parent response \(x^p/p+\xi_x\).
The parent factorial is \(p(p+1)\).
If \(p+1\) is not a unit, its order condition is impossible
already. Otherwise changing \(\xi_x\) from 0 to 1 at one chosen
contributing site changes the factorial-scaled output by the
nonzero \(p(p+1)\mu_x\). At least one of those choices fails
the order-\(p+1\) condition. The site exists because the weight
sum is 1. The tree is not the next bush for \(p\ge2\), so this
refinement works even while the next bush passes. It costs one
extra helper and preserves the original active weights and clocks.

For \(p=1\) the sole order-two tree is the bush. With prescribed
support *and masses*, exact order one is possible precisely if
the supplied rule fails the linear moment. It would be false
to guarantee exact order one when the fixed scalar rule also
has order two.

## 4. Equality concerns support, not physical width

Fix the coefficient setting, allowed contributing sites, and any
restriction on the aggregate masses (for example positivity of
those masses in an ordered field). Allow arbitrary zero-output
helper rows. For each of ERK, DIRK and strict SDIRK with any one
fixed permitted common diagonal, the **set of attainable finite
weighted contributing supports** for order *at least* \(p\) is
exactly the set for scalar quadrature order at least \(p\):

- Every such tableau supplies (1) by the reviewed bushy-tree
  theorem, after grouping.
- The donor bank realizes every such scalar rule, unchanged on
  its weighted support.

Thus their minimal contributing support counts coincide whenever
the feasible sets are nonempty, and emptiness also matches. If
the RK order is required to be **exactly** \(p\ge2\), the one-extra-
helper refinement gives the same equality against scalar quadrature
order *at least* \(p\). An exactly order-\(p\) RK method may fail
on a non-bush tree while its scalar quadrature holds to higher
order. For \(p=1\) exact-support equality uses exact scalar order one.

Over a characteristic-zero field with rational contributing sites
and arbitrary masses, the minimal scalar support is also the same
as over \(\mathbb Q\). Choose any \(p\) distinct rational nodes and
solve their rational Vandermonde weight equations; this proves
a support minimum exists with \(m\le p\). In any minimal
mixed-field rule its first \(m\) moments force all *aggregate*
weights to be rational by that invertible rational Vandermonde
system. This last rational-weight conclusion is about a minimum
(or any particular \(m\le p\) rule), not about general rules
with larger prescribed support.

For the [positive 19-site rule with nodes \(u/128\)](../rational-quadrature-four-shift/standalone-19.md),
the [exact check](../rational-quadrature-four-shift/standalone-19-check.txt)
gives its degree-20 moment defect as
\[
 \sum_x\mu_x x^{20}-\frac1{21}
   =-\frac{35673661962961255473941956091}
           {302182019494570093201085819637437237821440}\ne0 .
\]
Consequently the ordinary 190-helper donor bank yields rational
tableaux of **exactly order 20** with precisely 19 contributing
sites in all three classes, including every fixed rational
common nonzero diagonal. Their next bush fails. These particular
realizations use 209 physical rows, not 19 and not a claim about
an improved stage upper endpoint. Combining with the independent [four-shift bound](../rational-quadrature-four-shift/proof.md), the actual
minimal **rational** contributing support at order 20 in each
class lies in \([17,19]\), and equals the unknown standalone
rational quadrature minimum. This also holds for mixed-field
tableaux whose contributing sites are rational. Nothing here decides
whether 17 or 18 is attained.

## Evidence status

The [exact checker](verify-donor-lift.py) verifies small literal
rooted-tree examples, the extra non-bush perturbation, and each
rational donor equation in the 19-site transfer. It uses fixed
formulas, not an order-20 tree enumeration or a tableau search.
Run `python3 verify-donor-lift.py` and compare the
[expected output](exact-check.txt). No Lean certificate for the
donor realization is claimed.
