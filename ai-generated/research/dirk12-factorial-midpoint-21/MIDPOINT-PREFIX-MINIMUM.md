# Twenty-one is also sharp for arbitrary readout of uniform midpoint prefixes

This is a scope-specific lower bound, not an unrestricted DIRK lower
bound. Unlike the separate endpoint-mixture stability proof, it makes
no assumptions on the output weights, on branch endpoints, or on the
sign or size agreement of steps **between** branches. It even allows
sign changes **within** each branch, as long as the squared step is
constant on that branch. It works in every nonzero commutative unital ring;
no ordered-field hypotheses are used.

Take finitely many disjoint branches, the \(m\)-th of length \(\ell_m\).
On a branch let \(h_{m,j}\) be the \(j\)-th midpoint step, now numbered
from zero. The actual causal tableau uses diagonal \(h_{m,j}/2\),
earlier same-branch taps \(h_{m,k}\), and no off-branch taps.
Require \(h_{m,j}^2=u_m\) independent of \(j\) within each branch,
but allow any final branch time, repetitions, and any literal
\(\mathbf b\). If it has rooted-tree order at least twelve, then
\(\sum_m\ell_m\ge21\).

## Paid two-variable functional

It suffices to prove this over a field: reduce any nonzero
commutative coefficient ring modulo a maximal ideal. Every rooted
condition and the literal branch identities descend through the
ring homomorphism. Order twelve makes \(12!\) a unit by the tall
tree, so in any such field \(2,\ldots,12\) are nonzero. The reduction
can turn some \(u_m\) into zero; this is handled below.

Write \(S_j=\sum_{k<j}h_{m,k}\) within a branch. The literal node is
\(c_{m,j}=S_j+h_{m,j}/2\). The same-branch telescope gives
\[
  2\sum_{k<j}h_{m,k}c_{m,k}=S_j^2,
  \qquad 2(A\mathbf c)_{m,j}-c_{m,j}^2=h_{m,j}^2/4.
\]
Indeed each summand multiplied by two is
\((S_k+h_{m,k})^2-S_k^2\); the remaining diagonal contributes
\(h_{m,j}c_{m,j}\). Consequently the literal vector \(\mathbf u\)
having value \(u_m\) on branch \(m\) is four times the actual
order-three quadratic defect, and lies in the actual forward
space \(F_2\). The usual clock and product rules give
\(\mathbf u^k\mathbf c^a\in F_{2k+a}\) for each \(k\ge1\);
this is a statement about the original rooted elementary vectors,
not an added “if the flags happen to hold” hypothesis.

Equivalently, for a direct tree check, merge the roots of any two
rooted trees. Their Butcher weight vectors multiply entrywise, and
the sum of their numbers of nonroot vertices is unchanged by merging.
For a tree with \(a\) nonroot vertices, assign the exact stage monomial
\(X^a\) times its number of vertices divided by its tree factorial.
These monomials multiply under root merging, since the ratio is the
reciprocal of the product of the child tree factorials. Thus the
exact stage monomials for \(A\mathbf c\) and \(\mathbf c^2\) are
\(X^2/2\) and \(X^2\); their defect has zero assigned monomial. The
rooted output condition reads the assigned monomial by \(\mathcal I\).

For any \(P(X,Y)\) of weighted degree at most eleven, with
\(\deg X=1,\deg Y=2\), the literal output therefore gives
\[
   \mathbf b^T P(\mathbf c,\mathbf u)
     = \mathcal I(P(X,0)),\qquad
     \mathcal I(X^a)=1/(a+1).
\]
Pure \(X\) moments are the rooted bushes. Every term with a \(Y\)
is a paid forward defect and thus has zero output. The symbol
\(\mathcal I\) is a finite algebraic moment functional, not a
real analytic integral.

## The support debit at each depth

Fix \(0\le n\le5\). Let \(E_n\) be the set of distinct **nonzero**
values \(u_m\) occurring on branches of length \(>n\). Suppose
\(n+|E_n|\le5\), and use the paid polynomial
\[
  P_n(X,Y)
    =X\!
       \prod_{r=0}^{n-1}\bigl(X^2-(r+\tfrac12)^2Y\bigr)
       \prod_{v\in E_n}(Y-v).
\]
Its weighted degree is \(1+2n+2|E_n|\le11\). It vanishes at every
literal row:

* If \(u_m=0\) then each branch step is zero in the field, so \(c_{m,j}=0\).
* If \(u_m\ne0\) and \(\ell_m>n\), the \(Y-u_m\) factor occurs.
* Otherwise every row on \(m\) has \(j<n\). Choose one step
  \(h\) with square \(u_m\). Each step in that branch equals
  \(h\) or \(-h\) since the field has no zero divisors.
  Thus \(c_{m,j}/h\) is a half-integer with absolute value
  \(r+\tfrac12\) for some integer \(0\le r\le j\).
  This assertion is first about the signed integer sum of the
  selected signs (at most \(j\) previous units), then mapped to
  the field; it does not use an ordering of that field.
  Hence a factor in the first product vanishes.

But its paid output is
\[
   \mathcal I(P_n(X,0))
     =\frac{\prod_{v\in E_n}(-v)}{2n+2},
\]
which is nonzero in the field. This contradicts rowwise
vanishing, including for \(E_n=\varnothing\). In particular the
proof does not divide by a vanishing or repeated branch mass.
It follows that at least \(6-n\) physical branches have length
\(>n\). Summing over \(n=0,\ldots,5\) gives
\[
    \sum_m\ell_m
      \ \ge\ \sum_{n=0}^{5}\#\{m:\ell_m>n\}
      \ \ge\ 6+5+4+3+2+1=21.
\]
Equality forces exactly one branch of each length \(1,\ldots,6\);
at \(n=0\) it also forces the six squared steps to be nonzero and
pairwise distinct after every residue-field reduction. The
twenty-one-stage uniform rational witness in this directory
attains the bound over any nonzero commutative ring inverting
\(12!\).

This does not handle genuinely varying absolute step sizes inside a
branch, cross-branch taps, or general ordinary DIRK factorizations.
