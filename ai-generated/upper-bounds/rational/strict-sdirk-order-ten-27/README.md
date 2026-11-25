# Exact order-ten strict SDIRK over the rationals in 27 stages

The [literal rational tableau](tableau.json) has 27 stages and common
nonzero diagonal `1/9`. It satisfies every classical rooted-tree order
condition through order ten and fails the eleventh tall-tree condition.
Both the exact arithmetic checker below and the [Lean certificate](native-lean/README.md)
verify this witness. Lean checked the same matrix and weight vector,
including the exact eleventh tall-tree obstruction.

Only a rational upper witness is claimed. This does not establish a
rational stage minimum, change the real-algebraic 17-stage upper bound
at order ten, or claim a stability property.

## Tableau and proof

For the integers in `tableau.json`, let `M = a_integer`, `w = b_integer`,
`d = a_denominator` and `e = b_denominator`. The tableau is
\(A=M/d\) and \(b=w/e\). The checker verifies the dimensions, integer
entries, positive scales, zero entries above the diagonal, and
\(9M_{ii}=d\) for each \(i\). Thus \(A\) is lower triangular over
\(\mathbb Q\) with common diagonal \(1/9\). The first eleven weights are
zero and the other sixteen are positive. The coefficient file is one
self-contained literal; no generator or other tableau is needed.

Use the constructor presentation in the archive's
[rooted-tree definitions](../../../../RKResearch/FiniteRootedTree.lean)
and [order predicate](../../../../RKResearch/OrderConditions.lean).
The leaf has order one, forest factorial one and elementary-weight
vector \(\boldsymbol 1\). For the binary constructor \(t=u\mathbin{\triangleleft}v\),
which adds child \(v\) at the root of \(u\), write \(n(t)\) for its order
and \(F(t)\) for its forest factorial. The exact recurrences are
\[
n(t)=n(u)+n(v),\qquad
F(t)=F(u)n(v)F(v),\qquad
\Phi_M(t)=\Phi_M(u)\odot M\Phi_M(v).
\]
Here \(\odot\) is componentwise multiplication and \(t!=n(t)F(t)\).
Induction gives \(\Phi_A(t)=d^{1-n(t)}\Phi_M(t)\). Thus the reviewed
order condition \(t!\,b^\mathsf T\Phi_A(t)=1\) is equivalent to the
integer equality
\[
n(t)F(t)\,w^\mathsf T\Phi_M(t)=e\,d^{n(t)-1}.
\]

To enumerate at order \(n>1\), the checker takes all ordered pairs of
trees of orders \(j\) and \(n-j\) for every \(1\leq j<n\). The unique
outer constructor and induction on order prove that this visits every
tree in the reviewed predicate. No unproved symmetry reduction is
needed: different branch orders are checked directly. For orders
one through ten the counts are
\(1,1,2,5,14,42,132,429,1430,4862\), totaling **6,918** presentations.
The checker verifies the integer equality for each one.

For the tall tree with eleven vertices, the checker computes
\[
b^\mathsf T\Phi_A(t_{\mathrm{tall},11})=
\frac{5946972394780345710421384301593}
 {224017752875470299449731184306688000000}
\ne \frac{1}{11!}=\frac{1}{39916800}.
\]
The target \(1/11!\) follows from the same tree-factorial recursion.
Thus the same tableau does not satisfy order eleven.

## Reproduction

From the repository root, run:

```sh
python3 ai-generated/upper-bounds/rational/strict-sdirk-order-ten-27/check_exact_table.py
```

This uses only the Python standard library, with integer and exact
rational arithmetic. Any failed check exits nonzero. The checker pins
the coefficient file by SHA-256, evaluates every ordered presentation,
and prints the exact next tall-tree weight. It is not a Lean replay.

For an independent verification through order ten without enumerating
trees, see the [graded-span arithmetic checker](augmented-span/README.md).
It checks 404 lower basis-pair memberships and 328 direct top payments.
The next tall-tree check above is separate.
