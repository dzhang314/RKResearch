# Transporting the ERK stage barrier to semirings

Let $S$ be a commutative unital semiring. The denominator-cleared
condition for a rooted tree is
$$
t!\bigl(\mathbf b\cdot\boldsymbol{\Phi}_t(A)\bigr)=1.
$$
Both sides are polynomials in the tableau entries with nonnegative
integer coefficients. In particular the equations, and strict lower
triangularity of $A$, are preserved by unital semiring homomorphisms.

## Exactly when transport to a nonzero ring is possible

The additive group completion of $S$ carries a commutative ring
structure: multiplication extends by distributivity to differences.
The images of $x,y\in S$ are equal precisely when $x+u=y+u$ for
some $u\in S$. Consequently the completion is nonzero if and only
if there is no $u\in S$ with $u+1=u$. Conversely, such an equality
would force $1=0$ in any unital ring image. Therefore
$$
S\text{ has a unital map to a nonzero ring}
\quad\Longleftrightarrow\quad
(\forall u\in S)\;u+1\ne u .
$$
This condition is weaker than additive cancellation. For example,
the product of the nonnegative rationals and the Boolean semiring is
not additively cancellative, but projection to the first factor gives
a unital map to the rationals.

Under this condition every order-five explicit tableau maps to one
over a nonzero commutative ring, and so has at least six stages by
the [ring theorem](../../lean/AuditReviewedNativeERKUniform.lean).
In fact it is enough to apply the test in the subsemiring generated
by the entries of $A$ and $\mathbf b$, together with $0$ and $1$.
The denominator-cleared conditions use no additional constants.

## Without a ring image, the barrier may hold or fail

In $\mathbb R_{\geq0}\cup\{\infty\}$ with extended addition and
multiplication and $0\cdot\infty=0$, the absorbing sum
$\infty+1=\infty$ prevents a nonzero ring image. Nevertheless the
order-five barrier holds. Expand each required equation as a finite
sum of products of entries. Any product containing an infinity must
also contain a zero; otherwise the left side would be infinity.
Replacing every infinite entry by zero preserves all required
equations and strict triangularity. The resulting tableau over the
nonnegative reals maps to the reals, where the ring theorem applies.

There is a finite example with the same behavior. Start with
$\mathbb F_7$, adjoin an external zero $0_*$ as additive identity
and multiplicative absorber, and then adjoin infinity. Infinity
absorbs every sum and every product except multiplication by
$0_*$. The field's internal zero remains distinct from $0_*$.
A sum is $0_*$ only if both summands are $0_*$; this verifies
distributivity for an infinite multiplier. With finite multipliers
the remaining rules follow from field distributivity or absorption
by $0_*$. The same deletion of infinite entries works because a
product of finite nonexternal entries remains in the field copy.
After deletion, send $0_*$ to the field's zero and apply the ring
theorem over $\mathbb F_7$.

In the Boolean semiring the barrier fails. Take five stages with
ones on the adjacent subdiagonal, zeros elsewhere, and output
weight one at stage five only. At a stage indexed by $i$ starting
at one, the tree weight is one if and only if the tree has height
less than $i$. This follows by induction: extension shifts the
stage vector and rooted sum takes its coordinatewise Boolean
product. Every tree on at most five vertices has height at most
four. The output for each of these trees is therefore one, and
every positive integer represents one in the Boolean semiring.

Thus the additive completion characterizes the transfer argument.
Its vanishing does not characterize whether the stage barrier holds.
