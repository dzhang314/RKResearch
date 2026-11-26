# Where a graph-only conclusion stops

## Fixed offdiagonal values: genuinely minimal obstruction

Over Q take p=2 and three stages with common diagonal 0 and
permitted edges only 2→0 and 2→1 (indices 0,1,2). Both choices
(a,b)=(1,1) and (1,−1) give the exact same nonzero support,
which embeds every tree through p. The stage feature vectors
are `(1,c_i)` with c=(0,0,a+b). The first choice spans two
dimensions and the second choice spans just one. Thus support
cannot decide full span for a single fixed realization. This
is minimal for common diagonal and exact nonzero support over
Q: at p=1 any nonempty stage family spans; at p=2 with two
stages the only proper edge, if present, shifts the second
clock by a single nonzero entry, so cannot cancel. No special
order condition or actual method search enters this example.

## Noncommon numerical diagonal: pattern alone is insufficient

Even at p=2 with two isolated stages (no proper edges), the
two features are `(1,δ_0)` and `(1,δ_1)`. Over a field these
span iff the two fixed diagonal values differ. Thus the common
shift is a real hypothesis; one cannot discard arbitrary
fixed diagonal data. This follows already before any tree
with multiple rooted shapes of its size.

## Varying A is not varying only b

Over an infinite field, some *single* allowed matrix with
full output span exists iff at least one maximal stage-feature
minor is a nonzero polynomial in the independent edge entries.
This is a separate criterion from full rank of the coefficient
matrix, which pools rows across many A. The infinite field
claim also holds with exact nonzero support, since a nonzero
polynomial cannot vanish on the entire product of infinite
nonzero sets. Over a finite field test the minors as polynomial
functions; their degrees can exceed the per-feature p−1 cap.
For an already fixed A one simply tests its actual stage rows.

Even stage count alone does not repair the distinction. For p=3
there are four tree shapes through p. Take a complete three-stage
strictly lower triangular block and an isolated fourth stage,
all with zero diagonal. The pattern embeds every tree through
p and its family has full span by the coefficient criterion
(equivalently the folded embedding test). Yet in every fixed
realization the isolated stage and the first stage of the block
both emit only the leaf coordinate, so at most three stage rows
are independent. A finite linear combination across A can be
realized as a disjoint block sum if adding those stages is allowed,
not automatically in the original prescribed four stages.

Finally, specifying the exact order-p target rather than the
entire space is a different question, and failure at p+1 is
outside the coordinate set used here. No exact-next-order,
minimal width, path-rank or stability claim follows merely from
this family span test.
