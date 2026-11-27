# Rational even orders by merging the entire preparatory head

These are exact ordinary rational strict SDIRK tableaux with common
nonzero diagonal (1/4). The even upper bounds improve as follows:

| Terminal order | Previous rational upper | New physical stages | Prior preparation stages | Actual copied rows |
|---:|---:|---:|---:|---:|
|12|29|**28**|22|5|
|14|39|**38**|31|6|
|16|50|**49**|41|7|
|18|63|**61**|52|8|
|20|77|**75**|65|9|

These are upper bounds, not minimum-stage or stability claims. They
do not change the smaller unrestricted real-algebraic stage table.

**Verification split.** The 28-stage literal passes an independent
complete integer Gram order check as well as triangularity, common
diagonal, and exact next-bush checks. The full actual order-12
existence theorem, with real physical copies removed, also passed
[Lean 4.36.0](../../lean/evidence/even-moment-tail-20261127/README.md)
using only standard axioms. Orders 14, 16, 18 and 20 currently have
explicit exact rational construction and finite scalar, matrix-feed
and literal-merge gates, not a claim of full Lean replay at those
orders. The higher data can be completely regenerated.

## Stage-count reason

Write (p=2m). In a **preparation** lift choose the low subtree
cutoff (q=m), with (a=p-q-1=m-1) chronological pivot rows. A
((p-1))-site rational scalar rule leaves (m) early rows outside
that pivot block. It only needs an old decoder through size (m);
one actual old size-(m) sample together with the old order
(2m-2) moment rows gives that decoder. Thus **every early row**
of the preparation is at least locally exact through size (m+1).
Old higher pure rows qualify as literal copies. To conserve future
high donors, three actual size-((m+1)) observations plus the old
moments give the next-grade decoder. For order 12 preparation,
two observations are inherited, and the first fresh early row
provides the third. On the later preparations three appropriate
observations are already inherited. The decoder is paid on the
physical prefix before each protected new stage is assigned.

| Preparation order | Physical rows | Copies | Head rows' locally exact sizes |
|---:|---:|---:|---|
|10|22|0|6, 6, 6, 7, 7|
|12|31|2|7, 7, 7, 8, 8, 8|
|14|41|3|8, 8, 8, 9, 9, 9, 9|
|16|52|4|9, 9, 9, 9, 10, 10, 10, 10|
|18|65|4|10, 10, 10, 10, 11, 11, 11, 11, 11|

For a **terminal** lift to (p=2m), choose the lower cutoff
(q=m-1). Thus (a=m), leaving (m-1) virtual early rows.
The entire ((m-1))-row preceding preparation head is eligible,
including its merely low-pure rows, not only the high bank. Place
all of them first and compare their entire strict predecessor
rows exactly. Every virtual early row is then redirected into
its earlier physical representative, so only the (m) pivots
are new physical rows. This selection trades away higher
preparation for the next lift; it does not claim these cheap
terminal tableaux are the optimal prefixes for another lift.

To place the remaining quadrature site, prescribe only the last
(a-1) ladder clocks, leaving the first pivot free. If (F_0)
is the monic product over the fixed clocks, its real rational
value is (z=I(XF_0)/I(F_0)), where (I) integrates on
([0,1]). The new nodal polynomial ((X-z)F_0) has zero integral.
All roots are distinct, all weights nonzero, and the degree-(p)
scalar defect is nonzero in the supplied exact arithmetic.

## Exact proof obligations for each terminal tail

Let \(A_0,\boldsymbol{b}_0\) be the already paid preparation, \(U\)
the old-to-new feed, \(B\) the new block, \(\boldsymbol{c}\) its
physical clocks, and \(\boldsymbol{w}\) its output weights. The
ordinary condition is tested on the normalized column
\(\boldsymbol{N}_t=F(t)\boldsymbol{\Phi}_t(A)\). The first (a-1) reverse
moment rows have old polynomials (h_j) of degree at most
(j-1), so their weighted readouts are covered by the old
ordinary order (p-2). Only the highest row (j=a-1=m-1)
allows degree (j). It can occur only for a high attached
subtree of size (m=q+1): its size plus (j+1) is at most
(p), and its size exceeds (q). An actual size-(m)
decoder buys that precise readout, not an additional old
whole-tree order. The same decoder supplies the finite low
integration compatibility on all inputs through size (q).

The numeric construction checks the reverse Newton identity,
its actual old-to-new weighted feed, all low integrated
columns in the weighted pivot basis, the inverse defining
each mixed receiver, the scalar adjoint identity, and literal
predecessor equality on every copied row. Because the pivot
matrix is invertible and the earlier head is already paid,
these identities imply the actual pointwise low equations.
The symbolic proof then inducts on the binary rooted constructor,
paying all affordable root clock moments together: a small
child shifts the tested base moment, while a large child has
a small base and reads already proved moments of the smaller
attached child plus the paid old frontier. This is the standalone
`general_tail_hasOrder` theorem; `oneSpare_pay` justifies the
frontier policy. It does not amount to a native replay of each
higher numeric instantiation.

## Reproduce

From this directory, with Python and SymPy, the seed is the
[archived seven-stage order-six input](../strict-sdirk-rational/seven-stage-order-six-numerators.json).
Its digest is pinned in `seed6.sha256`. Regenerate and verify the
literal orders 8, 10 and 12:

```sh
out="$(mktemp -d)"
python3 build_even12.py ../strict-sdirk-rational/seven-stage-order-six-numerators.json --out "$out"
python3 check_shape_bush.py "$out"/tableau-{8,10,12}.json
python3 ../rooted-tree-gram/check_gram.py "$out"/tableau-{8,10,12}.json
```

The full even family and its prep stages are exact source data on
demand, rather than committing repeated large denominators:

```sh
out="$(mktemp -d)"
python3 build_terminal_family.py tableau-10.json --out "$out" --through 20
(cd "$out" && sha256sum -c "$OLDPWD/family.sha256")
```

The finite construction logs and fixture hashes are recorded. The
generated terminal order-12 file is byte-identical to the separately
verified and symbolically certified literal.
