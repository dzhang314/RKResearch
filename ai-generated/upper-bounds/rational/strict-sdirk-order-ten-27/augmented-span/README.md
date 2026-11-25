# Exact order-ten check by graded spans

This is a second exact arithmetic check of the
[27-stage rational strict SDIRK tableau](../tableau.json) with common
diagonal `1/9`. It uses the existing literal at archive revision
`8071977dd0b979bc39258ffe7960750fd09da807`, pinned by SHA-256
`eb0075a13713d9bfb4249391d7d951693c172426ed891b924b2b5c81c0692081`.
It does not enumerate trees, change coefficients, check the next tall
tree, or run Lean. The [separate exact-order argument](../README.md)
gives the eleventh tall failure; there is no stage-minimum or stability
claim.

## Why the finite checks suffice

Write the physical coefficients as `A = M/d` and `b = w/e`, using the
integer matrix and weight numerators in the tableau. For a rooted tree
`t` of order `n`, let `F(t)` be its forest factorial, and store the
integer feature
\[
 G(t)=\bigl(F(t)\Phi_M(t),\,d^{n-1}\bigr).
\]
The leaf gives `(ones,1)`. In the
[reviewed root-attachment convention](../../../../../RKResearch/FiniteRootedTree.lean),
attaching a right tree of order `ℓ` to a left tree with features
`(x,a)` and `(y,z)` gives the feature
\[
 J_\ell((x,a),(y,z))=\bigl(x\odot M(\ell y),\,daz\bigr).
\]
The map is bilinear over the rationals. The classical order condition
at degree `n` is the vanishing of the linear functional
`L_n(x,a)=n(w\cdot x)-ea`, since the tree factorial is `n F(t)` and
`\Phi_A(t)=d^{1-n}\Phi_M(t)`.

The [frozen lower rows](basis.jsonl) have ranks
`1,1,2,4,8,12,17,24,26` in degrees 1–9. Check the leaf, each lower
basis payment `L_n=0`, and every ordered pair of basis rows for every
positive split: below degree ten the joined row must be in the
destination span. The checker proves each membership with a positive
denominator and an exact signed integer combination on all 28
coordinates. Induction and bilinearity then put every actual lower
tree feature in its span. At degree ten, test `L_10=0` directly on
every ordered basis pair. Linearity in each argument proves the
condition for all degree-ten trees without storing a degree-ten basis.

| Exact checks | Count |
| --- | ---: |
| Lower basis-pair memberships (orders 2–9) | 404 |
| Direct order-ten basis-pair payments | 328 |
| Total ordered basis pairs | **732** |
| Lower basis payments / cached child actions | 95 each |
| Leaf | 1 |

## Reproduction

From the repository root, with Python 3.9 or later (standard library only):

```sh
python3 ai-generated/upper-bounds/rational/strict-sdirk-order-ten-27/augmented-span/check_augmented_span.py
```

There are no writes by default. Pass `--emit-receipts NEW_DIRECTORY`
to export the six canonical JSONL streams, including the sparse
integer clearings. The checker computes all identities and verifies
the pinned hashes of the reconstructed streams; any failed check
exits nonzero. The two inputs are the adjacent basis and existing
tableau, resolved relative to the script, not the current directory.
