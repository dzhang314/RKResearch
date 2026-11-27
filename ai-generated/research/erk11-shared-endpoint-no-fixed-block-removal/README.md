# Zero weight at the shared endpoint does not suffice

This is a scoped fixed-block obstruction, not a lower bound for all
twenty-one-stage explicit methods. Its [seed](tableau.json) is an exact
22-stage order-eleven method over \(\mathbb Z[1/11!]\), from the same
weighted reverse architecture as the shared-origin result but with a
second attempted overlap. The moved reverse width is \(4/3\), the
forward width is \(2/3\), and the reverse endpoint has physical clock
\(-1/3\). Give its two essential live donors half the scalar weight
\(-243/88000\) each and transfer their balancing copies into a pure
row of total output weight zero. This row (zero-based index 11) still
appears in four later incoming rows, so its removal is not immediate.
The paid common denominator is \(398337730560000\), and the next
bush has factorial-scaled residual \(1/165\).

Here is an exact stronger test allowing all chronological source
redistributions in a fixed rectangle. Hold all matrix entries fixed
except those in rows 16 through 21 and columns 0 through 15. Allow
every such redistribution that preserves the clock vector
\(\boldsymbol c\); require column 11 to become identically zero, and
keep its output weight zero. Allow every other output weight before
row 16 to vary independently, with later output weights fixed.
The column is zero above row 16 already, so success would permit
literal deletion of its stage. There is no such redistribution over
\(\mathbb F_{13}\), hence none over \(\mathbb Z[1/11!]\).

For the proof place each removed coefficient in column 0 to make a
baseline. There are 84 free matrix variables: each adds an amount
to another surviving column of that row and subtracts it from
column 0. There are 15 independent early output variables. All 56
trees used by the [dual receipt](dual-mod13.json) are spines, with
at most one non-leaf child at every root. For each such tree,
\(\boldsymbol{\Phi}_t(A)\) is a product of diagonal clock powers
and matrices applied to a clock power vector. Every nonzero term
of the product can cross from rows before 16 to rows from 16 on
only once, by strict explicitness. Thus each moment is exactly
affine in all 99 variables, not a linearization of a nonlinear
condition. The varied output weights multiply unchanged early
entries and also produce no cross terms. The independent verifier
replays each coefficient by exact substitution modulo 13. The
weighted sum of the 56 requirements has zero coefficients for
all 99 variables and inconsistent constant term 1.

    python3 -B audit_dual.py --full
    sha256sum -c sha256.txt

The optional full check verifies all 3,047 ordinary rooted
equations of the unmodified 22-stage seed as well. The obstruction
does not apply if other matrix blocks, the fixed late weights, or
the seed are changed. This is an exact arithmetic certificate, not
a Lean theorem.
