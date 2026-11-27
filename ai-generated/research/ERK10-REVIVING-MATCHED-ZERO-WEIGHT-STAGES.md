# A late grade-four match can revive a zero RK10 output weight

Consider a strict explicit RK tableau over a characteristic-zero
field. Use grades equal to rooted tree size minus one.
If a zero-weight physical row \(g\) has an **actually later** live
row \(h\) with the same evaluation functional on \(E_4\), then
there is a same-size strict explicit tableau of the same order
through ten with both these weights live and every other weight
unchanged. This condition is on actual tree profiles, not just
clock coincidence, cubic point exactness, or agreement of selected
defects.

## Proof by a lower-triangular change of coordinates

Use \(S\) equal to the identity except that it replaces the \(h\)-th
coordinate \(x_h\) by \((x_h+x_g)/2\). Its inverse \(Q\) replaces
that coordinate by \(2x_h-x_g\). Since \(g<h\), both are lower
triangular; hence \(A'=SAQ\) is strictly lower triangular.
Also \(S{\bf1}={\bf1}\).
For any actual stage vectors \(x,y\), the only possibly nonzero
entry of \(S(xy)-(Sx)(Sy)\), with pointwise multiplication, is
at \(h\); there it equals \((x_h-x_g)(y_h-y_g)/4\).
Thus it is zero whenever one of the operands agrees on the pair.

Each rooted-stage expression is constructed from the unit by
grafting an \(A\)-advance and multiplying two rooted inputs at
a common root. A graft adds one to the grade, while a product
adds its two input grades. Through grade nine, one factor of
every product has grade at most four. The actual old \(E_4\)
matching hypothesis therefore makes \(S\) multiplicative at
every such root. Induction, using \(A'S=SA\), proves that
the new numerical stage expression is exactly \(S\) times the
old one for every rooted tree of order at most ten. The new
output \(b'=bQ\) reads each as before. In particular its weights
are \(b'_g=-b_h,\ b'_h=2b_h\), with all others unchanged.

More than one ghost can be revived if each has some later
currently-live row agreeing with it on \(E_4\). Use the same
one-pair transformation repeatedly. Since every old stage
expression of grade at most four agrees on a mixed pair, its
\(S\)-image is the original numerical vector. Thus all low
matches survive the earlier transformations. At each step the
newly revived row is live and the designated later live row
stays live; other weights have not changed. This includes
several ghosts sharing a target.

Consequently the [all-live equality exclusion](ERK10-ALL-LIVE-COMPLETENESS.md)
also excludes any 14-stage order-ten candidate in which
**every** ghost has a later live \(E_4\) match. More
generally, if one chooses a hypothetical tableau that minimizes
its count of zero weights, none of its ghosts can have such
a match. This is not a claim that all zero-weight cases meet
the condition. In particular the sole isolated invisible
quadratic ghost does not match any live stage even at \(E_2\).

[ERK10ReviveGhostGate.lean](../lean/RKCert/ReviewedNative/ERK10ReviveGhostGate.lean)
proves both coordinates are inverses, linearity and strict
causality of the conjugation, the exact rooted-word transport
by induction, and the transformed weight formulas. The
stage-word grammar covers arbitrary rooted trees by attaching
a parent and merging roots one branch at a time.
The all-live equality application is conditional on the
remaining proofs in its separate ledger and makes no
unrestricted numerical stage-bound claim.

The portable module was independently checked with Lean 4.34.1, 4.35.0,
4.36.0 and 4.37.0-rc1. It uses a rooted-word interface; the direct bridge
to the separately reviewed tableau order predicate is not formalized here.
