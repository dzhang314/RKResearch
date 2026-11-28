# Scalar degree-eleven quadrature over the factorial localization needs eleven anchored sites

Over \(S=\mathbb Z[1/12!]\), any scalar quadrature exact through
degree eleven whose node set includes both 0 and 1 has at least
11 physical nodes. Either anchor may have zero weight, and
repeated nodes do not help. This is a scalar obstruction, not an
unconditional stage lower bound for ordinary DIRK. It excludes the
nine-node anchored subquadrature shortcut for paying four weighted
reverse trapezoids, without imposing any symmetry or unit-gap
hypothesis.

Reduce nodes and weights modulo 13 and sum weights of coincident
residue sites in \(\mathbb F_{13}\). Write \(w(a)\) for each merged
score, using zero at omitted sites. The twelve exact moments are
\(\sum_a a^j w(a)=1/(j+1)\), for \(0\le j\le11\).
The moment matrix has rank twelve, by a twelve-node Vandermonde.
The constant vector has zero moments, and hence spans its kernel.
A particular weight vector is the truncated harmonic polynomial
\[
 \rho(a)=\sum_{k=1}^{12} a^k/k.
\]
Indeed every \(j+k\) in the positive sum is at most 23, and
\(\sum_a a^{j+k}\) is zero unless \(j+k=12\), when it is \(-1\).
Thus the \(j\)-th moment here is
\(-1/(12-j)=1/(j+1)\) in the field. All possible score vectors
are exactly \(w(a)=\theta+\rho(a)\).

At \(a=0,1,\ldots,12\) the values of \(\rho\) are
\[
 (0,0,7,8,0,6,4,3,4,6,0,8,7).
\]
If \(\theta=0\), the nine nonzero scores omit both anchors and
thus require at least eleven nodes when the anchors are included.
If \(\theta\ne0\), at most two of the thirteen scores vanish,
so there are already at least eleven nonzero residue sites.
Every distinct required residue site needs a physical node.
Over \(\mathbb F_{13}\) the anchored floor eleven is attained
(for example, \(\theta=0\) with both anchors included as unused
rows). No global \(S\) equality is claimed from this residue
case.

The Python replay checks all finite scores and moment identities.
The core Lean receipt kernel-checks the literal table, finite
moments and the eleven-label minimum for the explicit score
family on all four compilers. The Vandermonde argument and
reduction from \(S\) are the separate mathematical proof above.
