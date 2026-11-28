# One appended row cannot upgrade the fixed rational ERK9 tableau

The [literal fourteen-stage rational order-nine tableau](../erk9-fourteen-rational-triple/README.md)
cannot become order ten by appending one arbitrary strict row and
changing the output weights arbitrarily, while keeping all fourteen old
rows unchanged. The obstruction is to the unchanged-prefix extension,
not to general 15-stage rational ERK10 or retunings of the old matrix.

## General actual-tree rank criterion

Let an \(s\)-stage strict tableau over a commutative ring
have actual order at least \(p\ge2\), with output \(\boldsymbol b\).
Suppose its rooted derivative vectors through size \(p-1\) span
the whole coefficient module (it suffices that their dot-product
annihilator be zero). Append any strict row \(\boldsymbol a\),
keep the old matrix unchanged, and write
\(z=\boldsymbol a^\top\boldsymbol 1\) for the new clock.
Assume the extended output \((\boldsymbol b',\beta)\) still has
ordinary order at least \(p\). Set \(\boldsymbol u=\boldsymbol b'-\boldsymbol b\).

The compared normalized tree factorial is a unit, since each
of the true order identities equals one. Thus for every
\(|\tau|\le p\) the actual unnormalized balance is
\[
  \boldsymbol u^\top\boldsymbol\Phi_\tau^{\rm old}
          +\beta\Phi_{\tau,\mathrm{new}}=0 .
\]
A root leaf mark multiplies the old derivatives by their actual
clocks \(C\) and the new derivative by \(z\). Subtract \(z\)
times the unmarked balance from the marked one for
\(|\tau|\le p-1\). This gives
\[
      \boldsymbol u^\top(C-zI)\boldsymbol\Phi_\tau^{\rm old}=0.
\]
The profile-span (or annihilator) assumption now implies
\(u_i c_i=z u_i\) on every old coordinate. Thus
\(u_i c_i^k=z^k u_i\) by induction at every nonnegative degree.
The true leaf balance \(\sum_i u_i+\beta=0\) then gives
\[
          \sum_i u_i c_i^k+\beta z^k=0
\]
at **all** degrees. In particular a next bush defect cannot
be repaired by the unchanged-prefix single-row extension.
This proof does not divide by \(\beta\) and remains valid
when it vanishes or is a zero divisor.

Over a field, if \(\beta=0\), the old weights are unchanged by
the same span argument. If \(\beta\ne0\), put
\(\boldsymbol\ell=-\boldsymbol u/\beta\). It is supported only at
old coordinates with clock \(z\), and has coefficient sum one.
An ordinary unary mark also gives
\(\boldsymbol a^\top=\boldsymbol\ell^\top A\) on the full old span.
So the possible physical new row is an affine combination of
old rows at that same clock.

## Exact application to the fourteen-stage seed

For this fixture \(p=9\). Its actual trees of size at most eight
include fourteen independent profile vectors. The selected
(size, zero-based index in root-child multiset enumeration) list is

    (1,0) (2,0) (3,0) (3,1) (4,0) (4,2) (5,0)
    (5,5) (5,7) (6,0) (6,5) (6,11) (7,28) (8,95)

The independent rational elimination obtains determinant
\[
   -\frac{699914663248933}{613702752390000000000000000000000000000},
\]
which reduces to \(5\bmod29\); the full list of rooted shapes and
literal residue matrix are recorded in [exact audit](exact-audit.txt).
The same replay checks all 486 ordinary rooted conditions through
nine and the tenth-order bush normalized defect \(-1/2160\).
Thus this bush defect is unchanged by every one-row extension that
preserves order nine. No vector weights are assumed positive.

## Replay

    python -B audit.py
    # From the repository root: sha256sum -c ai-generated/research/erk9-fourteen-one-row-extension/sources.sha256

The rank/determinant and 486 checks use only exact standard-library
rational arithmetic. No Lean verification of the literal rank or of the general argument is claimed in this note.
