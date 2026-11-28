# An étale coefficient cover and henselian-local specializations

The [all-primes cancellation proof](README.md) can be strengthened
from a faithfully flat finitely presented coefficient extension to
a faithfully flat **étale** one. It also extends the construction
to henselian local rings with appropriate residue roots, even when
their characteristic is zero and they are not complete.

Put \(S=\mathbb Z[1/10!]\), and use the same radicals and source
denominator \(D\) as in the main proof. Consider the finite free
rank-eight \(S\)-algebra
\[
 A_0=S[X,Y,Z]/(X^2-3,Y^2-7,Z^2-147-42Y).
\]
Each quadratic step is finite étale: \(2X\) and \(2Y\) are units
in the first two extensions, and \(2Z\) is a unit in the last since
\((147+42Y)(147-42Y)=21^3\). This last identity is checked
in the [portable scalar module](../../lean/RKCert/ReviewedNative/ERK10StepanovDomainScalars.lean).
The generic fiber is the degree-eight field from the main proof;
freeness embeds \(A_0\) in that field. Thus \(A_0\) is a domain.
At a prime \(\mathfrak p\) over an admissible \((p)\) its local
ring is a DVR with uniformizer \(p\): it is a normal one-dimensional
étale local extension, and its quotient by \(p\) is its residue
field.

## The cover

The open \(A_0[1/D]\) carries the literal tableau and covers
every base prime not dividing \(D\), as well as the generic point.
For each admissible \(p\mid D\) choose the verified integral branch
in the main proof and let \(\mathfrak p\) be the prime of \(A_0\)
defined by its residue. The corresponding field embedding into the
unramified local fraction field preserves the valuation normalized
by \(v(p)=1\): elements of \(A_{0,\mathfrak p}\) outside its
maximal ideal map to units, and \(p\) is a uniformizer on both sides.
The exact numerator cancellation therefore puts every actual
tableau entry in \(A_{0,\mathfrak p}\), not just in a completed
integer ring. Writing these finitely many fractions in the
localization, choose their product denominator \(s_p\notin\mathfrak p\).
Then \(A_0[1/s_p]\) carries the same tableau and has a prime over
\(p\).

The finite product of the \(A_0[1/D]\) factor and these at most
17 additional principal-open rings is étale and finitely presented
over \(S\). Its spectrum surjects onto \(\operatorname{Spec} S\),
so it is faithfully flat. Each ordinary order identity holds by
injection into the generic field in each factor, hence also in the
product. The failed order-eleven bush is a unit in every factor.
Base changing this algebra gives an étale faithfully flat
coefficient extension carrying an exact 15-stage tableau for every
nonzero commutative ring in which \(10!\) is a unit. The extension
is not asserted to be finite as a module. No descent to the base
ring is asserted.

## Henselian local rings

Let \(R\) be a nonzero henselian local ring in which \(10!\) is a
unit, with residue field \(k\). If \(k\) admits the verified
radical branch at its characteristic, the simple-root Hensel
property applied in sequence produces the same residue branch in
\(R\). In the good-prime case \(D\) is a unit in \(R\), so
the map factors through \(A_0[1/D]\). In a bad-prime case the chosen
\(s_p\) has nonzero residue, so it is a unit in \(R\) and the map
factors through \(A_0[1/s_p]\). This argument does **not** divide by
\(p\) in \(R\); even if \(p\) is a zero divisor, it uses only a
denominator with unit residue. The next-bush defect is an \(S\)-unit
and remains nonzero.

In particular this covers residue fields containing
\(\mathbb F_{p^4}\) at every \(p>7\), the prime residues from the
61 verified scalar cases without extra residue degree, and at 523
any residue field containing \(\mathbb F_{523^2}\). For residue
characteristic zero, any compatible three simple radical roots in
\(k\) suffice, e.g. when \(k\) is algebraically closed. The
[independent 17-adic family](../erk10-fifteen-17-power/LOCAL-AND-ALGEBRAIC.md)
also covers every henselian local ring of residue characteristic 17,
without any extension of its residue field.

These are mathematical consequences of the existing literal and
cancellation certificates, not new native geometry or Hensel theorems
in Lean. The stage interval over the factorial localization and the
real interval are unchanged.
