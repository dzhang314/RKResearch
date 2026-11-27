# A polynomial obstruction to fixed-high-block ERK10 deletion

This rules out a specific 17-to-16 shortening, not all 16-stage
ERK methods. Start with any member of the
[paid seventeen-stage half-port family](../erk10-seventeen-half-port-family/).
Delete its last row at clock one. Keep each surviving clock and
the surviving high-high block (zero-based rows and columns 9 to 15).
Every other matrix coefficient can change, subject to explicit
chronology and those same clocks. Every surviving output weight
can also change. Over any nontrivial commutative ring in which
\(10!\) is a unit, the resulting tableau cannot have order ten.
No assumptions about low-grade preservation or parameter values
are made.

Use the two scalar polynomials
\[
    P(X)=(X-1/3)(X-2/3),\qquad
    Q(X)=X(X-1/3)(X-1/2)(X-2/3)(X-1).
\]
Ordinary rooted conditions through nine fix
\[
    \boldsymbol b\cdot
    \bigl(P(\boldsymbol c)\odot A Q(\boldsymbol c)\bigr).
\]
Indeed its expansion uses only
\(\boldsymbol b\cdot(\boldsymbol c^{\odot j}\odot
A\boldsymbol c^{\odot k})\), where \(0\le j\le2\) and \(1\le k\le5\).
These are the derivatives at the root with \(j\) leaf children and
one \((k+1)\)-vertex bush child. The order is \(j+k+2\le9\),
and the tree factorial \((j+k+2)(k+1)\) is a paid unit.

Both the original and candidate scalar moment equations through
degree nine determine every aggregate scalar weight: cardinal
polynomials on the ten sites \(j/6\), \(-3\le j\le6\), are paid
because all site gaps are units. This determines each surviving
high weight individually except for the two high clocks 1/3
and 2/3, which are shared with the prefix. Both of those clocks
are zeros of \(P\). All nine prefix clocks are zeros of \(Q\).
Strict chronology therefore eliminates the prefix rows from the
observation, regardless of changes to their incoming coefficients,
and \(Q\) eliminates all contributions of the cross block to the
high rows. The surviving high-high block is unchanged, so the
whole change in the fixed observation would have to be the loss
of the last row.

The last row of every reference family member has weight \(7/150\),
\(P(1)=2/9\), and its read on \(Q(\boldsymbol c)\) is \(-10/441\).
The affine parameter directions vanish in this last read. The
lost contribution is therefore \(-2/8505\), a unit in the paid
ring. This is a contradiction. A successful 16-stage shortening
with these clocks must change part of the surviving high-high
block seen by the mixed moment, rather than merely redirecting
the entire terminal row into the original prefix.

The independent arithmetic replay checks the actual clocks,
which output masses can vary, all required paid node gaps, and
the last read and its two affine directions. This is not an
exhaustive numerical search.

    python3 -B audit.py
    sha256sum -c sha256.txt

## Lean evidence

`RKCert.ReviewedNative.ERK10TerminalBlockPolynomial` verifies the
mixed rooted-order invariant, with \(P,Q\) scaled by \(6^2,6^5\).
`RKCert.ReviewedNative.ERK10TerminalBlockClockAdapter.no_fixed_block_compensation`
checks the actual 17-entry clock pattern and proves that any two
literal explicit order-ten systems with these clocks and the
same surviving high-high block cannot differ by deleting the
last output, provided the reference's scaled last read is
\(-2304/35\). The zero-output last row is chronological padding
of the candidate and cannot affect earlier rows. The cardinal
polynomials, the units used to recover the surviving weights,
and the polynomial evaluation on the clock pattern are checked
over arbitrary paid rings, not over a field.

`RKCert.ReviewedNative.ERK10TerminalBlockHalfPort.affine_terminal`
instantiates the last read for the actual half-port reference
matrix and both integer-scaled affine directions, for arbitrary
parameter values. Its companion `family_explicit` and
`family_clock` check strictness and the literal clocks.
`no_half_port_family_fixed_block` therefore excludes the
compensation for every such reference of order ten. The
central member's order is already kernel-certified in
`ERK10UniversalSeventeen`; `no_half_port_literal_fixed_block`
discharges that reference-order hypothesis. For other family
members, the reference order is supplied by the separate
[familial tensor-grid replay](../erk10-seventeen-half-port-family/README.md),
not by this Lean packet. The arithmetic replay also verifies
that the native coefficient arrays are the two published
affine directions.

    cd ../../lean
    lake build +RKCert.ReviewedNative.ERK10TerminalBlockPolynomial:olean \
      +RKCert.ReviewedNative.ERK10TerminalBlockClockAdapter:olean \
      +RKCert.ReviewedNative.ERK10TerminalBlockHalfPort:olean

Checked on Lean 4.36.0, with standard axioms only.
