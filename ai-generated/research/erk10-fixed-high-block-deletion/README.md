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

The separate Lean module ERK10TerminalBlockPolynomial verifies
the reusable rooted-order invariant and its nonzero last
contribution contradiction, with \(P,Q\) scaled by \(6^2,6^5\).
The identification with the particular half-port family is the
above mathematical argument and exact arithmetic receipt.
