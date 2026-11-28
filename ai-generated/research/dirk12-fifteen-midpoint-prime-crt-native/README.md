# Native width-fifteen DIRK certificate for two prime-power families

The two published prime-field literals with parameters
\((x,f,d)=(111,57,85)\) at 131 and \((103,41,106)\) at 149 lift to
the specified literals modulo \(131^{20}\) and \(149^{20}\). The
generator checks both prime reductions against every original entry
in \(A,\mathbf b,\mathbf c\), then combines corresponding entries
and low-band receipts by CRT into one literal over
\(\mathbf Z/(131\cdot149)^{20}\mathbf Z\).

Lean verifies **all rooted conditions of order at most twelve** via
the low complementary-support conditions, that the tableau is lower
triangular, that its first diagonal entry is zero and its second is a
unit, and that its scaled order-thirteen bush defect is a unit. The
endpoint transfers the literal by the canonical residue map to any
commutative ring whose characteristic divides the combined modulus.
For every nonzero such ring it proves exact order twelve, and the
first two diagonal entries are distinct. It is not an explicit
method and not a common-diagonal method.

This is a finite native certificate through the twentieth powers. The
separate mathematical Hensel argument for arbitrary exponents and
the characteristic-zero real tableau are not native conclusions of
this packet. The exact arithmetic of the supplied width-fifteen
literal is independent of that argument.

Rebuild the 19.6 kB data file by running generate-crt.py with three
arguments: the repository's ai-generated/research directory, the
DIRK12MidpointPrimeCRTData.lean output path, and the exponent 20.
The generator uses the already archived real constructor and tower
data to obtain the chosen residues; the kernel replay does not rely
on their Hensel justification or on the generator's Gaussian solves.

Build order in RKCert/ReviewedNative: DualSupport12,
DualSupport12VectorReplay, DIRK12MidpointPrimeCRTData,
DIRK12MidpointPrimeCRTChecks, DIRK12MidpointPrimeCRT. Then run
AuditDIRK12MidpointPrimeCRT.lean. The attached receipt is Lean 4.36.0
with its matched Mathlib. There are no bespoke axioms or native
compiler-reduction assumptions.
