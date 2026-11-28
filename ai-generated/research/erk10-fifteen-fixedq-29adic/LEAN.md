# Kernel certificate for the fixed modulus 29^11

This certificate checks the separate, already-published
[fixed-modulus literal](lift29p11.json) at modulus
\(29^{11}=12200509765705829\). No hypothesis about a Hensel point
or an algebraic parameter remains in this certificate. The actual
eleven-vertex bush gives normalized value \(3554644188177161\),
hence unit defect \(3554644188177160\) with modular inverse
\(9738106248624930\).

The six audited endpoints are in namespace
**RKResearch.Certified.ERK10FifteenZ29Pow11**. In particular,
**exact_zmod** is the actual strict-triangular order-ten endpoint
over \(\mathbb Z/29^{11}\), **physical_failure_unit** proves the
failure is a unit, and **exact_of_char_dvd** gives a 15-stage
strictly explicit method of exact order ten over any nontrivial
commutative ring whose positive characteristic divides \(29^{11}\).
This includes characteristic \(29^k\) for each \(1\le k\le 11\) by reduction.
The same literal therefore suffices for all these exponents; no
separate kernel replay is needed at the smaller moduli.

The [arbitrary-power result](README.md) still uses its separate
mathematical proof. This Lean certificate does not claim to cover
exponents above 11, the 29-adic point, or arbitrary characteristic
zero coefficients.

The [same generator and proof templates](../erk10-fifteen-fixedq-f29/LEAN.md)
check these coefficients using natural reductions, without
constructing a Fin enumeration of the coefficient ring.
Lean/Mathlib 4.36.0 results are in [the axiom audit](lean-4.36-audit.txt).
A full dependency build on the other versions is not claimed.

From the repository root:

    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.ERK10FifteenZ29Pow11:olean

To regenerate from this research directory into an existing empty
directory:

    python3 -B ../erk10-fifteen-fixedq-f29/generate_native.py \
      --source lift29p11.json --emit /tmp/erk10-29pow11-regen \
      --modules /tmp/erk10-29pow11-modules.txt

From the repository root:

    sha256sum -c ai-generated/research/erk10-fifteen-fixedq-29adic/native-sha256.txt
