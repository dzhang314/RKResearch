# Native width-15 characteristic-17 certificate

Lean checks the exact already-published finite-field coefficients,
not an abstract geometrical witness or the higher-power family.
The checked endpoints are
RKResearch.Certified.ERK10FifteenF17.order_ten,
RKResearch.Certified.ERK10FifteenF17.exact_f17, and
RKResearch.Certified.ERK10FifteenF17.exact_of_char17.
The last theorem transfers the same 15-stage tableau to every
nontrivial commutative ring of characteristic exactly 17 by the
injective canonical coefficient map. The separately published
17-power construction at larger characteristic is mathematical.

The checker groups 732 normalized rooted profiles by grade and
value. Lean's kernel checks 324 ordinary recurrence actions
and 1,462 joins, and the normalized output values. The generic
forest-factorial proof applies the checked coverage to every
reviewed actual rooted tree. The actual eleventh bush
has normalized value 9, not 1. The dependency and evaluation
receipts use kernel reduction, not an unchecked native executable
equality. Lean/Mathlib 4.36.0 reported only standard axioms for
all three endpoints in [the exact native audit](lean-4.36-audit.txt).
No four-release dependency build is claimed for this certificate.

From the adjacent Lean development:

    cd ../../lean
    lake build +RKCert.ReviewedNative.ERK10FifteenF17:olean

From this directory the untrusted cache generator reproduces each
generated module byte-for-byte from the literal:

    python3 -B generate_native.py --emit /tmp/erk10-fifteen-regen \
      --modules /tmp/erk10-fifteen-modules.txt
    sha256sum -c native-sha256.txt

Create the empty emit directory first. The hand-written Core
and endpoint files prove the connection of the receipt data to
the actual order predicate and are included in the native
manifest. The literal uses SHA-256
02a8c0ca3e5b11e9c851b237420d46ce798ea14fb727dc2e00e51b85fd1cedf9;
the native work does not replace it.
