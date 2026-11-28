# Native certificate of the first rational sixteen-stage tableau

The literal tableau is unchanged. Its denominator-cleared
integer profiles, actions, joins, moments and two order-eleven
discrepancies are checked by the Lean kernel. This is an
ordinary rooted-tree HasOrder theorem, not a decimal check or
an external solver assertion.

End points in RKResearch.Certified.ERK10RationalSixteen:

* order_ten: actual HasOrder 10 for the scaled literal coefficients
  over any commutative ring supplying an inverse of D.
* exists_exact_of_unit: sixteen strict explicit rows of exact order
  ten over any nontrivial commutative ring with D a unit. The two
  next-tree numerators have a verified integer Bézout combination.
* exists_exact_rat: the exact rational specialization.

All 115 source modules are listed in native-modules.txt.
The fixed native order cover checks 488 distinct normalized stage
profiles, 221 actions and 985 joins, with all output moments.
The big integers are inputs to untrusted generation only; their
arithmetic is checked using kernel reduction with no compiler axiom.
The recorded build is Lean / Mathlib 4.36.0. No other release was
measured for this packet.

From ai-generated/lean:

    lake build +RKCert.ReviewedNative.ERK10RationalSixteen:olean

From this research directory, verify the exact source/literal manifest:

    sha256sum -c native-sha256.txt

To regenerate the numeric modules into an existing scratch directory:

    python3 -B generate_lean.py --source tableau.json --emit /tmp/rk-q16 \
      --modules /tmp/rk-q16-modules.txt

The checked Core and Next, and the final endpoint, are small separate
consumers; the generator emits the data and arithmetic shards.
