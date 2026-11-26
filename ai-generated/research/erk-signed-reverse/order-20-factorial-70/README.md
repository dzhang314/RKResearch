# An exact 70-stage explicit method of order twenty

The tableau has exact order 20 with coefficients in any nonzero commutative ring in which 20! is a unit. It improves the previous factorial-unit upper bound of 71. No inverse of 21 or additional primes is required.

## Construction

Use the previous 27-row forward chart and retain 25 of the 27 reverse donor rows, omitting the parallel primitives at centered clocks ±1/2. In the previous centered scalar grid, written as integer labels divided by 6, remove the labels 8 and −7 and insert 9, 10, and 13. The 20 distinct scalar nodes integrate polynomials through degree 19 by cardinal interpolation. All pairwise node differences are units in the coefficient ring. Among the 11 live sites, no unpaid prime kills two weights.

The lower reverse decoder captures all words through length eight. Seven higher reads pin the remaining directions except for two polynomial modes. Five early weighted sites recover those two modes. The six later live sites introduce polynomial corrections that agree with the negative primitive error on the early sites. Two extra compensation identities for each mode allow the signed late rows to remove the intermediate defect without adding a physical stage. At the top grade the 11 weighted measurements recover eight polynomial directions and the two correction modes. The maximal minors generate the unit ideal; individual scalar masses need not be units.

The replay checks all rooted source and dual attachment identities needed for order 20. A source correction is first nonzero at child size 10. Through order 20 no rooted product can contain two such source corrections. The single error in each rooted contribution is therefore paid by the lower, intermediate, or top pairing. Exact scalar quadrature supplies the remaining output. The literal owner-fold equations verify equality of rows before combining their weights. Two of the scalar rows already occur in the 27-row forward chart, leaving 27 + 25 + 20 − 2 = 70 distinct rows.

Two actual size-21 order defects have an integer linear combination equal to one. This excludes order 21 after every nonzero allowed base change. The replay evaluates each witness on the folded literal and verifies both the unit combination and the factorial divisibilities. The earlier [71-stage construction](../order-20-factorial-71/README.md) remains available. This is exact arithmetic, not a Lean certificate.

## Reproduction

From this directory:

~~~sh
python -B replay.py .. \\
  --prior-receipt ../order-20-factorial-71/receipt-20-factorial-71.json
out=$(mktemp)
python -B replay.py .. \\
  --prior-receipt ../order-20-factorial-71/receipt-20-factorial-71.json \\
  --emit-literal > "$out"
cmp tableau-20-factorial-70.json "$out"
~~~

The standard-library replay checks the input hashes, compares the old forward and retained reverse charts to the earlier structural receipt, verifies 7,910 owner-fold entries and the finite rooted identities, and requires the reproduced literal to match SHA-256 `172b4074ca84dc5546907eacc434780a980662b1bfaa51c99e6b43ecab2e5e44`.
