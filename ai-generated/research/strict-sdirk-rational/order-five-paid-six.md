# Six stages attain exact strict SDIRK order five over every paid ring

A single tableau over \(\mathbb Z[1/30]\) improves the uniform upper bound to **six** physical stages, including for nonlocal rings. Together with the existing [universal floor](../../lean/RKCert/ReviewedNative/NonsingularDIRKStageFloor.lean), this puts the minimum in \([5,6]\) over arbitrary nontrivial commutative rings with \(30\) a unit. Five is already [sharp over local rings](order-five-paid-local.md). If 30 is not a unit, the fifth tall-tree condition rules out order five at any stage count. Lean checks both this necessity and sufficiency at six stages. No stability is claimed.

The common diagonal of \(A\) is \(1/4\); all omitted entries are zero.

| Row | Lower-triangular entries of \(A\) |
|---:|---|
| 1 | \(1/4\) |
| 2 | \(-1,1/4\) |
| 3 | \(-3/16,-1/16,1/4\) |
| 4 | \(17/128,17/384,7/96,1/4\) |
| 5 | \(1107/4000,209/4000,21/1000,0,1/4\) |
| 6 | \(345/1024,35/1024,0,27/64,-75/256,1/4\) |

The weights and clocks are
\[
\mathbf b=(0,0,7/54,2,-125/54,32/27),\qquad
\mathbf c=(1/4,-3/4,0,1/2,3/5,3/4).
\]
Here both \(A\) and \(\mathbf b\) use the integer scale \(D=3456000\), which divides \(30^{10}\). The [native Lean proof](../../lean/RKCert/ReviewedNative/SDIRKFivePaidSix.lean) checks the full integer-scaled rooted-tree recursion \(\boldsymbol{\Phi}_t(A)\) and maps the numerator identities wherever \(D\) is a unit. It neither maps from \(\mathbb Q\) nor assumes an integral domain. The two order-six cleared discrepancies are \(11/64\) on the tall tree and \(-7/400\) on the bush. Multiplying by \(128\) and \(1200\), respectively, and adding gives \(1\). Thus at least one of these conditions fails in every target nonzero ring, even when one individual discrepancy vanishes.

## How the new splice was found

In the [two-donor chart](order-five-six-stage-splice.md), use the same two-stage core construction at \(\gamma=1/4\) and the second core clock \(-3/4\). The four centered output sites \((-1,0,1/5,1/2)\) were obtained by retaining \((-1,0,1/2)\) from the five-site Boole rule and completing one vanishing hull moment. Their interpolatory weights pay degree four, with all denominators in \(\mathbb Z[1/30]\).

The six strict-lower suffix entries satisfy three weighted column conditions and the chart's two linear order-five tests. Fix the remaining entry to obtain an integral solution after inverting only \(2,3,5\), then reconstruct the core-to-suffix feed by affine interpolation. The supplied exact proof verifies the resulting literal tableau rather than assuming that the chart search was exhaustive or that arbitrary rational chart solutions have the same denominator property.

The [independent checker](verify-order-five-paid-six.py) uses exact rational arithmetic on the 17 unordered rooted trees through order five and tests both sixth-order discrepancies.
