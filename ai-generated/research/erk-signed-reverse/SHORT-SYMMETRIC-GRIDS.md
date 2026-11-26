# Shorter scalar grids for orders eleven through twenty

The signed reverse construction gives the following exact explicit Runge–Kutta methods with coefficients in any nonzero commutative ring in which \(p!\) is a unit. Use the [eight-row reverse chart](SHARP-PAID-ERK-GRADE-FIVE.md) at order eleven, and the charts in the [main construction](CONSTRUCTION.md), [the shorter grade-seven chart](SHORT-GRADE-SEVEN.md), and [the additional row identities](ADDITIONAL-ROW-MERGES.md) at the later orders.

## Why the shorter rule preserves order

At odd order \(p\), ordinary interpolation on \(p\) distinct scalar sites integrates all polynomials of degree at most \(p-1\). At even order \(p\), use \(p-1\) sites symmetric about one-half. Interpolation integrates degree at most \(p-2\). The rule is symmetric because the weight of each site equals that of its reflection: their cardinal polynomials have equal integrals. Thus the rule and the exact integral both vanish on \((x-\tfrac12)^{p-1}\), and the rule integrates degree \(p-1\) as well. The weights are computed by integrating the cardinal polynomials, whose denominators are products of unit differences. The remaining moment denominators are at most \(p\).

The proof in the main construction uses only scalar exactness through degree \(p-1\) to verify the rooted conditions through order \(p\). In particular, it pairs a rooted error and a reverse word only after checking that the product has degree at most \(p-1\). The same proof therefore applies with these shorter rules. There are enough sites to include every reverse clock, so the negative donor copies merge with the pure rows exactly as before. No inverse of a scalar weight is needed.

## The literal choices

Each list of omissions is removed before dividing. A symmetric list uses both signs.

| Order | Forward and reverse chart sizes | Reverse sites | Final rows |
|---:|:---:|:---|---:|
| 11 | 9, 8 | \(0,\ldots,12\) divided by 12, omitting 1 and 11 | 25 |
| 12 | 9, 11 | \(0,\ldots,12\) divided by 12, omitting 1 and 11 | 28 |
| 13 | 11, 11 | \(0,\ldots,12\) divided by 12 | 33 |
| 14 | 11, 15 | \(0,\ldots,18\) divided by 18, omitting 1, 2, 4, 14, 16, 17 | 37 |
| 15 | 15, 15 | \(0,\ldots,18\) divided by 18, omitting 1, 2, 16, 17 | 44 |
| 16 | 22, 15 | Same as order 15 | 50 |
| 17 | 27, 15 | \(0,\ldots,18\) divided by 18, omitting 1 and 17 | 57 |
| 18 | 27, 22 | \((6+j)/12\), \(j=0,\pm1,\pm2,\pm3,\pm4,\pm5,\pm6,\pm8,\pm12\) | 64 |
| 19 | 27, 27 | \((6+j)/12\), \(j=0,\pm1,\pm2,\pm3,\pm4,\pm5,\pm6,\pm7,\pm8,\pm12\) | 71 |
| 20 | 34, 27 | Same as order 19 | 79 |

The constructor checks that the grids contain all true reverse clocks, that their differences are units, and that all actual coefficients are in the required ring. The origin merges at every order. The pure endpoint also merges at orders 11–14 and 16–19 because their forward charts prescribe the old zeroth moment on arbitrary data. At orders 11 and 12 the pure midpoint is identical to the ninth forward row. Orders 15 and 20 do not use an extra pure endpoint or midpoint merge.

## Why the order is exact

It is no longer necessary to force the highest scalar moment to be zero. For each literal tableau, the corresponding witness file gives one or two trees of size \(p+1\) and their defects in the order conditions \(t!\,\mathbf b\cdot\boldsymbol\Phi_t(A)=1\).

The integer verifier recomputes the defects. Their denominators are units. After removing the prime factors already inverted in \(p!\), the greatest common divisor of their numerators is one. Bézout's identity then gives a linear combination equal to one in \(\mathbb Z[1/p!]\). Consequently the defects cannot all be zero after any nonzero commutative base change. This proves exact order \(p\), including when \(p+1\) is not invertible.

For orders 11–14 the verifier also replays every rooted condition through the target order. For orders 15–20 the full order proof is the symbolic argument and the verifier checks a sample as a second check.
