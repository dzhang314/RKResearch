# Six stages are sharp in characteristics 11 and 17

The common-diagonal stage floor for order six is six over every nontrivial commutative ring. The characteristic-zero floor is seven. Previously the finite-characteristic six-stage example here was over the field of size 163; 11 and 17 divided the published sufficient obstruction product but were not classified by it. We give exact six-stage witnesses for both. This does **not** change a characteristic-zero or ordered-field bound.

| Coefficient ring | Common diagonal | Output weights | Cleared seventh bush |
|---|---:|---|---:|
| Z/11 | 4 | 0, 0, 0, 7, 9, 7 | 9 |
| Z/17 | 8 | 0, 0, 0, 5, 8, 5 | 16 |
| Z/187 | 59 | 0, 0, 0, 73, 42, 73 | 152 |

The last tableau simultaneously specializes to the first two. Its diagonal 59 has inverse 168, and the discrepancy 152 − 1 has inverse 161. Under every unital map from Z/187 to a nontrivial commutative ring, the diagonal remains a unit and the seventh bush still fails, even if the target has zero divisors. Thus six is the **minimum**, not only an upper bound, over every nontrivial commutative ring of characteristic 11, 17, or 187. These are squarefree characteristics; this argument does not lift the tableaux to characteristic 121 or 289.

**How the tables were found.** In the existing six-stage physical chart set z = γ⁻¹, B = zA, u = B₁₀ and v = z(c₅−c₄), with zero-based indices and physical abscissae c. The cubic terminal branch gives (z,u,v) = (3,4,6) modulo 11 and (15,10,15) modulo 17. For each remaining row, fix its normalized clock x. Write m = Bx and q = 2m−x² as stage vectors. Row sum, the chart's clock and shifted-Legendre equations, and Bm + x·m − 2B(x²) = 0 are linear equations for the earlier entries of that row. (The last identity expands the commutator equation.) Solving those equations and testing the resulting order conditions found the literal tables above. Correctness does not depend on the search being exhaustive or on the necessary chart equations being sufficient.

The [Lean module](../../lean/RKCert/ReviewedNative/SDIRKSixChar11and17.lean) contains the literal CRT coefficients, the native `HasOrder` certificate using `decide +kernel`, the failed seventh condition and the general ring transport. Combining this with the [existing universal six-stage lower bound](../../lean/RKCert/ReviewedNative/SDIRKSixFourConstantEndpoint.lean) gives sharpness. The [independent Python checker](check11and17.py) uses the 37 unordered rooted trees of orders 1–6, checks the seventh bush and verifies the two CRT reductions. The native Lean checker instead uses all 65 ordered representatives through order six.
