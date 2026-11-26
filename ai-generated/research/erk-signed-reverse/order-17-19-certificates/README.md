# Exact finite checks for the 53-stage and 66-stage explicit methods

The two receipts certify the published explicit Runge–Kutta constructions at orders 17 and 19 for coefficients in a nonzero commutative ring in which the respective order factorial is a unit. They do not change the stage counts. The structural argument is described in the [order-15 certificate](../order-15-certificate/README.md) and the [construction notes](../README.md). These finite checks use exact arithmetic, not Lean.

The checker verifies the finite forward identities used in the induction on rooted sums and extensions, and the closure identities for the two operations on the dual test vectors. It checks all denominators against powers of the order factorial. It then checks equality with the published tableau and combines two literal next-order defects to give 1. This final identity certifies exact order even when the next integer is not a unit. Only those two next-order trees are evaluated directly.

| Order | Physical stages | Virtual rows | Row aliases | Forward attachments | Dual transitions |
|---:|---:|---:|---:|---:|---:|
| 17 | 53 | 82 | 29 | 394 | 66 |
| 19 | 66 | 106 | 40 | 394 | 140 |

At order 19, the reverse residual polynomial vanishes at both endpoints and has zero mean. In the centered coordinate, write it as (1 − v²) times a polynomial of degree at most six. Its constant coefficient is determined by its other six coefficients because the mean of 1 − v² is 2/3, a unit. The checker uses a fixed interpolation map on nine actual reverse rows to verify these statements on the same dual basis used in the order proof. It checks that this map takes the two actual dual operations to multiplication by the reverse clock's complement and integration from zero. It then checks both endpoint reads and the mean on all 27 top-degree basis columns. This verification neither assumes the fitted mean nor needs a second span of test vectors.

Reproduce both receipts from this directory with Python 3.10 or later, without the optimization flag:

```sh
python3 check.py 17 receipt-17.json ..
python3 check.py 19 receipt-19.json ..
```
