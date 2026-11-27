# The eleven-stage SDIRK8 witness over the 31-adic integers and every Z/31^k

The [literal F31 tableau](../sdirk-eight-f31-upper/README.md) lifts to an eleven-stage strict SDIRK method of **exact order eight** over the 31-adic integers $\mathbb Z_{31}$, and over $\mathbb Z/31^k$ for every $k\ge1$. The diagonal and the specific order-nine bush discrepancy are units. This is an upper bound, not a determination of the stage minimum in these rings. The exact characteristic-zero coefficient field of this literal donor has degree 12 over $\mathbb Q$; that does not assert that all eleven-stage SDIRK8 methods require degree 12.

## The same characteristic-zero scalar tower, not a conjectural lift from residues

First use the archived [literal real theorem and field description](../../upper-bounds/real-algebraic/sdirk11_order8_literal_coefficient_field_20261125.md). Its parameters $s,t,c$ satisfy the monic equations
$$
 s^3-9s^2+18s-6=0,\qquad
 t^2-(s+3)t+s=0,\qquad c^2+\beta_1(s,t)c+\beta_0(s,t)=0.
$$
For the last equation, $a=(1+s)/2$, $z=a+s$, and the four moments $\mu_j$ are the average of $X^j(X-a)(X-s)(X-t)(X-1)$ on $[0,z]$ for $0\le j\le3$. With $D=\mu_0\mu_2-\mu_1^2$ the coefficients are
$$
 \beta_0=(\mu_1\mu_3-\mu_2^2)/D,\qquad
 \beta_1=(\mu_1\mu_2-\mu_0\mu_3)/D .
$$
The characteristic-zero theorem applies to a particular real branch. The following irreducibility receipts show why the branch used at 31 has the **same** algebraic identities, even if the ordering choices for the real root are different.

1. The monic cubic is Eisenstein at 3, hence defines the degree-three field $K_1=\mathbb Q(s)$.
2. Its simple root $s=7\bmod11$ (derivative $6$) lifts and defines an embedding of $K_1$ into $\mathbb Q_{11}$. The discriminant of the second polynomial reduces to $(7+3)^2-4\cdot7=6\bmod11$, a nonzero nonsquare. If it were a square in $K_1$, its image in $\mathbb Q_{11}$ would be a unit square, and the square root would also have valuation zero and reduce to a square. This is impossible. Thus $K_2=K_1(t)$ has degree two over $K_1$.
3. At the simple roots $s=9,t=7\bmod13$ the two derivatives are $8,2$. Successive lifts give an embedding of $K_2$ into $\mathbb Q_{13}$. The moment pivots reduce to $z=1,D=7$, and $(\beta_0,\beta_1)=(8,12)$. Therefore $\beta_1^2-4\beta_0=8\bmod13$, again a nonzero nonsquare. The same unit argument shows $K_3=K_2(c)$ has degree two over $K_2$.

The full tower is a field of degree 12. The real witness gives an injective evaluation of this abstract tower at its ordered real roots. Every literal tableau coefficient is an element of $K_3$, including the fourth calibrated clock $d=-E(0)/(E(1)-E(0))$. Every rooted identity verified for the real witness is therefore an identity in $K_3$ itself. In fact the field of the real tableau coefficients is **equal** to $K_3$: from the retained literal rows, the physical second clock is $\gamma(1+s)/2$, the fifth is $1-\gamma c$, and the eighth is $1-\gamma t$. The original deletion and column merge preserve the retained row sums. With the common nonzero diagonal $\gamma$, these three clocks recover $s,c,t$.

## Unit ingress at 31 and order transport

At $s=11,t=17,c=4\bmod31$ the roots are simple with derivatives $28,20,27$ in the order of the tower. The moment pivots reduce to $z=17,D=4$, and $(\beta_0,\beta_1)=(1,19)$. Therefore lift $s$, then $t$, then $c$ in $\mathbb Z_{31}$, using the lifted coefficients at each step. The defining polynomials are monic with integral coefficients at each step, so the simple-root Hensel argument applies. This gives an injective map $K_3\longrightarrow\mathbb Q_{31}$ by the field properties above.

For the chosen branch the literal computations of normalization, calibration, the two old projection pivots, the normalized cardinal denominators, the cleaned cubic denominator, quadrature weights used in divisions, split masses, and all scalar taps divide only by units. The exact source `lift_assembly.py` executes those divisions in $\mathbb Z/31$ without a total inverse or a branch fallback. `audit_units.py` independently checks every executed quotient denominator of that straight-line assembly, including those in the repeated cardinal and linear-operator evaluations. At modulus 31 the assembly matches the independently checked literal F31 matrix. Hence by induction through its arithmetic operations every denominator of the same lifted expression in $\mathbb Z_{31}$ is a unit (earlier operations and their lifts commute with reduction). The simple-root derivative checks cover the additional quotients in the Hensel iterations.

The injective field transport proves the actual order identities over $\mathbb Q_{31}$. Since all coefficients are integral and the proof compares ring order polynomials, the identities hold in $\mathbb Z_{31}$ as well and survive every reduction. The ninth bush equals $2\bmod31$ rather than $1/9=7\bmod31$, so that discrepancy stays a unit in the integral lift and every quotient. Strict lower triangularity is the same structural identity in the field and over its specializations, and the diagonal reduces to 11, so it stays a unit. In particular this theorem is **not** inferred just from the finite-power ledgers. Unital coefficient transport gives the same exact-order upper bound over any nonzero commutative ring of characteristic $31^k$.

## Coordinate and rooted-condition checks

The independent modular assembly checks all 200 rooted conditions and the next-order bush at the following powers:

| $k$ | Parameters $(s,t,c,d)$ at $31^k$ | Common diagonal | Ninth bush |
|---:|---|---:|---:|
| 1 | $(11,17,4,2)$ | 11 | 2 |
| 2 | $(476,482,903,715)$ | 538 | 684 |
| 4 | $(368539,554018,423743,277483)$ | 154298 | 67954 |
| 12 | $(132584873773010642,616586144953191650,124879865995716443,372498782144107381)$ | 380959222376850997 | 136392995481201423 |

The literal $k=2$ tableau is also recorded as `mod961.json` and `RKCert.Research.SDIRKEightEleven31Lift`. Its order-nine scaled condition is $390\ne1\bmod961$, and the diagonal is $538$ with inverse $234$. The Lean module kernel-checks its triangularity, unit diagonal, and next-order failure, plus the two small nonsquare guards and simple 31-adic root ingress. The 200 order identities modulo 961 are checked by the exact modular assembly and also follow from the all-power transport proof; unlike the adjacent F31 witness this packet does not claim a native all-tree Lean theorem at modulus 961. The rational tower irreducibility, p-adic existence and all-power transport are the mathematical proof above, not claimed as a native Lean Hensel theorem.

Use Python-flint 0.8 and run `python check_scalars.py`, `python audit_units.py`, and `python lift_assembly.py` from this packet. They use the adjacent F31 packet for the shared rooted tree enumeration and exact original data match.
