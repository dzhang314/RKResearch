# Nine stages are optimal for explicit order seven over factorial-admissible rings

Let \(R\) be a nonzero commutative unital ring. If \(7!\) is a unit in \(R\), the literal nine-stage tableau below has **exact order seven**. Conversely any method satisfying the order-seven tall-tree equation requires \(7!\) to be a unit. In the admissible case the [existing uniform explicit lower bound](../../lean/RKCert/ReviewedNative/ERKUniform.lean) rules out eight or fewer stages over these same rings, so **the minimum is nine**. This replaces the earlier [universal ten-stage witness](../erk-seven-ring-witness/README.md) and closes its one-stage gap. No additional prime, field property or ordering is needed.

## Tableau

Each row of \(A\) lists its entries in chronological predecessor order; all later columns are zero.

| Stage | Strict predecessor coefficients |
|--:|:--|
| 1 | none |
| 2 | \(1/6\) |
| 3 | \(0,\ 1/3\) |
| 4 | \(1/8,\ 0,\ 3/8\) |
| 5 | \(1/8,\ 0,\ 3/16,\ -1/16\) |
| 6 | \(64,\ 0,\ 474,\ -88,\ -448\) |
| 7 | \(151/972,\ 0,\ 13/27,\ -28/243,\ -320/1701,\ -1/6804\) |
| 8 | \(23637/168070,\ 0,\ 114/343,\ -7492/84035,\ -52576/588245,\ -93/1176490,\ -729/84035\) |
| 9 | \(1169/900,\ 0,\ 13/5,\ 5204/675,\ -147136/1575,\ -13/18900,\ -2376/25,\ 4802/27\) |

\[
 b=(7/40,\ 0,\ 0,\ 328/135,\ -512/35,\ -1/7560,\ -729/40,\ 16807/540,\ 1/8).
\]
The clocks \(A{\bf1}\) are \(0,1/6,1/3,1/2,1/4,2,1/3,2/7,1\). In particular an internal clock is outside the unit interval, and stages 3 and 7 have the same clock but are genuinely different stages. No stability or positivity claim is made.

The common denominator \(11435482800=2^4 3^5 5^2 7^6\) divides \((7!)^6\). The eighth-order tree obtained by adding two successive unary roots above the six-vertex bush has tree factorial 336 and cleared defect \(1/12\). Thus the defect is a unit even in the presence of zero divisors, and it is nonzero in \(R\).

## Why this choice of clocks works

This is a redesign of an order-seven simplifying-assumption family, not a specialization of either pole-bearing classical tableau. Write \(A{\bf1}=c\) and \(C=\operatorname{diag}(c)\). Put \(b_2=b_3=0\), require column 2 to vanish below stage 3, and impose the exact primitive equations \(Ac^k=c^{k+1}/(k+1)\) on stages \(4,\ldots,9\) for \(k=0,1,2\). Write \((\alpha,\beta,\gamma,\delta,\epsilon)=(c_4,c_5,c_6,c_7,c_8)\), and \(c_2=\alpha/3,\ c_3=2\alpha/3,\ c_9=1\). Interpolate \(b\) on the seven active clocks to price degrees \(0,\ldots,6\).

The three prescribed output rows \(b^\top A,\ D=b^\top CA,\ E=b^\top C^2A\) integrate against the densities \(1-x,\ (1-x^2)/2,\ (1-x^3)/3\), through degrees 5, 4 and 3 respectively. Here \(b^\top A=b^\top(I-C)\); \(D_i=E_i=0\) at \(i=2,3,9\). Literal last-column support forces \(D_8=E_8=b_8(1-c_8)\) and \(E_7=(1+c_8)D_7-c_8 b_7(1-c_7)\). Interpolation supplies the remaining entries. After the initial five rows this leaves one free entry, \(a_{65}\), in the sixth row; the remaining rows are read off from the three prescribed output rows by a \(3\times3\) linear solve at the three last clocks (smaller at the very end).

Here is a way to reduce the two nontrivial remaining scalar equations before selecting a rational grid. Let \(h\) be quadratic with \(h(c_i)=D_i/b_i\) for \(i=7,8,9\), and \(U=D-b^\top h(C)\). Its support is on stages 1,4,5,6, and through polynomial degree four it integrates against \((1-x^2)/2-h(x)\). This density has the form \((1-x)\) times a linear polynomial. Put \(P=x(x-\alpha)(x-\beta)\) and write \(J\) for zero-constant integration. The three prescribed rows vanish at column 3, so \(D A{\bf e}_3=0\) is equivalent to \(UA{\bf e}_3=0\); it fixes \(a_{65}\) in the chosen chart. On every prefix stage charged by \(U\), one has \(AP(c)=P(c_3)A{\bf e}_3\), since the other earlier predecessors lie on roots of \(P\). Therefore the remaining condition \(DAc^3=1/140\) reduces to \(U(JP)(c)=0\). The support also gives \(U((x-\gamma)P)(c)=0\). These two scalar moments can be arranged by setting
\[
 \rho=\frac{\int_0^1 x(1-x)(JP)(x)\,dx}{\int_0^1(1-x)(JP)(x)\,dx},\qquad
 \gamma=\frac{\int_0^1 x(1-x)(x-\rho)P(x)\,dx}
               {\int_0^1(1-x)(x-\rho)P(x)\,dx}.
\]
In fact with \(\alpha=1/2,\beta=1/4\) these give \(\rho=5/7,\gamma=2\). Among the choices of remaining distinct rational sites, \(\delta=1/3,\epsilon=2/7\) leave only the permitted primes in every coefficient. The reconstruction has \(a_{65}=-448\). The reported tableau is certified against *all* rooted equations, so correctness does not depend on completeness of the simplifying ansatz.

## Verification

Run **python3 check.py** in this directory. The independent exact rational replay verifies the common denominator, all 85 conditions on unlabeled non-plane rooted trees through size seven, and the stated eighth-order unit defect. No numerical approximation or finite-field heuristic is used in the verification.

The [Lean certificate](../../lean/RKCert/ReviewedNative/ERK7FactorialNine.lean) checks all 197 reviewed constructor trees through size seven via the existing [finite enumeration](../../lean/RKCert/ReviewedNative/FiniteOrderCheck.lean) and [integer replay](../../lean/RKCert/ReviewedNative/ERKQuadraticIntegerReplay.lean). Its principal theorem is **RKResearch.Certified.ERK7FactorialNine.exact_order_seven_iff**. In the configured Lean project, the direct build command is

    lake build RKCert.ReviewedNative.ERK7FactorialNine
