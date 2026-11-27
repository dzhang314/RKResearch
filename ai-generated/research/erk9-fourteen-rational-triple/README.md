# Exact rational ERK order nine in fourteen stages

The [literal strict tableau](tableau.json) has **rational coefficients and exact order nine in fourteen physical stages**. It improves the previous [rational upper bound of fifteen](../erk9-fifteen-native-upper/README.md) to **fourteen** over every characteristic-zero field, in particular over \(\mathbb Q\). There is no new claim about a minimum or about order ten. The signed weights and one clock at 2 are intentional; no positivity or interval constraint belongs to the ordinary ERK problem.

The common coefficient denominator is \(D=3941167085856000=2^8 3^9 5^3 7^2 11\cdot13\cdot19\cdot47\). The ordinary order identities specialize to any commutative ring in which this integer is invertible. The ten-vertex bush has normalized defect \(-1/2160\), so the method is exact order nine over each **nontrivial** such ring. It does not replace the factorial-only ring bound, since \(D\) has extra primes. The tenth tall tree also fails, with normalized defect \(-7167/32500\).

## Physical construction

The six opening clocks, in forward causal order, are \(0,1/10,1/5,3/10,3/4,4/5\). Only their origin is weighted. Use the canonical four-point cubic interpolator \(\Pi\) at old clocks \(0,p,q,r=0,3/10,3/4,4/5\) and its two actual size-five donor directions
\[
     \mathbf Q=(A\mathbf c^{\odot3}-\mathbf c^{\odot4}/4)|_{p,q,r},
                  \qquad \mathbf V_0=(A_{i,\,1/5})_{i=p,q,r}.
\]
Their annihilator \(\ell\) describes the exact size-five source space \(H_5=\ker\ell\) inside \(X\mathcal P_3\). The third clean donor tap onto \(q\) is the adjustable scalar \(f\); its other taps restore the first three exact scalar primitive moments. This is the same verified opening family as in the [two-pair construction](../../upper-bounds/real-algebraic/erk14-order9-six-opening-two-pair/README.md), but the high rows below use one triple, signed shares, and a different rational quadrature.

Take the seven contributing scalar clocks to be \(0,1,2/3,1/2,2,4/5,1/6\), with interpolatory integration weights. The monic polynomial with those seven roots and its product by \(X\) both integrate to zero, so the rule is exact through scalar degree eight. This follows by literal rational integration, with no algebraic coordinates. Its failure on degree nine is just the bush defect above. The eight physical high rows in **reverse** causal order are
\[
           1,\quad 2/3,\quad 2/3,\quad 1/2,\quad 2/3,\quad 2,\quad 4/5,\quad 1/6 .
\]
The three physical scores at \(2/3\) are \((-729,729,-243)/2240\), in that reverse order. Their scalar weight is \(-243/2240\). All 14 rows of the literal tableau are distinct, including the three at the same clock; no virtual donor or extra hidden row is counted.

In reverse \(y=1-x\), put \(a=1/3\), \(t=1/2=3a/2\). The weighted transpose \(L\) satisfies \(L\mathbf1=\mathbf y\). The second physical triple row taps the first by \(a\), giving distinct opposite first values of
\[
   \mathbf u=L\mathbf y-\mathbf y^{\odot2}/2,\quad
   \mathbf g=L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\quad
   \mathbf h=L\mathbf u .
\]
At \(t\) the \(y,y^2\) requirements use one scalar donor site \(a\); they are compatible exactly because \(t=3a/2\). The two actual early occurrences are used separately to kill its \(\mathbf u\) read. The third triple row uses those two and the actual \(t\) row to make the weighted aggregate of \(\mathbf u,\mathbf g,\mathbf h\) at their common clock zero. Consequently \(\mathbf u\) and \(\mathbf v=\mathbf g/2+\mathbf h\) are two independent opposed directions on the three physical rows, and are zero at the singleton interiors.

The cubic reverse defect \(\mathbf k=L\mathbf y^{\odot3}-\mathbf y^{\odot4}/4\) is fixed through the first subsequent singleton (at \(x=2\)). Its weighted action on the pressure polynomial
\[
                      X(X-4/5)(X-1/6)(X-\tau)
\]
is zero precisely at \(\tau=17/26\). Setting \(\ell\) of that polynomial to zero gives \(f=6128/131625\) exactly. The final two available cubic responses then kill \(H_5\), and the last three free \(L\mathbf v\) responses kill \(H_5\) as well. Each of those responses is solved by actual earlier-tap equations, with no extra stage. The forward high block is the weighted transpose of \(L\) in reversed order; its low/high cross block is \((EJ-BE)\Pi\), where \(J\) is scalar integration from zero and \(E\) evaluates at the actual high sites.

For ordinary order, through nine there is at most a single propagated primitive mark from any size-five source. The scalar comparisons use the degree-eight rule and formal integration by parts. Up through two exterior reverse steps the grouped \(\mathbf u,\mathbf g,\mathbf h\) errors vanish. At the last possible exterior step the only new errors are \(\mathbf k\) and \(L\) on an opposed direction; \(L\mathbf u=\mathbf h\) and the paid \(L\mathbf v\) complete the latter. The pair/triple rank and locality calculations are all literal in the generator. For a separate check which does not rely on this marked reduction, the integer verifier enumerates **all 486** ordinary rooted trees through nine and checks each reviewed factorial-normalized weight, as well as both actual size-ten failures.

## Reproduce

From this directory:

    python3 -B construct.py
    python3 -B verify.py
    sha256sum -c sources.sha256

The first script regenerates the fixture byte for byte from the rational construction; the second independently checks only the literal output. Neither needs a third-party Python package. All tree counting and arithmetic are exact.
