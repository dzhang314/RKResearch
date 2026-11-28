# Exact degree-216 midpoint coefficient field and one certified real embedding

This is a field and root-isolation receipt for the surviving midpoint scalar candidate of the [degree-36 ordinary projection](../dirk12-fifteen-rank3-invisible-midpoint-zero-fourth-projection/README.md). It makes **no Runge–Kutta order claim** over characteristic zero.

Use \(a=1/2\), the primitive integer degree-36 polynomial \(Q_{36}\) for \(x=b/a\), the exact field expressions for \(y=c/a,t=e/a\), and the monic cubic \(F_x\) for the physical fifth ordinary clock \(f\) from the previous field data. In reflected variable \(Y\) define
\[
 P_*(Y)=Y(Y-1)\prod_{s\in\{a,ax,ay,at,f\}}[Y-(1-s)],\quad
 n_j=\int_0^1 Y^jP_*(Y)\,dY.
\]
Let \(q=n_0n_2/n_1^2,\ h=3n_1/(2n_0),\ L=4q/(9-4q)\). The unordered reverse support is the two roots of
\[
           D^2-hLD+\frac{h^2 L^2}{L+4}=0
\]
and the single label \(u=-hL/(L-2)\). This is the same orientation algebra as the split-free projection, with no new polynomial or assumed order.

## Characteristic-zero irreducibility

The primitive \(Q_{36}\) keeps degree and is irreducible modulo 137. At prime 31 its leading coefficient is a unit. In the residue field
\[
        \mathbb F_{31}[z]/(z^5+z^4+11z^3+30z^2+24z+27)
\]
the chosen \(z\) is a root of \(Q_{36}\). All rational coefficient denominators used for \(y,t,F_x\) at that place are units. Its monic cubic for \(f\) has no root: the replay checks its coprimeness with \(Y^{31^5}-Y\). Thus the characteristic-zero monic cubic is irreducible. In the degree-three residue extension, the discriminant of the stated orientation quadratic has Euler character \(-1\), so that quadratic is irreducible in characteristic zero as well.

These conclusions are ordinary finite residue-field unit arguments: a characteristic-zero monic factor at the indicated place would have integral coefficients (integral roots of a monic polynomial), hence preserve its degree on reduction. A square root of the integral discriminant would likewise be integral and reduce to a square. The resulting characteristic-zero algebra is a **field of degree \(36\cdot3\cdot2=216\)**; this alone does not verify any tableau.

## Certified real embedding

The supplied rational intervals isolate a simple real root \(x\) near \(0.1296731532\) of \(Q_{36}\) and a simple real root \(f\) near \(0.2347728503\) of \(F_x\) for that \(x\). Exact directed Horner evaluation proves opposite endpoint signs and a nonzero derivative throughout each interval, even for the \(x\)-dependent \(F_x\) coefficients. The same directed arithmetic checks \(1333/1000<q<1334/1000\) and a strictly positive orientation discriminant. Either orientation is real; the named real embedding chooses the plus-square-root expression for \(d\). The verifier bounds that square root by exact rational integer square roots and checks the ten scalar labels are distinct. It makes no claim that the possible tableaux meet the order equations.

    python3 -B verify.py

The independent standard-library replay uses the previous midpoint field JSON as a sibling; an explicit path can be passed as the first argument. The residue and real isolation arrays are entirely literal. No reduction of an unknown characteristic-zero tableau is made.
