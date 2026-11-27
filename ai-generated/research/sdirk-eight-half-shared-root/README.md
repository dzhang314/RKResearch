# No singleton shared-root discrepancy in the ten-stage SDIRK8 endpoint pair

Use the [all-active half-diagonal endpoint pair](../sdirk-eight-half-equal/README.md) over a field of characteristic zero. Let \(\boldsymbol h=(A-\gamma I)\boldsymbol g\). The eight physical quadratic-zero rows \(U\) have a profile relation
\[
        q(c_i)h_i=p(c_i),\quad \deg q\le2,\quad
        p\in\langle L_3,L_4,L_5\rangle,\quad p,q\ne0 .
\]
The [coprime exclusion](../sdirk-eight-half-arithmetic-quadratic/README.md) leaves only shared roots. Write \(p=d_0p_0,q=d_0q_0\) after maximal cancellation. A **discrepancy** is a row where \(q_0(c_i)h_i-p_0(c_i)\ne0\), necessarily at an actual root clock of \(d_0\).

**Result.** No discrepancy clock consists of just one physical row. This includes charts with eight distinct physical clocks and charts with one or more other repetitions. Consequently the remaining endpoint-pair chart has **either seven distinct clocks and one unequal-\(h\) double group at a linear common factor, or six distinct clocks and two unequal-\(h\) double groups at both roots of a fully canceled quadratic**. The [repeated-clock follow-up](../sdirk-eight-half-repeated/README.md) excludes both remaining group charts. The unrestricted strict SDIRK8 stage interval remains **10–11**.

## 1. A chronological gate that also works at repeated clocks

The four pegged front/rear zero clocks \(a,b,c,d\) are distinct and have nonzero cubic defects. As in the [chronological reduction](../sdirk-eight-half-quadratic/README.md), the low three literal reads at row four determine \(h_s=H_{\mathrm{tap}}(s)\), \(s=c_4\). At \(s=a,b\) they give the padded earlier row exactly, hence a literal twin. In addition the early determinant \(\mathfrak d(s)\) of \(\boldsymbol h,C\boldsymbol h,L_4(\boldsymbol c)\) is nonzero: a singular early rank would force the replacement determinant with \(A\boldsymbol h\) to vanish, contrary to the existing gcd check. These statements use actual taps and do not assume a single-valued defect.

The fifth zero clock \(y=c_5\) also cannot repeat \(a,b,s\), even if its defect could differ. The two pure rank reads have the affine form
\[
               A_0(s,y)+B_0(s,y)h_y=0,\qquad
               C_0(s,y)+D_0(s,y)h_y=0 .
\]
At \(y=a,b,s\), the padded predecessor defect gives an affine solution (checked by polynomial substitution). Two distinct defect values would require both affine coefficients to vanish. For each front phase and each of the three repeated clocks, the exact \(\gcd_s(B_0(s,y),D_0(s,y))\) has no factor outside the known nonzero \(\mathfrak d(s)\) guard. Thus \(h_y\) must equal the predecessor value. The same donor tap and three-clock Vandermonde as in the earlier chart then give a literal twin, again impossible. We can therefore use the necessary quadratic fifth-clock equation \(R(s,y)=0\), after removal of the three earlier clock factors, **irrespective of other clock collisions**.

## 2. A complete finite singleton check

With \(g_1=1/8\), the discrepancy vector
\[
 \boldsymbol u=q_0(\boldsymbol c)\odot\boldsymbol h-p_0(\boldsymbol c)
             +p_0(\gamma)\boldsymbol g/g_1
\]
vanishes at the endpoints and is supported at shared-root zero clocks. It belongs to \(E_4\) when \(\deg d_0=1\), and to \(E_3\) when \(\deg d_0=2\). At an actual singleton discrepancy \(r\), isolate its row in \(E_4\) by multiplying by \(C-r'I\) if there is a second distinct supported root \(r'\); otherwise it is already isolated. The pure pairing with \(\boldsymbol h\in F_3\) then gives \(b_i u_i h_i=0\) up to a nonzero scalar. Nonzero weight and discrepancy imply \(h_i=0\). Thus the singleton is at an interior clock, not one of the four nonzero-defect corners.

The actual weighted time reflection preserves the shared-root relation (replace \(X\) by \(1-X\) and scale by the reflected defect factor) and sends a singleton to a singleton. We can orient it at one of the two literal positions four or five, since all other noncorner physical zero rows are positions six and seven.

* If the singleton is at \(s\), use \(H_{\mathrm{tap}}(s)=0\) and \(R(s,y)=0\). The exact \(s\) projection has degree three in both front phases.
* If at \(y\), use \(A_0(s,y)=C_0(s,y)=0\) and \(R(s,y)=0\). Project by the gcd of the two \(Y\)-resultants, removing only the guarded factors of \(\mathfrak d(s)\). It has degree nine: exact factor degrees \(3+6\) for front star and \(9\) for front arithmetic. In each scalar quotient intersect the three \(Y\) equations by exact gcd.

For each surviving literal clock fiber, with \(r=s\) or \(y\), normalize \(q=X-r\) or \(q=(X-r)(X-\xi)\). The four literal front values are known and at distinct clocks; interpolate \(p\in\langle L_3,L_4,L_5\rangle\) from the values \(p(x)=q(x)h_x\) at \(a,b\) and one of \(s,y\). The preceding exact rank audit supplies one of these third-site pivots. The fourth value imposes one affine equation in \(\xi\) in the quadratic case, and is a direct exact check in the linear case. Finally use
\[
                        l q(d)p(c)-k q(c)p(d)=0 ,
\]
where \(k,l\) are the normalized reverse corner defects. This necessary equation is valid even if an unrelated repeated discrepancy is a rear clock and \(q\) vanishes there. There is no division at a physical pole. The finite replay permits other coincidences between front and rear clocks and does not impose \(q(c),q(d)\ne0\).

The [replay](check_no_singleton.py) finds no linear or quadratic pencil candidate in any orientation. Every nonzero divisor used in a degree-two \(Y\) quotient is checked for a unit; a zero-divisor splits the quotient exactly into the two clock roots rather than falsely discarding a branch. The proof uses only the literal chronology and the rear ratio after the paid singleton pairing and does not require the distinct-clock Bézout identity.

## 3. An exhaustive remaining physical census for this chart

Write \(n\) for the number of distinct **physical** zero clocks (including aggregate-canceled ones), with nodal polynomial \(D\). The earlier corner census gives \(n\ge6\). If \(h\) is single-valued, the [no-repeat theorem](../sdirk-eight-half-distinct/README.md) gives \(n=8\), which has a singleton discrepancy and is now excluded. Thus \(n=6,7\).

At each physical clock \(x\), use group sums \(H_x=\sum_{c_i=x}b_i h_i\), \(K_x=\sum_{c_i=x}b_i h_i^2\), counting only \(U\). Interpolate \(R(x)=D'(x)H_x\) and \(S(x)=D'(x)K_x\). The paid five linear and two quadratic \(h\) moments give \(\deg R\le n-6\) and \(\deg S\le n-3\) by leading-coefficient Lagrange pairing. At each clock \(q(x)K_x=p(x)H_x\) holds even if \(q(x)=p(x)=0\). The polynomial \(qS-pR\) has degree at most \(n-1\) and vanishes at all \(n\) clocks, hence is zero. Thus \(R=q_0 Z,S=p_0 Z\). Here \(R\ne0\): at least one nonzero-defect corner is singleton, since there are at most two repeated groups among eight rows and at least six clocks.

A fully canceled quadratic has two distinct actual discrepancy clocks by the [earlier single-support obstruction](../sdirk-eight-half-quadratic/README.md): one support clock would force the cubic reduced numerator to be a fourth Gauss cardinal, violating the exact corner slopes. Therefore it cannot occur at \(n=7\), where only one clock repeats. The remaining single common root is the repeated pair's clock. If \(q_0\) is linear then degree forces \(Z\) constant; if \(q_0=1\) and \(q\) is linear, the reduced numerator necessarily has degree four (the same single-support cubic obstruction) and the bound \(\deg S\le4\) again forces \(Z\) constant.

When \(n=6\), \(R\) is a nonzero constant. This excludes a reduced linear denominator. A fully canceled *linear* \(q\) would require the reduced numerator to have degree four, contradicting \(\deg S\le3\). So \(q\) is a fully canceled quadratic. Both supported roots repeat, requiring exactly two physical double groups. Their aggregate \(H_x=R/D'(x)\) is nonzero; since \(K_x=p_0(x)H_x\), a common defect value on a double group would have to equal its reduced polynomial value, contrary to discrepancy. The groups therefore have two different \(h\)'s each.

The [Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8SharedClockReceipts.lean) checks affine uniqueness, singleton pairing, coprime dual degree budgeting and the signed two-weight variance identity. The chronology and exact finite computations are source-level. Run `python3 check_no_singleton.py` from this folder within the repository with `sympy==1.14.0` and `python-flint==0.9.0`; it uses the two preceding quadratic checker directories.
