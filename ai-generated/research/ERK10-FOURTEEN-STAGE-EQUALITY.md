# The exact 14-stage ERK order-ten equality case: ranks, reversal, and clean clocks

Work with an actual strictly lower triangular fourteen-row tableau of
rooted order ten over a field in which \(10!\ne0\). Grade is tree size
minus one; \(E_j\) is the actual numerical span and \(F_j\) its pure
zero-model pair space. Write \(c=A{\bf1}\), \(C=\operatorname{diag}(c)\),
\(Y=I-C\), \(d=Ac-c^2/2\), and \(J P(X)=\int_0^X P\).
All integrals are formal polynomial primitives.

**New conditional exclusions.** When every \(b_i\ne0\) and \(d,Cd\)
are independent, \(F_4=d\,\mathcal P_{\le2}(c)\) and there is a
unique polynomial \(G\) of degree at most two giving \(d_i=G(c_i)\)
at every dirty row \(d_i\ne0\). In characteristic zero, \(G\)
must have degree **exactly two**. There are just two remaining
physical clock presentations in this fork:
* four distinct dirty clocks, each an opposing pair, and six
  distinct clean Lobatto sites; or
* nine live, distinct dirty sites and five distinct clean sites.
  Dirty output weights have a single barycentric scale.

The first alternative is impossible over \(\mathbb Q\), not over
the real algebraic numbers merely for this reason.
The algebraic chart deductions also work over paid fields outside
characteristics 19, 31 and 60757. Zero-weight charts and the
\(d,Cd\)-dependent charts are not excluded. This does not change
the unrestricted **14–15** stage interval.

## The equality ledger and the literal endpoints

The [paid grade-five surplus](../lower-bounds/paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md)
supplies the uniform floor 14 and the exact equality ledger
\[
 \dim E_5=11,\quad \dim F_5=5,\quad bA=bY,\quad
 V_3=\operatorname{Ann}(E_5),\quad \dim V_3=3 .
\]
Here \(V_0=0\), \(V_1=\langle h_2\rangle\) with
\(h_2=2bYA-bY^2\), and \(V_{j+1}=V_j+V_jA+V_jY\).
The paid reverse no-plateau proof gives ranks \(j\) at \(0\le j\le3\).
If \(b_{14}=0\), pruning the last row preserves all rooted tests
and violates the floor. Thus \(b_{14}\ne0\), and strictness in
\(bA=bY\) gives \(c_{14}=1\).
Every \(V_j\) has last coordinate zero, so the actual physical
indicator \(e_{14}\) belongs to \(E_5\).
Pairing \(e_{14}\) with any pure grade-four vector costs \(5+4=9\)
and forces that pure vector to be zero at row 14. Thus row 14 is
individually point exact through grade four, with no all-live
assumption.

For \(5\le j\le7\), a numerical plateau \(E_j=E_{j+1}\)
would make \(\operatorname{Ann}(E_j)\) invariant under right
\(A,Y\). It contains \(h_2\) because \(h_2\) kills \(E_7\).
Modulo that annihilator, \(z=bY\) then satisfies
\(zY=2zA\). Multiplying by the diagonal partial inverse of \(Y\)
gives \(z=2z A Y^\dagger\), since \(z\) is supported where
\(Y\ne0\). The partial inverse is a polynomial in \(Y\), so this
calculation descends to the invariant quotient. Nilpotence gives
\(z\) in the annihilator, impossible as \(bY{\bf1}=1/2\).
The reverse rank caps now give
\[
 \dim E_6=12,\quad \dim E_7=13,\quad E_8=E_9=K^{14}.
\]
Separation and strict growth give \(\dim F_2\ge1\),
\(\dim F_3\ge2\), \(\dim F_4\ge3\); if all weights are live these
are equalities also by orthogonality to \(E_7,E_6,E_5\), respectively.
The independent-defect chart below uses this all-live equality,
not that deduction on an arbitrary degenerate pairing.

The exact grade-five model of \(e_{14}\) is \(30 b_{14}H\), where
\[
 H=X-14X^2+56X^3-84X^4+42X^5 .
\]
Indeed its origin is zero, and its five moments against
\(1,X,\ldots,X^4\) all equal \(1/30\). The paid anchored Beta
matrix gives uniqueness. **This does not yet fix \(b_{14}\)**
or give point exactness at grade five.

For later use the higher alias calibration is exact. The zero
numerical polynomial aliases at grades \(6\le g\le9\) are all
\(P\) with \(P(0)=0\), \(\deg P\le g\), and
\(\int X^iP=0\) for \(0\le i\le9-g\). Two generators at grade
six are \(JH,(1-X)H\) by \(Ae_{14}=Ye_{14}=0\).
At grade \(g\), add \(X^jJH,J(X^{j-1}JH)\) for \(1\le j\le g-6\).
Selecting coefficient columns \(2,1,3,4,\ldots,2(g-5)\), the
determinants are \(1/2,7/72,343/16200,343/405000\) at grades
six through nine (ordinary coefficient expansion). This is
\(2g-10\) independent aliases, and the anchored moment tests
are independent by the paid Beta matrix, so the list is exact.
Consequently
\[
 \dim F_6=7,\quad \dim F_7=9,\quad \dim F_8=11,\quad \dim F_9=12 .
\]
Concretely \(F_g\) in these grades is cut out in \(E_g\) by
initial coordinate zero and \(bC^i=0\) on the vector for
\(0\le i\le9-g\). The higher-alias calculation is separate from
the following scalar-exclusion Lean file.

Over characteristic zero, the
[shift-one weighted order-nine floor](WEIGHTED-ORDER-NINE-SHIFT-ONE-ATLAS.md)
applied to the actual \(bA\) forces \(b_{13}(1-c_{13})\ne0\)
and \(A_{14,13}\ne0\). Thus the actual first thirteen rows are
a sharp weighted size-nine prefix, not an invented alternate output.
Deleting \(e_{14}\) on restriction to this prefix reduces \(E_5\)
to rank ten, with one nonzero model-alias line \(KH\).
Restriction remains injective on \(E_4\): a nonzero multiple of
\(e_{14}\) cannot have a degree-four model, by uniqueness of its
degree-five model and the nonzero leading coefficient of \(H\).

## Weighted transpose at the saturated even midpoint

Now assume all output weights nonzero. Put \(B=\operatorname{diag}(b)\)
and \(A^\star=B^{-1}A^\mathsf T B\), and reverse literal stage order.
The reversed clock is \(Y{\bf1}\) by \(bA=bY\). In unpermuted
coordinates write
\[
 H_j=E_{9-j}^{\perp_B}\cap\{x:x_{14}=0\}.
\]
For \(0\le j\le4\), \(H_j=F_j\) by the exact numerical ranks,
pure orthogonality and last-row grade-four exactness.
The space \(H_j\) transports to \(H_{j+1}\) under \(A^\star,Y\)
by adjointness and \(AE_k,YE_k\subset E_{k+1}\).
Multiplication by an original pure vector in \(F_i\) transports
\(H_j\) to \(H_{i+j}\) whenever \(i+j\le9\), by testing against
\(E_{9-i-j}\). Every relevant two-pure product has one grade
at most four, already a common original pure factor in the induction.
The reflected unary polynomial primitive defect belongs to the
appropriate \(H_j\) by the paid scalar integration by parts
\[
 \int_0^1 (1-X)^k(JP)(X)\,dX
   =\frac1{k+1}\int_0^1(1-X)^{k+1}P(X)\,dX .
\]
All \(H_j\) annihilate \(b\) and the reflected scalar clock moments
are exact. The usual rooted pair recursion therefore proves
**the full order ten** of the actual reversed tableau. The
paid low pure rank lower bounds show \(\bar F_j=F_j\) through
grade four. This is the even-budget version of the
[ERK11 adjoint-proof induction](ERK11-ONE-SPARE-WEIGHTED-TRANSPOSE.md);
there is no untested \((5,5)\) product at order ten.

Additionally the numerical \(E_j\) are the same in both orientations
at all \(j\le9\). For \(j=5,6,7\), they are the orthogonal
complements of the common \(F_{9-j}\), and the other grades are
already common or full. In particular \(e_1,e_{14}\) both lie in
the common \(E_5\). Grade-five model maps can differ only by the
one-dimensional unanchored orthogonal degree-five polynomial line
(same moments against polynomials through degree four). If the two
grade-five *pure* spaces agree, then either map equals the other on
the common pure-plus-clock decomposition and both endpoints are
point exact to grade five; in that event \(b_1=b_{14}=1/30\).
Equality of the grade-five pure spaces is **not** assumed below.
In characteristic zero applying the shift-one floor to the reversed
tableau also forces \(A_{21}\ne0\).

## Independent quadratic defect: the two clean-boundary primitives

Assume \(d,Cd\) independent. Then \(F_3=\langle d,Cd\rangle\);
the [paid noninvariance argument at grade three](../lower-bounds/paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md#why-a-separated-explicit-stage-algebra-has-dim-f_5ge5)
forces \(F_4=\langle d,Cd,C^2d\rangle\).
Since \(d^2\in F_4\), there is a unique \(G\) of degree at most
two with \(d_i=G(c_i)\) for dirty \(i\). The reverse \(d\)
is a nonzero multiple of this same vector by \(\bar F_2=F_2\).

Call \(u\) the clock at the first nonzero clean row and \(v\) the
clock at the last clean row whose clock is not 1. They exist
because the two physical endpoints are clean through grade four.
The grade-three vector \(C(G(c)-d)\) is zero before the row with
clock \(u\): at dirty rows by definition, and at earlier clean
rows because their clock is zero. Its unary advance at \(u\)
is zero by strictness and exactly \(\int_0^u XG(X)\) by point
exactness through grade four at all clean stages.
The weighted transpose gives the companion primitive at \(v\).
Thus
\[
       \int_0^u XG(X)\,dX=0,\qquad
       \int_v^1 (1-X)G(X)\,dX=0.                       \tag{1}
\]
This already excludes a nonzero constant \(G\).
Also \(G(0)\ne0\): otherwise \(G(c)-d\) itself is zero before
the first nonzero clean row, so the same argument gives
\(\int_0^u G=0\). For \(G=X(a+bX)\), these two tests give
\(3a+2bu=4a+3bu=0\), impossible. Reflection gives \(G(1)\ne0\).

There are at least four distinct dirty clocks. Separation of
\(d,Cd,C^2d\) gives at least three. If exactly three, \(F_4\)
contains every level indicator of these rows by interpolation
and the nonzero value of \(G\) there. Incoming reads to clean stages
on this space annihilate \(F_3\), so are on one line. The first
nonzero clean \(u\) has nonzero such read, by testing the
dirty-supported restriction of \(X\). At a first different
nonzero clean node test \((X^2(X-u)^2)'\) on the same dirty
support. All earlier clean contributions vanish, and the
calibrated first read is zero, hence so is the later primitive
despite its nonzero value \(X^2(X-u)^2\) there. Thus all clean
clocks would be among \(0,u\), giving at most five clocks total,
contrary to grade-five polynomial separation. This is also the
[reviewed native rank-three core obstruction](../lean/ERK-GRADE-EIGHT-OFF-CORE.md)
in characteristic zero.

## Balanced dirty measure: four pairs, fixed exterior clocks

The paid scalar tests \(b C^k d=0\) for \(0\le k\le7\)
say that the pooled measure with masses \(b_iG(c_i)\) at dirty
clocks has its first eight moments zero. If that measure is zero,
each dirty clock has zero ordinary pooled output mass because
\(G(c_i)\ne0\). Every dirty clock therefore needs at least two
physical rows (all \(b_i\ne0\)). The clean rows now integrate all
ordinary polynomials through degree nine. They have at least six
distinct clocks: if at most five, their one endpoint 1 and the
monic polynomial \(Q_0\) vanishing at the other at most four
clocks would make \(\int (1-X)Q_0(X)R(X)=0\) for all
\(\deg R\le4\), contrary to the paid Beta determinant.

Thus there are exactly eight dirty rows in four opposing pairs
and six distinct clean rows, including 0 and 1.
The four internal clean clocks are precisely the roots of
\[
 L(X)=42X^4-84X^3+56X^2-14X+1.
\]
Indeed their monic product is orthogonal for \(X(1-X)\) to
all polynomials through degree three, which determines it uniquely.
The residue of \(L\) has no root modulo 11, and the leading
coefficient is prime to 11, so no internal clean node is rational.

If \(G\) is linear, (1) yields
\(2(u-v)=1\), after solving each two-term primitive for the root
of \(G\): in left units it is \(2u/3\), in right units
\(2(1-v)/3\). Here \(u,v\) are distinct internal clean labels.
But \(L(v)=L(v+1/2)=0\) is impossible; \(8L(v+1/2)
=336v^4-56v^2+1\) and there is an integer Bézout identity
with constant 95. This proves the balanced linear exclusion.

## Unbalanced dirty measure: exact clean-weight tests

A nonzero pooled dirty measure needs at least nine distinct
active clocks by Vandermonde. Thus at most five clean **physical**
rows remain. The dirty \(d\)-moments also give
\[
          \sum_{\rm clean} b_i G(c_i)P(c_i)
                 =\int_0^1 G(X)P(X)\,dX,
                            \qquad \deg P\le7 .       \tag{2}
\]
Let \(K_s\) be the product over all distinct internal clean
clocks, of degree \(s\). The clean support includes the literal
endpoints 0 and 1 regardless of any pooled mass cancellations.
Equation (2) shows \(G K_s\) is orthogonal for weight \(X(1-X)\)
to every polynomial through degree \(5-s\).
If \(s\le1\), with \(\deg G\le2\), or \(s\le2\), with
\(\deg G\le1\), a nonsingular paid Beta matrix rules this out.
Thus there are at least four distinct clean clocks, or at least
five if \(G\) is linear.

**Linear \(G\).** There are exactly five distinct clean clocks.
The internal values are \(u,w,v\) in chronological order;
\(v=u-1/2\), and \(2u/3\) is the root of \(G\).
Set \(z=4u-3\), and let \(y=2w-1\). After centering
\(Z=2X-1\), the monic quartic \(G K_3\) has roots
\((z+1)/2,(z-1)/2,z/3,y\).
Its elementary symmetric sums \(S_i\) satisfy
\[
     S_2=-2/3,\qquad S_4=1/21,\qquad 7S_3+3S_1=0 .
\]
These are the three orthogonality tests with weight \(1-Z^2\)
against \(1,Z,Z^2\); the cleared even equations are
\(3+7S_2+35S_4=5+9S_2+21S_4=0\).
Insert the four roots into the three equations to get
\[
 \begin{split}
 7z^2+5+16zy&=0,\\
 7z(z^2-1)y&=4,\\
 7z^3+41z+(49z^2+15)y&=0.
 \end{split}
\]
They imply \(p(T)=49T^2-14T+29=0\) and
\(q(T)=77T^2-102T+25=0\) at \(T=z^2\).
The checked identity \((87-55T)p+(35T-19)q=2048\)
contradicts the paid field. Hence \(G\) is not linear here either.

**Quadratic \(G\), only four distinct clean clocks.** There
are exactly two internal clean clocks, so \(G K_2\) is the
quartic Lobatto polynomial up to scale, now using all four
orthogonality tests. Its roots are simple: in centered coordinates
\(Z=2X-1\), its normalized equation is \(J_4=21Z^4-14Z^2+1=0\),
with distinct squared values of sum \(2/3\) and product \(1/21\).
Passing to a splitting field only for naming roots, the two roots
of \(G\) are a pair of these four roots in
centered coordinates, and the two internal clean clocks are
the complementary pair. Call the centered roots of \(G\)
\(a,b\), with \(S=a+b,\ P=ab\), and write \(U=2u-1\)
for the first nonzero clean clock.
It is either one of the complementary roots or \(U=1\)
(the latter allows an earlier repeated endpoint clock).
Expanding the first equality of (1) and cancelling \(u^2\) gives
\[
              3U^2-(2+4S)U+1+2S+6P=0 .             \tag{3}
\]
If the two \(G\) roots are opposite, \(S=0\).
For a complementary \(U\), \(P=U^2-2/3\), and (3) gives
\(9U^2-2U-3=0\), incompatible with \(J_4(U)=0\) by
the checked Bézout constant 248. At \(U=1\) equation (3)
forces \(a^2=1/3\), directly contradicting \(J_4(a)=0\).
If the two roots are not opposite, a complementary \(U\)
has \(G\)-root pair \(-U,V\) where \(V^2=2/3-U^2\).
Equation (3) is \(7U^2-4U+1+(2-10U)V=0\).
Squaring gives
\(447U^4-288U^3-98U^2+56U-5=0\), incompatible with
\(J_4(U)=0\) by the checked constant 486056.
At \(U=1\), (3) instead gives \(S=1+3P\).
Since \(21P^2=1\) and \(3S^2=2+6P\), this implies
\(21P=-4\), contradicting \(21P^2=1\) by the paid 5.
These possibilities exhaust the first nonzero clean node.
Thus the unbalanced quadratic branch has exactly five distinct
clean rows and nine distinct, individually active dirty rows.

## Remaining scalar reconstruction in the unbalanced chart

Let \(u,w,v\) be the three remaining interior-in-time clean
rows (numerically distinct from each other and the endpoints).
The polynomial \(G\) is quadratic, nonzero at both endpoints,
and the exact independent scalar tests are (1) and
\[
 \int_0^1 X(1-X)G(X)(X-u)(X-w)(X-v)\,X^k\,dX=0,
                                    \qquad 0\le k\le2 .
\]
These are necessary, not sufficient, for a literal tableau.
Writing \(D(X)=\prod_{i\ {\rm dirty}}(X-c_i)\), the
unique moment relation on the nine distinct dirty sites is
\(b_iG(c_i)=\kappa/D'(c_i)\), \(\kappa\ne0\).
For instance the leading coefficient in ordinary degree-eight
Lagrange interpolation is that unique annihilating row.
This supplies a scalar reconstruction without selecting
a candidate \(A\) by parameter count.

The [Lean scalar companion](ERK10EqualityClockGate.lean) checks the
finite Bézout identities, formal implications in the centered
branches, and the modular root test. The literal graded and
rooted deductions above are mathematical. No native full
fourteen-stage exclusion, no construction, and no numerical
stage-bound improvement are asserted.
