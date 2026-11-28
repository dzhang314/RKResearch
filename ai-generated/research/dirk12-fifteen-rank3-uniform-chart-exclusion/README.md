# DIRK12/15: the high uniform terminal-dirty visible chart is impossible

This eliminates the **entire uniform polynomial branch** of the [high visible reverse-rank-four equality reduction](../dirk12-fifteen-rank3-high-visible-cubic/README.md) for real ordinary \(C(2)\) DIRK at order twelve and fifteen stages with \(f_5=3\). It does **not** exclude all fifteen-stage tableaux. In this same rank-four visible face the [singular rational profiles](../dirk12-fifteen-rank3-rational-profile-census/README.md) remain. Other faces include reverse rank five, weighted-invisible cubic directions, the all-cancelling four-label branch, and the separate \(f_5=4\) and non-\(C(2)\) reductions. The overall real bound remains **15–16**.

We use genuine rooted numerical spaces \(T_j\), pure spaces \(F_j\), and true scalar weighted reverse words \(\mathcal B_j\) at tree grade \(j\), meaning tree order minus one. Write \(o,\tau\) for the literal first and last rows, \(\mathbf c=A\mathbf1\), \(C=\operatorname{diag}(\mathbf c)\), \(\beta\mathbf v=\mathbf b\odot\mathbf v\), \(D=L'_6\) for the fixed shifted Legendre derivative, and \(\mathbf h=A\mathbf c^2-\mathbf c^3/3\).

## Actual clean-coordinate and grade-six data

The high uniform reduction already gives ten live dirty rows at distinct labels with \(h_i=P_f(c_i)\) for one nonzero polynomial \(P_f\) of degree at most three; all other physical rows are the two literal endpoints and three live clean rows at distinct nonendpoint labels. There are no uncounted ghost rows, and the only weight which might be zero is \(b_o\). The clock of the ordinary literal origin is zero and that of the live terminal is one. Both diagonals are zero, the latter's whole column is zero, and \(b_\tau\ne1/42\). The required endpoint card of grade six is
\[
 \mathbf L=\mathbf e_\tau-b_\tau C D(\mathbf c)\in F_6.
\]
Its terminal value is \(1-42b_\tau\ne0\). The genuine flags from the actual equality frame and the independent occupied powers are
\[
\begin{aligned}
& F_j=\mathbf h P_{j-3}(\mathbf c) \quad (j=3,4,5),\qquad
 F_6=\mathbf h P_3(\mathbf c)+\langle\mathbf L\rangle,\\
& \mathcal B_j=(\beta\mathbf h)P_{j-3}(\mathbf c) \quad (j=3,4,5,6),\qquad
 \operatorname{Ann}T_6=\mathcal B_5 .
\end{aligned}
\]
Here \(P_d\) denotes polynomials of degree at most \(d\). The reverse band is literally zero on every clean row, even if \(b_o=0\). No whole normalized reversed method is assumed.

Every clean coordinate vector is in \(T_6\), as \(\operatorname{Ann}T_6\) is supported on the ten dirty positions. Since \(T_6=P_6(\mathbf c)+\langle\mathbf e_\tau\rangle+\mathbf hP_3(\mathbf c)\), any vector supported on clean rows has a representation whose scalar restriction on the dirty labels is \(S(X)+P_f(X)R(X)=0\) with degree at most six. Ten distinct roots give the polynomial identity. Consequently on all nonterminal clean rows it is \(-P_f(\mathbf c)R(\mathbf c)\); the individual coordinate vectors show \(P_f\) is nonzero on the literal origin and all three clean interiors. Write these three interiors in **physical forward chronology** as \(x_1,x_2,x_3\), without assuming numerical ordering.

In reflection use \(y=1-x\), \(t=1-x_3\), and call \(P(X)\) the reflected \(P_f(1-X)\), scaled to monic when useful. The first nonzero value of the genuine weighted grade-four contrast
\[
                   \mathbf z=\beta[\mathbf y\odot(P(\mathbf y)-\mathbf h)]
\]
in actual reverse chronology is at the first interior \(t\ne0\), since it is zero on all dirty rows and at the reflected origin (physical terminal). Scalar profiles are reflected along with the clock, and an overall common scaling of the cubic defect and its profile makes no difference. Let \(N\) be the actual transposed matrix with stages in reverse chronology and \(Y=\operatorname{diag}(\mathbf y)\). Its genuine commutator \(YN-NY-N^2\) has grade-six pure output on \(\mathbf z\) by the identity \(XJ-JX-J^2=0\), where \(JQ(s)=\int_0^s Q\). Its pivot is exactly \(-A_{ii}^2 z_i\); hence the physical diagonal there is zero. The actual two primitive reads of \(\mathbf z,Y\mathbf z\) now give
\[
                   J[XP](t)=J[X^2P](t)=0 .
\]
All grades are at most six. If \(P(0)=0\) in reflection, instead start the grade-three unmultiplied contrast \(\beta(P(\mathbf y)-\mathbf h)\), zero on the reflected origin and all preceding dirty rows. The now explicit clean pivot gives the three moments of \(P\) against \(1,X,X^2\) on \([0,t]\); since \(P=XQ,\deg Q\le2\), the fixed \(X\,dX\) Gram after scaling by \(t\ne0\) gives \(P=0\), impossible. Thus \(P\) is nonzero at **both** ends.

## The exact scalar hull elimination

Let \(V\) be the degree-three monic hull of the three active clean interior labels in the reflected coordinate. Its test against every \(X(1-X)R\), \(\deg R\le3\), vanishes at all clean nodes. On dirty rows the cubic equals \(P\). Hence the true grade-three moment paired with the scalar test of degree at most eight gives
\[
                   VP\perp P_3\quad\hbox{for }X(1-X)\,dX .
\]
The scalar product has degree at most eleven. The two pivot moments already exclude \(\deg P\le1\). For degree two they force
\[
                  B(X)=X^2-\tfrac65t X+\tfrac3{10}t^2
\]
as the monic \(P\). Then \(VP\) belongs to the span of the degree-four and degree-five shifted Jacobi polynomials \(D_4=L'_5,D_5=L'_6\) for \(X(1-X)\,dX\), and vanishes at \(t\). Their consecutive pair is coprime. Either this forces the lower degree when \(D_4(t)=0\), impossible, or \(B\) must divide \(D_5(X)D_4(t)-D_4(X)D_5(t)\). The two remainder coefficients, degrees eight and nine in \(t\), have exact rational gcd one. This closes the quadratic profile without a tableau pivot division.

For degree three write the monic scalar profile after the two pivot moments as
\[
 P=X^3+sX^2-\tfrac65(st+t^2)X+\tfrac3{10}st^2+\tfrac25t^3 .
\]
Write \(V=(X-t)(X^2+gX+k)\); the other two interior clocks are the roots of this exact monic quadratic. For \(i=0,1,2,3\) let the \(i\)-th row of the \(4\times3\) scalar moment matrix be the coefficients of \(g,k,1\) in
\[
             \int_0^1 X^{\,i+1}(1-X)(X-t)(X^2+gX+k) P(X)\,dX.
\]
All four \(3\times3\) minors must vanish, since \((g,k,1)^{\mathsf T}\ne0\). The exact script forms these four polynomials (each degree three in \(s\)), takes four pairwise resultants in \(s\), and computes their monic gcd \(m(t)\), degree 36. Thus **every** possible \(t\) is a root of \(m\), with no assumption that a minor stays full degree on specialization. The padded Sylvester identity makes the resultant a necessary zero at a common finite root even when leading coefficients drop. The exact script then performs Euclidean steps on the first two minors in the algebra \(\mathbb Q[t]/(m)\), checking the inverses used by exact gcds. A linear remainder with unit leading coefficient fixes \(s\). Rows zero and one recover \(g,k\) by a determinant verified to be a unit in the same algebra; all four equations then re-evaluate to zero there. Thus the following tests are made against the **full** algebraic necessary locus, not just approximate roots. An optional exact Sturm count gives ten real \(t\)'s for this scalar relaxation alone, but no part of the exclusion uses numerical isolation or existence of an actual tableau at these points.

## Unit gates on the scalar candidates

All arithmetic below uses the just-specified \(P,s,g,k,t\). Define
\[
 A_f(y)=\int_y^1(1-X)P(X)\,dX,\quad
 B_r(y)=J[XP](y),\quad C_r(y)=J[X^2P](y).
\]
The \((1-X)\) factor in the forward expression accounts for the switch back to \(x\). These are polynomials. For any polynomial \(G(y)\), to rule out its vanishing at either of the other clean clocks, reduce it to \(a+b y\) modulo \(y^2+gy+k\) and check the norm \(a^2-ga b+kb^2\) is a unit in the degree-36 parameter algebra. This is the determinant of multiplication on the monic quadratic quotient, including any multiplicity. All gates below are units, computed over the rationals by the modular receipts specified at the end.

1. **Forward diagonal.** \(A_f\) has unit norm. The ordinary grade-four \(\mathbf z_f=C(P_f(\mathbf c)-\mathbf h)\) is first nonzero at \(x_1\); ordinary \(F_5\) is clean, so its diagonal \(d=A_{i_1i_1}\) is nonzero by \(d\,x_1P_f(x_1)=J[xP_f](x_1)\).
2. **Forward five-dirty gate.** The determinant of the coefficient remainders modulo \(P\) of \(A_f(y),\,yA_f(y),\,(1-y)D(y)\) is a unit. This is a test in three coefficient coordinates, not pointwise divisions at polynomial roots.
3. **Empty first reverse gap.** Put \(H=C_r-t B_r\). At the middle reflected clean clock \(u=1-x_2\), the actual grade-five \((Y-t)\mathbf z\) is first nonzero, and gives the diagonal \(e\) there by
   \[
                         e\,u(u-t)P(u)=H(u).
   \]
   The norm of \(u(u-t)P(u)[uB_r(u)-C_r(u)]-H(u)B_r(u)\) is a unit.
4. **Empty first forward gap.** Put \(z=-g-u=1-x_1\), \(\xi_1=1-z,\xi_2=1-u\), \(p_i=\xi_i P(1-\xi_i)\), \(F_i=A_f(1-\xi_i)\), \(\ell_i=\xi_iD(1-\xi_i)\), \(d_n=u(u-t)P(u)\), \(d_u=H(u)\). With \(q=\xi_2-\xi_1\), the following polynomial has unit norm:
   \[
     \big[(q p_1-F_1)(d_n F_2-d_u p_2)-d_u F_2p_1\big]\ell_1
               +F_1^2 d_n\ell_2 .
   \]
   These are deliberately cross-multiplied expressions, with no need to divide by \(D\) at any arbitrary clock.
5. **Same-clock final factors.** Both \(3s+4t\) and \(9s+16t\) are units in the parameter algebra.

## Exact chronology DAG to four–one–one–four

For cubic \(P\), the two pivot moments after scaling \([0,t]\) to \([0,1]\) give at least two sign-changing roots in the open scaled interval (otherwise test against the hull of the at most one sign-changing root). Hence \(P\) has three simple real roots. In either orientation the actual \(P\) is nonzero at the originating endpoint. It cannot divide its own antiderivative \(J[XP]\): two consecutive roots lie on the same side of zero, so the integrand between them is of one strict sign and their primitive values cannot both be zero.

- **End counts bounded above by five.** In each direction the grade-four clean contrast \(X(P-\mathbf h)\), weighted in reversal, is zero strictly before the first interior clean row. Its genuine primitive zero there, on the earlier dirt, gives the polynomial \(J[XP]+P R_2\), degree at most five, vanishing at the earlier dirty labels, through actual \(F_5\) or \(\mathcal B_5\). It cannot be identically zero by the preceding nondivisibility. Thus at most five dirty predecessors in either direction.
- **End counts bounded below by four.** If either end had at most three, the grade-three contrasts \(U-\mathbf h q\), with \(\deg U\le3\) and constant \(q\), would have a nonzero scalar profile vanishing numerically on the full earlier prefix by elementary dimension (five coefficients, at most four constraints; the pure constant has zero kernel as soon as any dirty row is present). In the forward direction the clean grade-five commutator and the verified nonzero diagonal first force \(U(x_1)=0\). The first two primitive reads then force \(JU(x_1)=J[XU](x_1)=0\); factoring \(X(X-x_1)\) contradicts the fixed \(X(1-X)\) Gram after scaling. In reverse the first interior diagonal is already zero and grades through six are clean, so three primitive reads force \(JU(t)=J[XU](t)=J[X^2U](t)=0\); the origin root and the fixed \(X\,dX\) Gram contradict the nonzero profile. With no preceding dirty rows the nonzero scalar profile can be chosen directly, so the dimension count never requires a division at an absent site.
- **Five forward predecessors impossible.** If there were five, let \(F\) be their monic hull. The ordinary \(A\mathbf z_f\) calculation means \(J[xP_f]+P_f R_2\) is a nonzero multiple of \(F\). Also \(R\mathbf z_f=(CA-AC-A^2)\mathbf z_f\) is in \(F_6=\mathbf hP_3+\langle\mathbf L\rangle\); at \(x_1\) its value is \(-d^2x_1P_f(x_1)\ne0\). Thus the coefficient of \(\mathbf L\) is nonzero. At each earlier dirty row the commutator is zero numerically, so a polynomial \(P_f R_3-\lambda b_\tau xD(x)\) of degree at most six (with \(\lambda b_\tau\ne0\)) is divisible by \(F\). Comparing remainders modulo \(P_f\), this forces \(xD\) to lie in the span of \(J[xP_f]\) and \(xJ[xP_f]\). Reflection gives exactly the vanishing determinant of gate 2, impossible. No division by \(J[xP_f]\) at roots is needed.
- **Empty reverse gap impossible.** If no dirty row lay between the first two reverse clean interiors, \(N\mathbf z\) would be zero before the middle clean row: it is zero before the first interior by causality and at that interior by its zero diagonal. Thus \(N^2\mathbf z\) would read only its own diagonal times \(N\mathbf z\) there. The true grade-five and grade-six scalar reads at that row give \(J^2[XP](u)=e B_r(u)\). Since \(J^2[XP](u)=uB_r(u)-C_r(u)\) and the genuine masked read fixes \(e\) as above, this is exactly the forbidden gate 3.
- **Empty forward gap impossible.** Suppose no dirty row separates the first two forward clean interiors. For \(\mathbf z_f\) as above the first two numerical values of \(A\mathbf z_f\) are \(F_1,F_2\); all earlier entries before the first clean vanish. Write \(d=F_1/p_1\). The actual commutator values at these two rows are \(-d^2p_1\) and
  \[
                       (q-d)(F_2-e p_2)-e F_2 .
  \]
  In fact up to the middle row \(A\mathbf z_f\) can only see its numerical first clean input and its diagonal, and at the middle row \(A^2\mathbf z_f\) can only see the two actual nonzero values already listed. On both clean rows this commutator is a common scalar times \(-b_\tau \xi_iD(\xi_i)\), so cross-multiplying their values with \(\ell_i\) gives gate 4. The only cleared diagonal denominators \(p_1\) and \(d_n\) are nonzero because the actual clean clocks are distinct, nonendpoint, and \(P\) is nonzero there. Gate 4 is nonzero, so the gap cannot be empty.

There are ten dirty physical rows total. Each end needs at least four, the forward end can have at most four, and each of the two gaps between clean interiors needs at least one. Thus the entire physical chronology of dirty counts is exactly **four, one, one, four** (before first interior, first gap, second gap, after last interior). This does not put the numerical clocks in sorted order.

## The actual single-dirty reverse gap forces an impossible extra root

Consider the four actual dirty predecessors of the first reversed clean interior \(t\). The grade-four contrast \(\mathbf z\) already has zero inputs through them. More generally, degree-four scalar profiles \(S\) with affine cubic corrections \(Q\) can be chosen zero on that earlier five-row prefix (origin plus four dirt), using the seven available coefficients. Their map to \(S\) is injective because a pure affine \(Q\) would vanish at four distinct dirty labels. At the first clean interior their primitive values \(JS(t),J[XS](t)\) are zero by the known zero diagonal and clean \(\mathcal B_6\). Together with \(S(0)=0\), these put the profiles in a two-dimensional space, by the fixed two-row \(X\,dX\) Gram. Consequently this space is filled by actual contrasts, including an independent choice
\[
 \mathbf z'=\beta[X B-\mathbf h Q](\mathbf y),\qquad
 B=X^2-\tfrac65tX+\tfrac3{10}t^2 .
\]
The difference \(XB-PQ\) is a nonzero multiple of the monic hull of the four preceding dirty labels: degree at most four, four roots, and not identically zero because \(P(0)\ne0\). Thus \(\mathbf z'\) is nonzero at the unique dirty row \(j\) in the first reverse gap, which is not one of the four preceding dirty labels.

The true commutator of each contrast belongs to \(\mathcal B_6\) and is zero at the four preceding dirty coordinates by triangularity. Since \(\mathcal B_6=(\beta\mathbf h)P_3(\mathbf c)\), the four distinct clock zeros force its scalar multiplier polynomial zero identically. Thus each commutator is zero **globally**, not just on the clean rows. Also \(N\mathbf z,N\mathbf z'\) are zero through the first clean row because its diagonal is zero. If \(N\mathbf z\) were zero at the unique gap dirt \(j\), the same actual \(N^2\mathbf z\) calculation at the middle row would yield forbidden gate 3. Therefore \(N\mathbf z(j)\ne0\); it is exactly the tap from the first clean pivot times that pivot's contrast entry.

Let \(y_j\) be the actual gap clock, \(a_{jj}\) its (unchanged) diagonal. Expanding the two commutators at the gap row gives, successively,
\[
    (y_j-t-a_{jj})N\mathbf z(j)=0,\qquad
    -a_{jj}^2 z'_j=0 .
\]
For the second identity the term coming from the first clean row disappears using the first equality; the only extra term is the genuine diagonal square on the nonzero \(z'_j\). Thus \(a_{jj}=0\), \(y_j=t\). This equal numerical clock is derived, not assumed a clone. It is distinct from the four earlier dirty labels because all ten active dirty labels are distinct.

Now \((Y-t)\mathbf z\) has true grade five; it is zero through the gap dirt including \(y_j=t\). Its actual primitive yields a polynomial
\[
                      I(X)+P(X)R_3(X),\qquad I=J[X(X-t)P],
\]
zero at all four earlier dirty labels **and** \(t\), by clean coefficient support of the genuine weighted grade-six discrepancy. But \(I(t)=0\) by the two first-pivot moments and \(P(t)\ne0\), so \(R_3(t)=0\). Dividing this *known polynomial factor* \(X-t\), not a stage pivot, gives a degree-at-most-five polynomial zero at the four earlier dirty labels. Its remainders modulo \(P\) must therefore put \(I/(X-t)\) in the span of \(XB,X^2B\), by the earlier literal four-root characterization. The fixed determinant of their three coefficient remainders is
\[
                    \frac{t^7(3s+4t)(9s+16t)}{300000}.
\]
This identity is replayed over the rationals, and both final factors are units by gate 5; \(t\ne0\) by the physical clean clock. Contradiction. This closes the final cubic branch and hence the entire specified uniform terminal-dirty chart.

## Exact arithmetic and Lean scope

The script uses exact rational polynomial arithmetic (SymPy) for the quadratic remainders, the \(4\times3\) moment matrix, cubic minors and resultants, Euclidean reductions modulo \(m\), and the final divided primitive determinant. It also reconstructs all actual gate residues at primes 1009 and 1013. Their common argument is solely a **unit certificate in a fixed monic polynomial quotient**: if the gate residue polynomial is coprime to the monic degree-36 \(m\) modulo a good prime, its multiplication determinant is a unit there and is a nonzero rational determinant before reduction. Thus the gate is nonzero at every characteristic-zero root. This does not infer divisibility, real roots, clock coincidences or existence of any method from a modular tableau; no unknown coefficient is reduced. Both primes pass all eight quotient-unit checks, and all exact recovered-denominator coefficients are locally defined at both primes. The quadratic pair independently has a rational gcd-one check.

The root-order, rank and actual chronology reduction above is an exact mathematical proof, not an end-to-end native exclusion. The standalone **DIRKOrderTwelveFifteenUniformChartUnitArithmetic** checks linked coefficient Euclidean identities and strict remainder degree decreases for the eight degree-36 quotient units and the quadratic remainder pair modulo 1009, as published expanded receipts. It compiles on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 with only standard axioms. It does not formalize their derivation from the moment matrix. The reviewed **DIRKOrderTwelveFifteenUniformGapCore**, checked on Lean/Mathlib 4.36.0, proves four-live-root cancellation and the actual adjacent-matrix commutator expansion and same-clock/zero-diagonal implication. Earlier rooted equality and grade-six support inputs have separately native receipts in the prior packets. The optional real-root count of the relaxation is informational and not needed by the proof.

    python3 -B check.py --expanded /tmp/dirk12-uniform-expanded.json --sturm
    cmp expanded.json /tmp/dirk12-uniform-expanded.json
    python3 -B generate-lean.py /tmp/DIRKOrderTwelveFifteenUniformChartUnitArithmetic.lean
    cmp /tmp/DIRKOrderTwelveFifteenUniformChartUnitArithmetic.lean \
        ../../lean/RKCert/ReviewedNative/DIRKOrderTwelveFifteenUniformChartUnitArithmetic.lean
    sha256sum -c sources.sha256

From **ai-generated/lean** in the pinned Lean/Mathlib environment:

    lake build +RKCert.ReviewedNative.DIRKOrderTwelveFifteenUniformChartUnitArithmetic
    lake build +RKCert.ReviewedNative.DIRKOrderTwelveFifteenUniformGapCore
