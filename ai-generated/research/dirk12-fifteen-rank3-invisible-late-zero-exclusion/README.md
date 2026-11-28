# DIRK12/15: the late fourth ghost cannot have numerical clock zero

In the real order-twelve fifteen-stage \(C(2),f_5=3\) invisible equality frame, assume exactly four distinct truly cubic-dirty ghosts, in either the [nine-site early-return](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md) or [ten-site earliest-extra-zero](../dirk12-fifteen-rank3-invisible-ten-site-early-zero/README.md) high-site chronology. Suppose exactly three ghosts precede the first nonzero ordinary live clock \(a\), and the fourth, occurring before the next live clock \(b\), has numerical ordinary clock zero. **This subchart is impossible.** In particular all three exactly isolated real candidates for \(a\) in the [ordinary fourth-ghost projection](../dirk12-fifteen-rank3-invisible-ordinary-ghost-chronology/README.md) are excluded here. No entire high-site chart or unrestricted bound is claimed; real DIRK12 remains **15–16**.

This uses the genuine fourth ordinary row, its grade-five scalar nodal test, and a separate genuine grade-seven pure word. The ordinary ghost contribution reduces to an exactly determined two-mode polynomial before a coefficient prime is used. No output weight or unknown ghost amplitude is reduced modulo a prime, no individual weight positivity is used, and **\(\varepsilon_{12}\) is neither paid nor set to zero**. In fact the reduction allows the entire two-mode Jacobi plane containing the mixed reverse-derived \(\alpha,\gamma\).

## Coordinate and grade conventions

The first four nonzero ordinary live clocks \(a,b,c,e\) are four unique physical rows, the literal ordinary origin is live and is the only live row at ordinary numerical zero, and all ghosts are before \(b\). In the nine-site chart the only repeated live numerical clock belongs to the early reverse pair, physically near the ordinary end, so it does not interfere with this ordinary prefix. In the ten-site chart all nonterminal live numerical labels are distinct. Write \(C=\operatorname{diag}(\mathbf c)\), \(A\) for the literal ordinary matrix, and \(R=CA-AC-A^2\). Work in normalized ordinary clock \(X=\mathbf c/a\) and normalized matrix \(\bar A=A/a\), with \(\bar R=R/a^2\); scalar primitives \(J\) below are based at zero in this normalized variable. Set
\[
       x=b/a=2/5,\qquad y=c/a,\qquad t=e/a .
\]
The earlier genuine results give zero ordinary diagonals at \(a,b\), \(aL_6'(a)\ne0\), and
\[
\begin{gathered}
 P_a(a)=129888a^5-330000a^4+312000a^3-136800a^2+27800a-2015=0,\\
 D=2xy-x-3y^2+2y\ne0,\qquad
 \omega=\bar A_{cc}=y(x-y)(y-1)/(2D),\\
 (2x-1)D\,L_6'(ay)+y^2 P(x,y)L_6'(a)=0,\\
 P(x,y)= -10x^2+(20x^2+5x)y+(-18x^2-6x)y^2
                      +(6x^2+8x-3)y^3+(2-4x)y^4 .
\end{gathered}
\]
The last equation is the actual grade-six third-clock equation, not just a scalar quadrature identity. Its two inadmissible exact factors \(y-1,y-x\) are removed in forming the degree-five polynomial for genuine \(y\). Throughout \(a,y,y-1,y-x\ne0\). The degree-six state tests used below are the genuine ones in that proof.

## Eliminate the early ghost geometry over characteristic zero

Because the late ghost has numerical zero, all three earlier ghost clocks are nonzero. Let \(s_g=c_g/a\) at the early ghosts. The actual grade-three mask in the earlier proof gives early amplitudes
\[
      h_g=\kappa a^3 s_g P_2(s_g),\qquad P_2(X)=10X^2-12X+3,
      \qquad \kappa\ne0.
\]
The same proof gives the genuine affine correction to \(A\mathbf V\): write \(A\mathbf V=(JS_{\rm phys})(\mathbf c)+\mathbf hQ(\mathbf c)\) in the physical clock, \(S_{\rm phys}(X)=\kappa X(10X^2-12aX+3a^2)\). At the ordinary late zero, \(Q(0)=-2a/7\). The first three actual ghost entries of \(A\mathbf V\) vanish by chronology. Thus at their clocks, \(N(s_g)/P_2(s_g)=\lambda s_g+2/7\), where \(-Q(aX)/a=\lambda X+2/7\) and
\[
       N(X)=X(X-1)(5X-3)/2 .
\]
Set \(B_0(X)=N(X)-(\lambda X+2/7)P_2(X)\), \(C_0=5/2-10\lambda\). Its roots are exactly the three distinct \(s_g\), and \(C_0\ne0\): otherwise the degree is at most two but it has these three roots, making \(N\) a polynomial multiple of \(P_2\), contrary to their fixed coprimality. No \(s_g\) is zero or a root of \(P_2\), by distinctness from the late zero and \(h_g\ne0\).

For \(k=1,\ldots,6\), take partial fractions of \(X^{k-2}/[P_2(X)B_0(X)]\). The residue sum at the three roots of \(B_0\) is
\[
        M_k=\sum_g\frac{s_g^{\,k-2}}{P_2(s_g)B_0'(s_g)}.
\]
At either fixed root of \(P_2\), \(B_0=N\), so those residues are independent of \(\lambda\). There is also a pole at zero for \(k=1\), of residue \(-7/18\); for the first five cases the coefficient of \(X^{-1}\) at infinity is zero, and for \(k=6\) it is \(1/(10C_0)\). The exact constants are
\[
 (M_1,M_2,M_3,M_4,M_5,M_6)
      =(15/2,4,8/3,2,8/5,33/25+1/(10C_0)).
\]
For example the fixed-pole contribution is the leading coefficient of the affine remainder of \(X^{k-2}/N(X)\) modulo \(P_2\), divided by \(10\); for \(k=1\) use the inverse of \(X\) in this quadratic quotient. All inverses and values in this table are checked by the rational replay. The partial-fraction argument uses the distinct true ghost amplitudes but does not specialize them modulo a prime.

The physical \(\ell_g=1/(h_gD_4'(c_g))\), with \(D_4\) the four-ghost monic hull, gives for these early ghosts
\[
        \ell_g=\frac{C_0}{\kappa a^6 s_g^2 P_2(s_g)B_0'(s_g)} .
\]
The actual \(AC^2\mathbf h\) mode is \(\nu c_i L_6'(c_i)\) on live nonterminal rows. Its numerical read at \(a\) is \(\kappa a^6/(8C_0)\). To see this with the true row, the actual \(a\)-diagonal is zero and it integrates degrees through four exactly on \(0,s_g\) in normalized units. Their nodal polynomial \(V_4=XB_0/C_0\) has zero integral. The true row's evaluation of \(X^3 P_2(X)\), of degree five, therefore equals its exact integral minus \(10\int_0^1 X V_4(X)\,dX\), just polynomial division by \(V_4\). These integrals are \(1/60\) and \(-(1+2\lambda)/(120C_0)\), giving \(1/(8C_0)\). This does not assume degree-five *local* stage precision. Hence
\[
             \nu=\frac{\kappa a^5}{8C_0 L_6'(a)} .
\]
The genuine grade-six scalar discrepancy for quintic input is \(\eta X L_6'\) on nonterminal live rows. The earlier actual \(AC^2\mathbf V\) read at \(a\) gives
\[
          \frac{\eta}{a^5}
                      =\frac{1/(80C_0)-1/600}{L_6'(a)} .
\]
In degree five the \(1/(10C_0)\) in \(M_6\) cancels exactly with the \(1/(80C_0)\) here. This cancellation is between two actual ordinary mode coefficients and does not concern the unpaid global degree-twelve scalar moment.

## The geometry-free actual live row formula

Put
\[
 R_6(s)=L_6'(as)/L_6'(a),\qquad
 G_j(s)=s\big[L_j'(as)-R_6(s)L_j'(a)\big]\quad(j=5,7).
\]
After the literal zero ordinary \(a\)-tap to the late ghost, the two Jacobi tap modes yield a polynomial \(B\in\langle G_5,G_7\rangle\). For a scalar \(F\in XP_4\) (degree at most five) define
\[
 \mathcal I(F)=\int_0^1 F,\qquad
 \mathcal M(F)=8\int_0^1 F(X)/X\,dX-\tfrac12 [X]F .
\]
The true normalized numerical live part of the ordinary row at any nonterminal live scalar label \(s\) is
\[
           \mathcal A(F)(s)
             =JF(s)-sR_6(s)\mathcal I(F)-B(s)\mathcal M(F).
\]
Precisely, the left side sums \(\bar A_{ij}F(c_j/a)\) only over the ordinary live physical source rows, using their actual existing taps. To derive it, take the true scalar stage reads through input degree five. The \(C_0\)-normalized ν-mode ghost moments for \(X^k\), \(1\le k\le4\), are \(M_{k+1}/8=1/(k+1)\), and at \(k=5\) the just-paid \(\eta\) leaves \(33/(8\cdot25)+1/600=1/6\). The other ghost-mode moments are \(M_k=8/k-\tfrac12{\bf1}_{k=1}\), including \(k=5\). The late ghost is at \(X=0\), so there is no contribution to these positive-degree input scalars from its own literal coefficient. This gives the exact displayed formula without retaining the early ghost geometry or amplitude normalization. In particular no nonterminal *reverse* singleton is assumed pure-clean.

The polynomial \(B\) has exact readings
\[
    B(x)=3\,x^3(x-1)^2/2,\qquad
    B(y)=B(x)\theta,\qquad
    \theta=-\frac{y^3(y-1)^3(3x^2-2xy-2x+y)}
                         {x^3(x-1)^3D}.
\]
The first is the true late tap normalization: writing \(q=A_{b,g_*}\), one has \(q(A\mathbf V)_{g_*}=J^2 S_{\rm phys}(b)\), \((A\mathbf V)_{g_*}=-(2a/7)h_{g_*}\), and \(\ell_{g_*}^{-1}=h_{g_*}a^3(-6/7)/C_0\). Thus \(B(x)=C_0(q/a)/(\kappa a^6\ell_{g_*})=3x^3(x-1)^2/2\). The second is the actual third-to-second late tap ratio \(\theta=A_{c,g_*}/q\), evaluated from the true cubic primitives and the actual third diagonal in the preceding proof. These conditions determine \(B\) because the \(2\times2\) evaluation determinant of \(G_5,G_7\) on \(x,y\) is nonzero; the arithmetic replay certifies it is a unit at the coefficient prime for every base branch. Allowing any such \(B\) contains, and does not substitute for, the particular mixed \(\alpha/\gamma\) derived in either reverse chronology.

## Two literal fourth-row polynomials with exact factors removed

Let \(P_0(X)=X(X-1)(X-x)(X-y)\). The two polynomials \(\mathcal A(P_0)\) and \(\mathcal A(XP_0)\) both vanish at \(0,1,x,y\) **in characteristic zero**, by the actual preceding live rows: those scalar profiles vanish on every available live source at those rows, including their own numerical labels. The origin also follows directly from the factor \(s\) in the formula. Hence \(P_0\) divides both polynomials exactly. Form
\[
 d(s)=\mathcal A(P_0)(s)/P_0(s),\qquad
 E_5(s)=\mathcal A(XP_0)(s)/P_0(s)-s\,d(s).
\]
Both quotients are polynomials. At the actual fourth ordinary live row \(t\notin\{0,1,x,y\}\), the true scalar nodal read gives \(d(t)=\bar A_{ee}\) and \(E_5(t)=0\). The only live source at the fourth label for these profiles is its own physical diagonal. The degree bounds are \(\deg d\le3,\ \deg E_5\le4\).

Now use the actual [common grade-four mask](../dirk12-fifteen-rank3-invisible-third-ordinary-live/README.md) \(\mathbf Q\) (in normalized scalar units) with scalar profile \(W'\), \(W=X^2(X-1)^2(X-x)\). Numerically \(\mathbf Q\) is identically zero at ghosts and through the first \(a\)-row, and \(\bar A\mathbf Q\) is zero on ghosts and has value \(W\) at all live rows. Its actual twofold primitive at a live nonterminal clock \(s\) is therefore
\[
            V(s)=\mathcal A(W)(s)=JW(s)-s R_6(s)\mathcal I(W),
\]
where \(\mathcal M(W)=0\) since \(x=2/5\). This uses the actual numeric support of \(\bar A\mathbf Q\), and the true scalar input through degree five in the geometry-free row formula.

The actual pure grade-seven word \(\mathbf Z=\bar R(\bar A\mathbf Q)\) has nonterminal live profile \(\mathcal Z\in\langle G_5,G_7\rangle\): the genuine \(F_7\) profile is \(s\langle L_5'(as),L_6'(as),L_7'(as)\rangle\) and the word's value at the first live clock \(1\) is zero. Its exact observed values \(\mathcal Z(x)=0,\ \mathcal Z(y)=-\omega^2W(y)\) fix it in the same nonsingular two-mode interpolation. This is not a hypothesized extension of root order to a deweighted transpose.

At the fourth live row \(t\), the only prior nonzero source of \(\bar A\mathbf Q\) is the physical preceding \(y\)-row. The literal off-diagonal commutator coefficient on that source is \((t-y-\omega-d(t))\bar A_{e,c}\); the diagonal of \(\bar R\) is \(-d(t)^2\). Using \(V(t)=\bar A_{e,c}W(y)+d(t)W(t)\) yields the exact fourth-row requirement
\[
        (t-y-\omega)V(t)
            -d(t)\,[V(t)+(t-y-\omega)W(t)]-\mathcal Z(t)=0.
\]
The left side is a polynomial of degree at most nine. It has exact roots \(0,1,x,y\): at \(0,1,x\), \(V,W,\mathcal Z\) vanish by the actual prefix or their factors; at \(y\), \(V(y)=\omega W(y)\), so the \(d\)-bracket vanishes and the first term equals \(\mathcal Z(y)=-\omega^2W(y)\). Thus dividing by the monic \(P_0\) exactly gives an actual \(E_7\) of degree at most five, with \(E_7(t)=0\). This removes all these root factors *before* reduction, not by assuming an unknown clock distinct after reduction.

## Integral bounded reduction at 271

Use any finite place above \(271\) of the field of the scalar algebraic coordinates. In characteristic zero the leading coefficient of \(P_a\) is a \(271\)-unit, so \(a\) is integral at every such place. At \(271\) the polynomial splits into the five simple residues \(11,82,99,134,191\), each a unit and each with \(L_6'(a)\ne0\) after reduction. The cleared degree-seven equation for \(y\), divided by its exact factors \(Y-1,Y-x\), has leading coefficient a \(271\)-unit (its degree-seven leading coefficient was \(-3(2x-1)5544a^5\)). Thus \(y\) is integral too. The reversible nonzero coefficient guards for the residual two-clock quotient and two-mode solve, including \(y,y-1,y-x,D\) and the determinant on \(x,y\), all reduce to units in **every** irreducible branch checked below. Every coefficient used in \(B,V,\mathcal Z,d,E_5,E_7\) is then integral: the displayed scalar rational denominators are \(271\)-units, and polynomial division is by the monic integral \(P_0\).

The exact standalone certificate verifies all eleven irreducible factors of the five residual degree-five polynomials in \(y\), of total residue degree 25. It checks their products and irreducibility, then shows the reduced \(E_5,E_7\) have degrees four and five and gcd one in each branch. In particular the **actual \(E_5\) leading coefficient is a unit** in any number field branch (its degree never exceeds four). Any real \(t\) satisfying these equations is algebraic by \(E_5\), and integral above \(271\) by dividing its equation by that unit leading coefficient. Thus \(t\) has a finite reduction, which would have to be a common root of the two reduced polynomials over a residue extension. Their exact coprimality forbids this. This explicitly rules out both a degree-loss/infinity escape and a spurious assumption that actual distinct clocks remain distinct after reduction. The denominator checks concern only the forced algebraic scalar base, not coefficients of an unknown tableau.

## Replaying the calculation

    python3 -B verify-identities.py
    python3 -B verify.py

The first script checks the rational residue table, definite paid cancellations and shape constants. The second uses only the Python standard library; no floating-point arithmetic, factorization oracle, or reduction of unknown tableau data is used. The degree-seven live pure profile is justified by the genuine \(7+4=11\) pairing as in the third-live analysis. The overall stage-space argument is analytic with an exact finite certificate, not a complete native order-twelve proof.
