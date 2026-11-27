# Partial closure of a single invisible off-zero clock at strict SDIRK8

Consider a ten-stage strict SDIRK tableau of order at least eight over a characteristic-zero field. Let \(A,\boldsymbol b,\boldsymbol c,\boldsymbol g\) be its tableau, weights, clocks and quadratic residuals. Here **every physical stage with \(g_i\ne0\) has zero weight**, and all such stages share **one physical clock**. This is not the same as joint or per-clock cancellation of individually active weights. The active [one-clock family](../sdirk-eight-half-equal/README.md) is a different branch.

**Results.** There are at most four invisible physical off-zero rows; four is impossible. Three is impossible if their residuals are all equal or if the reverse pure degree-two line vanishes on those invisible coordinates. In the remaining three-row case with variable residuals and nonzero reverse restriction, precisely six active quadratic-zero rows and a detected cubic defect are also impossible. This leaves one or two invisible off-zero rows, or the stated narrower three-row branch; no conclusion on multiple invisible physical clocks or the unrestricted **10–11** stage interval.

## 1. Literal census and pure-support bounds

Use the saturated flags \(E_j,F_j,W_j,Z_j\) and
\[
 C=\operatorname{diag}(\boldsymbol c),\quad B=\operatorname{diag}(\boldsymbol b),
 \quad G=\operatorname{diag}(\boldsymbol g),\quad N=A-\gamma I,\quad
 M=CA-AC-A^2,\quad \boldsymbol h=N\boldsymbol g .
\]
Write \(L=\{i:g_i\ne0\}\), \(U=L^c\), \(\ell=|L|\), \(m=10-\ell\). We keep every index, including silent rows on either set. The first stage is in \(L\), so its sole off-zero clock is \(\gamma\), and it is silent. The first two nonfirst stages are literal zero rows at clocks \(a,b\) with nonzero \(h\) and distinct clocks not equal to \(\gamma\). Indeed \(c_2\ne c_1\) by the literal twin obstruction, so \(g_2=0\), and the [literal first-three identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) with \(g_2=0\) then give \(g_3=0\) and
\[
       a=\gamma(2+2t),\qquad
       b=\gamma(2-2t)\ \hbox{(star)}\quad\hbox{or}\quad
       b=\gamma(3+4t)\ \hbox{(arithmetic)},\qquad t^2=1/2 .
\]
The two strict taps into stage one are nonzero in both phases. The same polynomial first-three argument applies in characteristic zero without ordering.

Put \(\boldsymbol w=\boldsymbol b^{\mathsf T} M\), the nonzero spanning row of \(Z_2\), and \(r_2=\operatorname{rank}(Z_2|_L)\in\{0,1\}\). All scalar reverse rows are supported on \(U\) because the weights on \(L\) vanish. Hence \(\operatorname{rank}(W_2|_L)=r_2\). The [saturated support identity](../sdirk-eight-two-zero-line/README.md) gives
\[
               \dim(E_3\cap U)=m-4+r_2,\qquad
               \operatorname{rank}(E_3|_L)=\ell-r_2 .
\]
Its restriction to \(L\) is spanned by \(\boldsymbol1,\boldsymbol g,\boldsymbol h\) because the physical clock is constant there and \(F_3=\langle\boldsymbol g,\boldsymbol h\rangle\). Thus \(\ell\le4\); \(\ell=4\) requires \(r_2=1\), rank three and variable residuals on \(L\).

Let \(e=\operatorname{rank}(E_2|_L)\), equal to one for a constant residual and two for a variable residual. The analogous support identity at \(W_3,E_2\) gives
\[
             \operatorname{rank}(Z_3|_L)=\operatorname{rank}(W_3|_L)=\ell-e.
\]
Because \(Z_3\) has dimension two, if \(\ell-e=2\) it has no nonzero row supported on \(U\). Two useful supported rows in \(Z_3\) are \(\boldsymbol h^{\mathsf T}B\) (paid pairing against \(E_4\)) and \(\boldsymbol w(C-\gamma I)\) (the right-multiplication pure recurrence). Hence both vanish when \(\ell-e=2\). The terminal weight \(b_{10}\ne0\) by stage trimming, \(c_{10}=1-\gamma\) by \(D(1)\), and \(w_{10}=-\gamma^2 b_{10}\ne0\) by triangularity. It follows that \(\gamma=1/2\) and \(\boldsymbol w\) is supported on this clock.

The vanishing \(\boldsymbol h^{\mathsf T}B=0\) makes the two front zero rows silent. For \(\ell=4\) there are at most four active rows; ordinary precision requires four distinct ordinary sites, so these are exactly the four shifted Legendre nodes. The terminal site \(1/2\) is not such a node. For \(\ell=3,e=1\) there are at most five active rows. Four give the same contradiction. With five, the two front zero rows are the only silent zeros. Since \(\boldsymbol w\) annihilates \(\boldsymbol1,\boldsymbol g\) and the nonzero residual is constant on \(L\), \(\sum_{i\in L} w_i=\sum_{i\in U} w_i=0\). Besides the terminal row, another zero row must therefore have \(w_i\ne0\) at \(c_i=1/2\). It is active, since the two silent zeros are at \(a,b\ne1/2\). Five physical active rows with a repeated clock have at most four ordinary sites. Precision forces exactly four, including \(1/2\), again impossible.

## 2. A three-row variable residual with \(r_2=0\)

Here \(e=2\). The space of rows in \(Z_3\) supported on \(U\) is one-dimensional. Because \(r_2=0\), it contains \(\boldsymbol w,\boldsymbol w C\), so \(\boldsymbol w(C-xI)=0\), \(x=c_{10}\), and the row is supported on the terminal clock; \(\boldsymbol h^{\mathsf T}B\) is either zero or proportional to \(\boldsymbol w\).

Two external chronology checks used below are as follows.

* The penultimate weight is nonzero and \(c_9\ne c_{10}\). Otherwise \(D(1)\) kills its sole later strict tap, producing a silent or proportional coordinate in every reverse word, contrary to saturation. If \(b_8=0\) and \(w_8=0\), the two equations \(D(1)\) and
  \[
      -\boldsymbol w/2=\boldsymbol b^{\mathsf T}(I-C)A
                                   -\tfrac12\boldsymbol b^{\mathsf T}(I-C)^2
  \]
  at column eight kill both later strict taps, since the terminal two weights are nonzero and their clocks differ. Thus a silent eighth stage must have \(w_8\ne0\) on the terminal clock.
* When \(b_8,b_9,b_{10}\ne0\), normalize just that trailing three-row block by its weights (no invertibility of \(B\) elsewhere is assumed). The actual reverse quadratic defect is \(-w_i/(2b_i)\) there, hence nonzero at the first reflected row and zero at its second (since \(c_9\ne x\)). The [literal reverse three-row identities](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md) now give \(c_9=1-\gamma A'\), \(c_8=1-\gamma B'\), where \(A',B'\) have the same two phase formulas with an independent sign of \(t\). These are distinct from each other and from \(x\). They cannot both be Gauss: the shifted Legendre polynomial \(L_4\) is invariant under \(X\mapsto1-X\), and the exact gcd of \(L_4(\gamma A')\), \(L_4(\gamma B')\) as polynomials in \(\gamma\) is one in both phases.

If \(B\boldsymbol h\ne0\), the active defect is supported on \(x\). There are at least six active zero rows: the ordinary cubic scalar span has a nonsingular four-by-four Hilbert Gram, and its orthogonal complement on the active coordinates is nondegenerate. A nonzero isotropic \(h\) cannot lie in a complement of dimension zero or one. Since \(h\) is nonzero at both different front clocks, one of those front rows must be silent; there are exactly six active zeros. At least two active rows on \(x\) have nonzero defect, one front row and the terminal. If exactly two active rows lie on \(x\), the paid local \(h,h^2\) sums force equal nonzero defects and opposite weights, so all four other active sites are Gauss. If three or more lie on \(x\), there are at most four sites in total; ordinary rank forces exactly four Gauss sites, hence again all outside \(x\) are Gauss. The sole silent zero is a front row, so an eighth-stage silence would be off-zero and have \(w_8=0\), impossible. Thus the anchored trailing pair \(c_8,c_9\) would be Gauss, contrary to the exact gcd.

If \(B\boldsymbol h=0\), both front zeros are silent. Also \(F_4|_U\) has rank \(4-e=2\) and is spanned by the independent restrictions of \(\boldsymbol h,C\boldsymbol h\), so every active zero pays all four clean moment reads. There are four or five active zero rows.

* **Four active.** All are at Gauss nodes, so \(\gamma\) and \(x=1-\gamma\) are Gauss. Active \(b_8\) would give the excluded Gauss pair. A silent stage eight has \(w_8\ne0\), is therefore a zero at \(x\) (not an off-zero row, where \(w\) vanishes), and is the sole extra silent zero besides the front pair. The earliest active zero is before stage eight. Its strict feeds can see only \(\gamma,a,b\) prior to its own diagonal. The cubic nodal moment at its clock \(z\) is
  \[
           \int_0^z (X-\gamma)(X-a)(X-b)\,dX
                       -\gamma(z-\gamma)(z-a)(z-b)=0 .
  \]
  It fails at all Gauss \((\gamma,z)\) in both front phases. The exact computation inverts this cubic read in the fixed 32-dimensional quotient for the two Gauss-root relations and \(t^2=1/2\).
* **Five active.** Only the two front zeros are silent, so \(b_8\) is active. Repetition among the five active rows would leave four Gauss sites and give the excluded trailing pair. Thus all five are distinct. Since \(\boldsymbol w\) annihilates \(\boldsymbol1\) and is solely at \(x\), a second row besides the terminal must be there. It is one of the two front silent zeros, so \(\gamma=1/(1+A_0)\) with \(A_0=a/\gamma\) or \(b/\gamma\). This is an exact finite set. Set \(P_3(X)=(X-c_{10})(X-c_9)(X-c_8)\) at the three pegged trailing sites. The two unknown ordinary sites give a quadratic in the kernel of \([I(X^{i+j}P_3)]_{i,j=0}^2\), using only precision seven. Its determinant is nonzero in all but one of the sixteen phase choices. In the exceptional choice the principal two-by-two matrix is invertible, and the reconstructed residual quadratic is coprime to the same literal earliest-active cubic. This cubic applies because the only silent zeros before the first active one are \(a,b\), and any intervening off-zero donors have clock \(\gamma\).

## 3. A six-active obstruction when \(r_2=1\) and \(e=2\)

Suppose \(\ell=3\), \(B\boldsymbol h\ne0\) and exactly six zero rows are active. In the two-dimensional orthogonal complement of the nondegenerate cubic scalar span on those rows, \(h\) is nonzero and isotropic. Both \(Ch\) and \(L_4(c)\) are in this complement and orthogonal to \(h\) by paid pure pairings, so both restrictions are proportional to \(h\). Hence the active nonzero defect is supported on one clock \(r\), and all other active zero clocks are Gauss. Exactly one of the two front zeros is silent, and the other has clock \(r\ne\gamma\).

If \(\gamma=1/2\), the active terminal zero at the non-Gauss clock \(\gamma\ne r\) is already a contradiction. Otherwise \(\boldsymbol w(C-\gamma I)\) is nonzero at the terminal coordinate, is supported on \(U\), and spans the supported \(Z_3\) line. It is therefore proportional to \(\boldsymbol h^{\mathsf T}B\) and forces \(r=c_{10}\) and \(\boldsymbol w\) supported on the two clocks \(r,\gamma\). If \(c_9\ne\gamma\), then \(w_9=0\) since \(c_9\ne r\). But \(\{\boldsymbol w,\boldsymbol w N\}\) is a basis of \(Z_3\), detected at rows ten and nine by the nonzero last strict tap. The row \(\boldsymbol w(C-rI)\in Z_3\) would have both terminal coordinates zero, hence be zero, contrary to the nonzero invisible restriction at \(\gamma\ne r\). Thus \(c_9=\gamma\), an active clock outside \(r\), so \(\gamma\) is Gauss. The equation \(r=a\) or \(b\) together with \(r=1-\gamma\) again gives \(\gamma=1/(1+A_0)\), and the exact scalar test \(L_4(1/(1+A_0))\ne0\) contradicts this in all front choices.

The remaining \(\ell=3\) variable-residual branch has \(r_2=1\) and either \(B\boldsymbol h=0\), or all seven physical zero weights nonzero. If \(B\boldsymbol h\ne0\) there is no case with fewer than six active zeros, by the cubic Gram argument. No result is asserted for the one- or two-invisible-row charts.

## Verification

Run `python3 check_earliest_gauss.py` and `python3 check_tail.py` with Python 3 and `sympy==1.14.0`. They use rational coefficient and exact quadratic quotient arithmetic. The [Lean receipts](../../lean/RKCert/ReviewedNative/SDIRK8SilentClockReceipts.lean) check the literal three-clock integration gate, the midpoint exclusion, and the two explicit Gauss cubic ideal identities. The support rank, chronology and remaining exact tail calculation are source-level.
