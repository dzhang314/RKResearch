# DIRK12/15: geometry-free finite ordinary prefixes in both high-site reverse charts

In the real ordinary fifteen-stage order-twelve DIRK \(C(2),f_5=3\) weighted-invisible cubic frame, assume exactly four distinct cubic-dirty ghosts and either the [nine-site early reverse return](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md) or [ten-site earliest extra reflected zero](../dirk12-fifteen-rank3-invisible-ten-site-early-zero/README.md) chronology. Then the first four nonzero ordinary live clocks \((a,b,c,e)\) belong to a **finite algebraic set**, without any restriction on the numerical ghost clocks or whether the fourth ghost is early or late. The first three ordinary live ratios use only genuine explicit scalar gates, and for each actual \((a,b,c)\) there are at most four choices for \(e\).

This makes the earlier finite-prefix arguments independent of ghost parameterizations. We do not compute the finite set, assert it empty, or claim a new unrestricted lower bound. Real DIRK12 remains **15–16**. In particular these two reverse chronologies are hypotheses; do not assume that every nine-site return is early or that every ten-site grid has an early extra reflected zero. No scalar degree-twelve moment is paid.

## Two cardinal modes from the two actual live rows

Use \(T=\mathbf c/a\), \(\bar A=A/a\), \(\bar R=(CA-AC-A^2)/a^2\), \(J\) scalar integration from zero, and \(\mathcal I(F)=JF(1)\). Write \(x=b/a,\ y=c/a,\ t=e/a\). The actual first four nonzero ordinary live rows are physically unique in the two stated reverse chronologies. The unique repeated nonterminal label in the nine-site case is the early reverse pair, hence is near the ordinary end and cannot include any of these first ordinary rows or the literal live origin. The ten-site case has no such pair. The only ordinary live source at clock zero in the first four rows' prefixes is therefore the literal origin. The [ordinary chronology proof](../dirk12-fifteen-rank3-invisible-four-ghost-variable-grid/README.md) forces all four ghosts before \(b\), and at least three before \(a\).

Write \(p_g=c_g/a\), \(D_g\) for the monic hull of the four ghost clocks in physical units, and \(\ell_g=1/[h_g D_g'(a p_g)]\). Use the [true ordinary tap-rank and moment result](../dirk12-fifteen-rank3-invisible-four-ghost-variable-high-sites/tap-rank-and-moments.md). On a nonterminal ordinary live row at normalized clock \(s\), its normalized ghost taps have the exact form
\[
             \bar A_{s,g}=\ell_g[r(s)+k(s)p_g],
 \qquad r(s)=s[\mu L_6'(as)+\alpha L_5'(as)+\gamma L_7'(as)],
 \quad k(s)=\nu a s L_6'(as).
\]
Here \(\nu\ne0\), and \(\gamma\ne0\) in the two stated reverse chronologies by their actual mixed grade-six relations, with the real unpaid \(\varepsilon_{12}\) retained. The two actual \(a,b\) ghost rows have exact rank two, so their two coefficient rows \((r(1),k(1))\), \((r(x),k(x))\) are independent. Indeed \(\boldsymbol\ell\) and \((p_g\ell_g)_g\) are independent for distinct dirty clocks.

For scalar inputs \(F\in TP_4\) (zero constant, degree at most five) define
\[
 \mathcal M(F)=\sum_g\ell_g F(p_g),\qquad
 \mathcal K(F)=\mathcal M(TF)-\epsilon [T^5]F.
\]
The single \(\epsilon\) absorbs the true degree-five-input scalar primitive discrepancy, since it is a fixed scalar times \(s L_6'(as)\) on live nonterminal rows by \(F_6\), and \(\nu a\ne0\). Therefore the **literal ordinary live-only read** is
\[
                 \mathcal A(F)(s)=JF(s)-r(s)\mathcal M(F)-k(s)\mathcal K(F).
\]
This is just the full actual row minus its four ghost taps, not a reduced replacement tableau.

By the actual rank-two determinant, there are unique modal polynomials \(U,V\) such that
\[
       (r(s),k(s))=U(s)(r(1),k(1))+V(s)(r(x),k(x)).
\]
They have the exact cardinal readings \(U(1)=V(x)=1,\ U(x)=V(1)=0\). This uses the rank of the **literal taps**, even if one actual ghost clock is numerical zero or coincides with a live clock.

## If the first ordinary clock is not a Legendre root

Assume \(L_6'(a)\ne0\). If the fourth ghost is late, the earlier [fourth-ghost proof](../dirk12-fifteen-rank3-invisible-ordinary-ghost-chronology/README.md) gives zero \(a,b\) diagonals and an actual common ghost-zero grade-four mask \(\mathbf Q\) with scalar \(W'\), \(W=T^2(T-1)^2(T-x)\). If all ghosts precede \(a\), the [paired affine mask proof](../dirk12-fifteen-rank3-invisible-no-late-affine-masks/README.md) gives zero \(b\)-diagonal and the same mask; the \(a\)-diagonal may be nonzero, but is not used below. Those arguments include the numerical-zero ghost fork: the scalar affine-mask space is still two-dimensional by the bare quartic, as in the [zero-ghost extension](../dirk12-fifteen-rank3-invisible-no-late-zero-ghost/README.md).

For every \(F\in TP_4\) with \(F(1)=0\), **both** actual live-only reads at \(a,b\) are zero. These inputs vanish at the literal origin and the first live nonzero \(a\), and the second live row has zero diagonal. Thus the two genuine ghost-functional readings are exactly \(JF(1),JF(x)\). Put
\[
       R(s)=\frac{k(s)}{k(1)}=\frac{sL_6'(as)}{L_6'(a)},\qquad \rho=R(x),
       \qquad \mathcal D(F)=JF(x)-\rho\mathcal I(F).
\]
The second tap coordinate gives \(U(s)+\rho V(s)=R(s)\). Hence on the whole four-dimensional input space \(F(0)=F(1)=0,\ \deg F\le5\),
\[
          \boxed{\mathcal A(F)(s)=JF(s)-R(s)\mathcal I(F)-V(s)\mathcal D(F).}
\]
Neither ghost moment functional nor ghost amplitudes appear. The polynomial \(V\) lies in \(\langle G_5,G_7\rangle\), where
\(G_j(s)=s[L_j'(as)-L_6'(as)L_j'(a)/L_6'(a)]\).
Its top coefficient is nonzero: \(V\) is the nonzero \(b\)-normalized multiple of \(r(s)-r(1)R(s)\), and the actual \(L_7'\) coefficient of \(r\) is nonzero. Consequently \(\deg V=7\).

The common mask gives the already-paid exact \(a,x,y\) restrictions in the [third ordinary live calculation](../dirk12-fifteen-rank3-invisible-third-ordinary-live/README.md): \(x\notin\{0,1,1/2\}\),
\[
 \rho=\frac{x^4(2x^2-6x+5)}{2x-1},\quad
 D=2xy-x-3y^2+2y\ne0,\quad
 \omega=\bar A_{cc}=\frac{y(x-y)(y-1)}{2D}\ne0,\quad
 R(y)=-\frac{y^3 P(x,y)}{(2x-1)D}.
\]
The same paid equations fix at most five \(a\) for any \(x\), and at most five \(y\) for each \((x,a)\), by the exact discarded roots and leading coefficients in the source. Test \(Q_x=T(T-1)(T-x)\) at the true \(y\)-row. Its sole nonzero live source there is the actual diagonal \( \omega Q_x(y)\). Direct integration gives
\[
 \mathcal D(Q_x)=-\frac{x^3(x-1)^3}{6}\ne0,\qquad
 V(y)=\frac{JQ_x(y)-R(y)\mathcal I(Q_x)-\omega Q_x(y)}{\mathcal D(Q_x)}
      =-\frac{y^3(y-1)^3(3x^2-2xy-2x+y)}{x^3(x-1)^3D}.
\]
This uses only the actual third row and fixes \(V(1)=0,V(x)=1,V(y)\) independently of ghost geometry.

The actual pure grade-seven word \(Z=\bar R(\bar A\mathbf Q)\) has first three live readings \(0,0,-\omega^2 W(y)\) and belongs to the same anchored two-mode span. The span is nonsingular at \(x,y\): two true ghost columns \(A\mathbf e_g\in F_7\) have independent first two live readings, and the actual \(Z\) is zero on both of those rows and nonzero at \(y\). This uses the genuine \(7+4=11\) pure space, not a reverse local-precision assumption.

Now take \(P_0=T(T-1)(T-x)(T-y)\) and the three test inputs \(P_0,TP_0,W\), all supported in the four-dimensional scalar domain above. Form
\[
 \begin{split}
 d&=\mathcal A(P_0)/P_0, \quad E_5=\mathcal A(TP_0)/P_0-Td,\quad
 L=\mathcal A(W),\\
 E_7&=\bigl[(T-y-\omega)L-d(L+(T-y-\omega)W)-Z\bigr]/P_0 .
 \end{split}
\]
They are exact on actual prefixes by the true previous row readings and the actual commutator argument in the [late-zero proof](../dirk12-fifteen-rank3-invisible-late-zero-exclusion/README.md). In particular \(d(t)\) is the actual fourth diagonal and \(E_5(t)=E_7(t)=0\). All ghosts are before \(b\), so in \(\bar A\mathbf Q\) there are no earlier nonzero sources at the actual fourth row other than \(y\); the own \(t\)-source is its diagonal. Its earlier zero ghost entries follow by causality since the whole \(\mathbf Q\) prefix is zero through \(a\). The row identity therefore pays the same true \(R(AQ)\) word as before.

For algebraic transfer, on the basis \(T^j(T-1),j=1,2,3,4\) the identities \(\mathcal D(F)=B(x)\mathcal M_z(F)\) and \(V(y)=B(y)/B(x)\) hold as exact rational functions, with the scalar \(B,\mathcal M_z\) of the [earlier late finite projection](../dirk12-fifteen-rank3-invisible-late-finite-projection/README.md). This is an identity of the whole scalar formulas, not a physical late-ghost requirement in the no-late case. Thus the two fourth polynomials, defined by monic Euclidean quotients in the finite coefficient algebra, specialize **exactly** to the archived prime-\(271\) degree-(4,5) coprime receipt at \(x=2/5\). Its nonzero generic norm proves finite \(x\) for every nonroot geometry. The specialization need not itself be admissible in the physical no-late chart.

For completeness, on any actual prefix the numerator \(P_0E_5\) is
\[
 -J^2P_0-R(T)(I_1-TI_0)-V(T)(D_1-TD_0),
 \qquad I_i=\mathcal I(T^iP_0),\quad D_i=\mathcal D(T^iP_0).
\]
If it vanished identically, the degree-eight coefficient forces \(D_0=0\). Dividing by \(T\) then puts \(J^2P_0/T\) in the neighboring Jacobi span \(\langle L_5'(aT),L_6'(aT),L_7'(aT)\rangle\). Its degree is five, so no \(L_7'\) component is possible; its double zero at zero contradicts the nonsingular two-jet determinant \(7560a\) of the remaining modes. Thus the actual \(E_5\) is nonzero of degree at most four at every admissible prefix, including exceptional coefficient specializations.

### The nonzero-diagonal fourth clock is now the same in all these geometries

Subtract \(\rho\) times the actual \(a\)-modal equation from the actual \(b\)-modal equation for \(F(0)=F(1)=0\). It gives
\[
                (r(x)-\rho r(1))\mathcal M(F)=\mathcal D(F).
\]
The multiplier is nonzero by the actual two-row rank. The genuine grade-five ghost-zero mask criterion \(\mathcal M(F)=0\) is therefore exactly \(\mathcal D(F)=0\) throughout this common domain. Its proof is the same four-point divided difference: \(F(p_g)/h_g\) is a quadratic on the four ghosts if and only if \(\sum_g\ell_g F(p_g)=0\). This continues to hold with a ghost/live overlap or one ghost at zero.

Consequently the true fourth-diagonal split from the [late-clock proof](../dirk12-fifteen-rank3-invisible-late-fourth-diagonal/README.md) transfers. In particular a nonzero \(d(t)\) forces
\[
            2xy-x-y\ne0,\qquad t=\frac{x(y-1)}{2xy-x-y}.
\]
Indeed \(\mathcal D(P_0),\mathcal D(TP_0)\) are fixed nonzero multiples of the earlier moments, with the same possible zero in the first and the same nonzero second. Choose their kernel combination of \(P_0,TP_0\). Its actual corrected grade-five vector is zero at all ghosts and first three nonzero live rows. Its genuine commutator, zero there by chronology, is globally zero on nonterminal live rows by the three-mode rank; the fourth diagonal term forces the scalar kernel combination to vanish at \(t\). If \(d(t)=0\), the true equations of degrees at most \(2,3,3\) also transfer, by the same rescaling identity of the two scalar functionals on \(P_0,TP_0,W\). This does not assert that either real branch is empty.

## If the first ordinary clock is a Legendre root

Assume \(L_6'(a)=0\). The actual late-ghost lemma makes this impossible with only three earlier ghosts, so all four are before \(a\). The genuine first-root affine-mask proof gives zero actual \(a\)-diagonal and mask \(W'=[T^2(T-1)^2(T-1/2)]'\), whether or not one ghost is at zero.

Now \(k(1)=0\), \(r(1)\ne0\), and \(k(x)\ne0\) by the true two-row rank. At the actual first live row, every \(F\in TP_4\) has zero live-only read (the only possible positive-degree live source is its own zero diagonal). Its true scalar quintic error is zero because \(L_6'(a)=0\). Therefore
\[
                        r(1)\mathcal M(F)=\mathcal I(F)
                 \quad\text{for all }F\in TP_4.
\]
This holds independently of all ghost clocks and amplitudes, not only at the specific earlier Lobatto ghost geometry. In degree at most four it also gives \(r(1)\mathcal M(TF)=\mathcal I(TF)\); in degree five their difference is just a scalar times \([T^5]F\). Hence after rescaling \(r,k\) by \(1/r(1)\) and absorbing the last difference into the quintic correction, the genuine live-only functional is exactly
\[
                  \mathcal A(F)(s)=JF(s)
                 -\widetilde r(s)\mathcal I(F)
                 -\widetilde k(s)\bigl[\mathcal I(TF)-\widetilde\epsilon[T^5]F\bigr],
\]
with \(\widetilde r(1)=1\), \(\widetilde k\) proportional to \(sL_6'(as)\), and nonzero top \(L_7'\) coefficient. These are precisely the actual scalar/grade premises used after the first modal formula in the [first-root finite projection](../dirk12-fifteen-rank3-invisible-no-late-first-root-projection/README.md). Its literal second diagonal \(W(x)/W'(x)\), second and third scalar solves, and genuine two-source fourth commutator now apply without any ghost-geometry hypothesis. Therefore it gives finite \((x,a,y,t)\) for all no-late first-root prefixes, and its [prime-\(43\) half-clock subchart exclusion](../dirk12-fifteen-rank3-invisible-no-late-half-clock/README.md) is valid for every such geometry.

## Verification scope

    python3 -B verify.py

The script checks the geometry-free rational factors, the four basis identities to the archived late operator, the two-jet guard, and the diagonal split constants. The earlier independent prime-271 and prime-43 replays are unchanged. The portable native scalar companion separately checks the two-row substitution and moment elimination; none of this claims a complete native rooted-tree theorem for all DIRK12.
