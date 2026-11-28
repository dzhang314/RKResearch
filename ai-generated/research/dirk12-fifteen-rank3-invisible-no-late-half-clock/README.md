# DIRK12/15: exclusion of the no-late zero-ghost half-clock at a first Legendre root

Consider real ordinary fifteen-stage order-twelve DIRK, \(C(2),f_5=3\), in the weighted-invisible four-distinct-cubic-dirty-ghost equality face, with either the [nine-site early reverse return](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md) or [ten-site earliest extra reflected zero](../dirk12-fifteen-rank3-invisible-ten-site-early-zero/README.md) chronology. Suppose all four ghosts precede the first nonzero ordinary live clock \(a\), the ghost at ordinary numerical zero is physically third, \(L_6'(a)=0\), and the next nonzero ordinary live clock is \(b=a/2\). **This precise subchart is impossible.** It does not settle other \(b/a\) ratios, the last-zero placement, or the full DIRK12/15 question. The real interval remains **15–16**.

This is an actual fourth-row test with exact coefficient arithmetic. All quantities reduced modulo \(43\) are forced algebraic scalar coordinates; no approximation, no reduced unknown tableau coefficient, no assumption of positive physical weights, and no setting of the actual unpaid \(\varepsilon_{12}\) is used.

## The fixed ordinary ghost moments

Use the [exact no-late third-zero calculation](../dirk12-fifteen-rank3-invisible-no-late-zero-ghost/README.md). In \(T=\mathbf c/a\) coordinates the three nonzero ghost clocks are \(1,(5-\sqrt5)/10,(5+\sqrt5)/10\), with the ghost at \(1\) the physically fourth. All occur before the literal first nonzero live row \(a\); the two physical rows at that clock are different. The first live diagonal is zero. The nonzero-ghost physical amplitudes are \(\kappa H(p_g)\), where \(\kappa\ne0\) is common and
\[
 H(T)=T^2-\tfrac65 T+\tfrac3{10},\qquad
 D_3(T)=(T-1)(T^2-T+\tfrac15),\qquad D_4=TD_3.
\]
In fact the unique masked cubic from that earlier result has normalized monic profile \(TH(T)\), obtained by fitting \(p_gh_g\) at the nonzero ghosts. The numerical-zero ghost has nonzero amplitude but does not contribute to positive-degree scalar input moments. The exact ghost moments for \(j=1,\ldots,6\) are
\[
 \sum_{p_g\ne0}\frac{p_g^j}{H(p_g)D_4'(p_g)}
     =(300,200,150,120,100,86)_j.
\]
Indeed \(H^{-1}\bmod D_3=10(30T^2-40T+11)\), and barycentric interpolation at the three roots gives the coefficient of \(T^2\) of \(T^{j-1}H^{-1}\bmod D_3\). For \(j\le5\) this is \(600/(j+1)\); for \(j=6\) it is \(600/7+2/7\).

Denote by \(J\) the scalar primitive based at ordinary normalized zero and by \(\mathcal I(F)=(JF)(1)\). The actual ordinary live-only row of the normalized matrix \(\bar A=A/a\) acts on any \(F\in TP_4\) as
\[
              \mathcal A(F)(s)=(JF)(s)-r(s)\mathcal I(F)-k(s)\mathcal K(F),
 \qquad       \mathcal K(F)=\mathcal I(TF)-\epsilon [T^5]F .
\]
Here \(P_j\) denotes polynomials of degree at most \(j\),
\[
      r(s)\in s\langle L_5'(as),L_6'(as),L_7'(as)\rangle,\qquad
      k(s)=\lambda sL_6'(as),\quad \lambda\ne0 ,
\]
and \(\epsilon\) is initially a constant. To see this, subtract the four ghost contributions from the genuine scalar primitive through input degree five. The [actual ordinary Jacobi tap profile](../dirk12-fifteen-rank3-invisible-four-ghost-variable-high-sites/tap-rank-and-moments.md) has coefficients
\(\ell_g[(\mu+\nu a p_g)sL_6'(as)+\alpha sL_5'(as)+\gamma sL_7'(as)]\) in \(\bar A\), with physical \(\ell_g=1/(h_g\,a^3D_4'(p_g))\). The constant-in-ghost-clock profile pays \(r(s)\mathcal I(F)\) by the first five moments, and the linear-in-ghost-clock profile pays \(k(s)\mathcal I(TF)\) except for the single fixed excess at degree five. The actual scalar quintic discrepancy is also a multiple of \(sL_6'(as)\) by genuine \(F_6\); combine it with this excess to define the displayed \(\epsilon\). In particular \(\lambda=600\nu a/(\kappa a^3)\ne0\) by the exact ghost tap rank. The left side sums the **literal ordinary live taps only**, not a modified tableau.

## The first three actual live rows

At the first nonzero live clock \(s=1\), \(k(1)=0\) and \(r(1)=1\), since its diagonal is zero and the earlier live inputs vanish. Put \(x=b/a=1/2\), \(y=c/a\) for the third distinct ordinary live nonzero clock. The first four nonzero ordinary live rows are physically unique and the live ordinary origin is the only live row at ordinary numerical zero in the two reverse chronologies.

By the [first-Legendre-root two-row case](../dirk12-fifteen-rank3-invisible-no-late-affine-masks/README.md), the true \(b\)-diagonal is \(W(x)/W'(x)=0\), where
\[
                       W(T)=T^2(T-1)^2(T-\tfrac12).
\]
The exact rank-two first \(a,b\) ghost taps force \(L_6'(b)\ne0\), since \(L_6'(a)=0\) and one Jacobi mode alone cannot give rank two. Thus \(k(x)\ne0\). For \(Q_x=T(T-1)(T-x)\), the actual \(b\)-row outputs of \(Q_x,TQ_x,T^2Q_x\) are zero on its live support. The two tests of degrees three and four solve the two modes at \(x\); the third fixes the quintic correction:
\[
                  r(x)=23/16,\qquad k(x)=-15/8,\qquad \epsilon=-1/5040 .
\]
These are exact two-by-two moment equations, with determinant \((5x^2-5x+1)/3600\) before substituting \(x=1/2\).

At the actual next row \(y\), the live-only moments of \(Q_y=T(T-1)(T-x)(T-y)\) and \(TQ_y\) are both zero. Write \(D_y=6y^2-6y+1\). Their two-by-two coefficient system has determinant \(-D_y/86400\) in this half-clock. The numerator for \(k(y)\) obtained by the adjugate is nonzero for \(y\ne0,1\) (it is \(y^3(y-1)^3/1440\)). Thus \(D_y\ne0\) on any actual tableau, and
\[
 \begin{split}
 r(y)&=-y^3(24y^4-114y^3+204y^2-165y+50)/D_y,\\
 k(y)&=-60y^3(y-1)^3/D_y .
 \end{split}
\]
Because \(k(s)=k(x)sL_6'(as)/(xL_6'(ax))\), the actual third-clock equation is
\[
          (6y^2-6y+1)L_6'(ay)-16y^2(y-1)^3 L_6'(a/2)=0.
\]
Its factors \(y-1,y-1/2\) are exact and invalid in the genuine chronology; the first uses \(L_6'(a)=0\), and the second follows by evaluating the displayed polynomial. The residual is degree five with nonzero leading coefficient \(6\cdot5544a^5\).

## Genuine grade-seven fourth-row gate

The actual ghost-zero grade-four mask \(\mathbf Q\) of scalar profile \(W'\) exists by the earlier first-Legendre-root proof. It has zero numerical values at \(a\), the literal origin and all ghosts. Its genuine primitive \(\bar A\mathbf Q\) is zero on ghosts by causality, and has profile \(W\) on live rows by \(F_5\). Write \(\bar R=(CA-AC-A^2)/a^2\). The actual pure grade-six word \(\bar R\mathbf Q\) has no ghost values by causality and is zero at \(b\) because the only possible nonzero input there is its own stage, whose diagonal is zero. Its live profile lies on the true \(sL_6'(as)\) line with \(bL_6'(b)\ne0\), so \(\bar R\mathbf Q=0\). At \(y\), only the \(b\)-row and the own diagonal can contribute to \(\mathbf Q\). Its genuine primitive and zero commutator give the exact actual third diagonal
\[
                    \omega=\bar A_{cc}=\frac{y(y-1)(2y-1)}{2D_y}\ne0 .
\]
This is the same literal tap elimination as in the [third ordinary live calculation](../dirk12-fifteen-rank3-invisible-third-ordinary-live/README.md): multiply its primitive row by \(y-x-\omega\) and subtract its commutator row. The resulting ratio is \((y-x)W(y)/(W(y)+(y-x)W'(y))\).

The genuine pure grade-seven state \(\bar R(\bar A\mathbf Q)\) has live nonterminal profile \(Z\in s\langle L_5'(as),L_6'(as),L_7'(as)\rangle\) by the true \(7+4=11\) band. Its literal reads at \(1,x,y\) are \(0,0,-\omega^2 W(y)\); the last is nonzero. Evaluation of this mode space at \(1,x,y\) is nonsingular: \(r(1)=1\), \(k(1)=0\), \(k(x)\ne0\), and \(Z\) has its first nonzero value at \(y\). Thus both \(r\) and \(Z\) are uniquely known from their three displayed readings, and \(k\) was known separately.

Let \(P_0(T)=T(T-1)(T-x)(T-y)\), \(t=e/a\) be the fourth ordinary nonzero live clock and put
\[
 \begin{split}
 d(T)&=\mathcal A(P_0)(T)/P_0(T),\\
 E_5(T)&=\mathcal A(TP_0)(T)/P_0(T)-Td(T),\quad V=\mathcal A(W),\\
 E_7(T)&=\frac{(T-y-\omega)V-d[V+(T-y-\omega)W]-Z}{P_0(T)} .
 \end{split}
\]
They are exact polynomial quotients in characteristic zero. The first two dividends vanish at the earlier rows since their possible ordinary live inputs vanish; the last vanishes at \(0,1,x\) by the true values of \(W,V,Z\), and at \(y\) by \(V(y)=\omega W(y)\), \(Z(y)=-\omega^2W(y)\). At \(t\), the first scalar read identifies the literal diagonal \(d(t)\), and the second gives \(E_5(t)=0\). The true grade-seven commutator at \(t\) uses the single earlier nonzero source \(W(y)\) and its own diagonal. Eliminate the corresponding earlier physical tap using \(V(t)\); this is exactly \(E_7(t)=0\). The respective polynomial degrees are at most four and five.

## Integral reduction rules out all fourth-clock roots

At any place above \(43\), the leading coefficient of \(L_6'\) is a unit, so \(a\) is integral. Its five simple residues \(2,9,22,35,42\) are nonzero and \(L_6'(a/2)\) is a unit in each. The residual degree-five equation for \(y\) has unit leading coefficient, so \(y\) is integral. The standalone exact replay verifies the products and irreducibility of its eleven residue factors of total degree 25. In every factor the guards \(y,y-1,y-x,D_y\) and the mode evaluation determinant are units. It then verifies that the *actual* two residual fourth equations have degrees four and five and gcd one. All coefficients are integral because the only reductions are of the unit-guarded scalar formulas above, and the quotients by \(P_0\) are monic divisions.

The true leading coefficient of \(E_5\) is therefore a unit. Thus any actual \(t\) satisfying \(E_5=0\) is algebraic and integral above \(43\); no last-clock infinity branch remains. Its reduction would be a common root of the two coprime equations over a finite residue extension, a contradiction. The removed factors were removed over characteristic zero before reduction, not by assuming actual distinct clocks remain distinct modulo \(43\).

Run the exact symbolic identities and independent standard-library residue replay:

    python3 -B verify-identities.py
    python3 -B verify.py

The stage-space argument is mathematical and the finite arithmetic is exact. No full Lean formalization is asserted here.
