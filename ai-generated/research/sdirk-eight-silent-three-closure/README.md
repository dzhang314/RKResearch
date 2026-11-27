# A single invisible off-zero clock cannot have three physical stages at strict SDIRK8

Under the [single invisible off-zero clock](../sdirk-eight-silent-oneclock/README.md) hypotheses at the ten-stage strict SDIRK8 floor over a characteristic-zero field, every physical stage with nonzero quadratic residual has zero weight, and all these stages share the first clock \(\gamma\). This packet closes the remaining three-invisible-stage branches. Therefore there can be **at most two** physical off-zero stages in this one-clock silent family. This is not a statement about per-clock aggregate cancellation of nonzero weights, multiple invisible clocks, or the unrestricted **10–11** interval.

Use the previous notation \(L,U,\boldsymbol g,\boldsymbol h=N\boldsymbol g,B,C,M,\boldsymbol w=\boldsymbol b^{\mathsf T}M\). The only remaining \(|L|=3\) case has variable residuals and \(\operatorname{rank}(Z_2|_L)=1\). There are seven physical zero rows. The literal first two zero rows at \(a,b\) have nonzero \(h_a,h_b\) in both phases. Write \(L_4,L_3\) for the shifted Legendre polynomials of degree four and three. The rank \(F_4|_U=2\), and \(\boldsymbol h,C\boldsymbol h\) are independent there by the two front values. Consequently on all physical zero rows,
\[
       L_4(c_i)=Q(c_i)h_i,\qquad
       \left(A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\right)_i
                           =T(c_i)h_i,
\]
where \(Q,T\) are affine and determined at \(a,b\), without using any output weight at those rows.

## 1. If the output does not detect the cubic defect

Suppose \(B\boldsymbol h=0\). Then all active zero rows have clean pure degree-four reads and \(L_4(c_i)=0\). Ordinary cubic scalar rank forces all four ordinary Gauss sites; the active terminal has \(c_{10}=1-\gamma\), so \(\gamma\) is itself Gauss. The first two zero rows are silent, leaving four or five active rows.

With five active, only \(a,b\) are silent zeros. The earliest active stage therefore has strict feed clocks among \(\gamma,a,b\), so its actual clean four moments force the [impossible earliest active Gauss cubic](../sdirk-eight-silent-oneclock/README.md).

With four active there is one further silent zero at \(z\), necessarily before the first active one by the same cubic. This is the third physical zero row chronologically. Its strict predecessors can only be at \(\gamma,a,b\). Let
\[
 P_3(X)=(X-\gamma)(X-a)(X-b),\quad
 G(X)=\int_0^X P_3(Z)\,dZ-\gamma P_3(X),\quad
 K(X)=T(X)-\tfrac23(\gamma+a+b).
\]
Here \(G\) denotes a scalar polynomial, not the diagonal matrix of quadratic residuals. The pure cubic residual at any zero row is \((2/3)h_i\). On expanding the four strict moments against \(P_3\) at \(z\), we obtain \(G(z)+K(z)h_z=0\). Combined with \(Q(z)h_z=L_4(z)\), the necessary polynomial is
\[
                     F(X)= Q(X)G(X)+K(X)L_4(X).
\]
The numerator vanishes at \(a,b\) by the same literal moment expansion on their known predecessor taps. The extra silent \(z\) cannot coincide with \(a,b,\gamma\), because the earliest active stage would then still have only the excluded three feed clocks. Thus \(z\) is a root of the degree-at-most-three quotient by \((X-a)(X-b)\). No generic tableau interpolation is assumed.

Let \(x,y\) be the first and second active clocks. Both differ from the terminal clock \(1-\gamma\). For the first active row \(x\), the four scalar moments fix its aggregates at \(\gamma,a,b,z\) by a Vandermonde. For \(y\), if \(x\ne\gamma\), the strict tap to the previous active \(x\) is one extra parameter; subtracting that tap's four moments leaves the same Vandermonde. On the four active Gauss sites every pure degree-five column lies in the \(L_3\) line by orthogonality to degree at most two. Apply this to
\[
             A((C-\gamma I)\boldsymbol h),\qquad
             A\boldsymbol c^{\odot4}-\boldsymbol c^{\odot5}/5 .
\]
The first read involves only \(a,b,z\) because \((C-\gamma I)\boldsymbol h\) vanishes at off-zero clocks and at all active rows. The second read fixes the extra tap to \(x\), with coefficient \(L_3(x)(x-\gamma)(x-a)(x-b)(x-z)\). At \(x=\gamma\), feeds to that previous active row merge into the scalar aggregate at \(\gamma\), and both tests remain independent of how that aggregate splits.

The [cubic quotient replay](four_active.py) performs these two comparisons at \(1129,t=203\), where the four Gauss roots are simple and split. The orientation data can be treated as the monic quartic for \(\gamma\), then the monic quadratic of the two remaining Gauss roots besides \(\gamma,1-\gamma\). Naming one of these roots \(v\), the ordered choices are \((\gamma,v),(v,\gamma),(v,1-v)\), covering both signs of \(v\). All 48 reduced combinations (front phase, Gauss \(\gamma\), ordered pair) are checked. In this finite algebra the cubic quotient has degree three and its leading coefficient is a unit; \(Q\) is coprime to \(L_4\), and \(Q(z)\) and every Vandermonde divisor are units. Moreover \(z\) cannot be any active Gauss node in characteristic zero: \(Q(z)\ne0\) there forces \(h_z=0\), so \(G(z)=0\) would contradict the earlier Gauss cubic. When \(x\ne\gamma\), the remaining first-column degree-five line test at the fixed tap is a unit. When \(x=\gamma\), the two residuals generate the unit ideal after reduction. In both cases the fixed monic bases lift the multiplication rank to characteristic zero, rather than requiring the hypothetical tableau to have a reduction.

## 2. Retain all seven active zero rows and the scalar defect profile

The earlier census and the six-active exclusion leave all seven zero weights nonzero if \(B\boldsymbol h\ne0\). Whenever \(Q\) is nonconstant and coprime to \(L_4\), its root is not a physical zero clock, so \(h=L_4/Q\) is single-valued. Let \(n\) be the number of distinct physical zero clocks, \(D\) their monic nodal polynomial. Interpolating \(R(c)=D'(c)\sum b_i h_i\) and \(S(c)=D'(c)\sum b_i h_i^2\) gives \(\deg R\le n-6,\ \deg S\le n-3\) by the paid moments. If \(n\le5\) the first sum is identically zero by Vandermonde instead. The polynomial \(Q S-L_4 R\) has at least \(n\) roots and degree at most \(n-2\), so \(Q\mid R\). The aggregate \(R\) is nonzero: otherwise all ordinary active sites are Gauss (because \(h\) is single-valued), and the two different nonzero-\(h\) front sites would need their own canceled groups of at least two physical rows apiece, leaving too few rows for four ordinary sites. Thus \(n\ge7\), and the seven zero clocks are distinct.

In this affine coprime chart normalize \(h=p/q\) with \(q=X-\xi\), \(p\) a nonzero multiple of \(L_4\). Write \(p=qS+d\), \(S=qU+r\). The paid moments \(\ell(h)=\ell(h^2)=0\) give
\[
 \lambda_1=\ell(1/q)=-I(S)/d,\qquad
 \lambda_2=\ell(1/q^2)=-[I(S^2)+2d(I(U)+r\lambda_1)]/d^2 .
\]
Thus for every \(f\) of degree at most nine, ordinary precision through seven and the two residues evaluate \(\ell(f/q^2)\). This holds without knowing any individual weight. The later projections check that \(Q\) really is nonconstant and coprime, rather than imposing that as an unproved architecture restriction.

## 3. Half diagonal

Here \(x=c_{10}=\gamma=1/2\). In both front phases the fixed affine \(Q\) is nonconstant and coprime to \(L_4\), with \(h_{10}\ne0\). The row \(\boldsymbol w(C-\gamma I)\) belongs to the one-dimensional supported \(Z_3\) line spanned by \(\boldsymbol h^{\mathsf T}B\). Its terminal entry is zero, so it is zero everywhere. Thus the reverse degree-two pure row is supported solely on \(\gamma\).

If \(b_8\ne0\), the literal trailing three-row normalization gives two rear zero-defect clocks in backward time, distinct from the terminal and the two front clocks. These five pegged clocks give \(P_5\). At most two physical rows survive \(P_5\), so the \(3\times3\) Hankel determinant of \(\ell(P_5 X^{i+j}/q^2)\) is zero. The [exact replay](center.py) checks it nonzero in every phase.

If \(b_8=0\), column eight's two weighted feed taps \(s=b_9 A_{9,8}\), \(t=b_{10} A_{10,8}\) satisfy \(s+t=0\), and \(w_8=2(c_{10}-c_9)t\ne0\). Since \(w_9=0\), \((\boldsymbol wN)_8=-\gamma^2t\). The two pure rows \(\boldsymbol w,\boldsymbol wN\) are independent, and their restriction to the invisible set has rank one. Subtracting \(\lambda\boldsymbol w\), where \(\lambda=(\boldsymbol wN)_8/w_8\), gives the supported \(Z_3\) line proportional to \(\boldsymbol h^{\mathsf T}B\). Its terminal and penultimate entries, together with \(D(1)\), force
\[
                    h_9/h_{10}=2(c_{10}-c_9)^2/\gamma^2
                               =2(1\pm\sqrt2)^2.
\]
This scalar is incompatible with \(L_4(c)/Q(c)\) at the two actual clocks, by the same replay. No full weighted reverse tableau is used.

## 4. Off-half diagonal and the literal reverse residual ratios

Let \(x=c_{10}=1-\gamma\), \(u=(x-c_9)/\gamma\ne0\), and \(k=1+2u-u^2\). The latter is the normalized reverse quadratic residual ratio on the last two active rows; this uses only the literal two-row block. From the pure basis \(\boldsymbol w,\boldsymbol wN\), comparing the last two coordinates gives
\[
                   \boldsymbol w(C-xI)=-k\,\boldsymbol wN .
\]
In particular \(k\ne0\): if it vanished then \(\boldsymbol w\) would be supported only at \(x\), inconsistent with its nonzero invisible restriction at \(\gamma\ne x\). Also \(\boldsymbol w(C-\gamma I)\ne0\) at the terminal, spans the supported \(Z_3\) line, and is proportional to \(\boldsymbol h^{\mathsf T}B\). Thus \(h_{10}\ne0\), and on the last two active rows
\[
            (x-\gamma) h_9=k(c_9-\gamma)h_{10}.
\]
The affine relation multiplies this to an exact polynomial gate using \(L_4(c)\) and \(Q(c)\); it holds without assuming either clock is regular for the profile.

**Silent eighth stage.** With the same two weighted strict feed taps in column eight, \(w_8=2(x-c_9)t\ne0\) and \((\boldsymbol wN)_8=-\gamma^2(1-k)t\). Its physical clock is \(\gamma\). The pure row identity therefore gives
\[
         2u(2\gamma-1)=\gamma k(1-k),\qquad
         \gamma=\frac{2}{4-k(u-2)}.
\]
The [Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8InvisibleTailReceipts.lean) checks the two silent-tail formulas directly from the scalar reads. Substitute this rational \(\gamma\) in the penultimate gate. After removing only known nonzero factors, the [exact projection](off8_projection.py) gives a squarefree degree-29 polynomial in each front phase, coprime to both the constant-\(Q\) and shared-root supports. Thus the affine coprime case is forced. The four pegs \(a,b,c_9,x\) leave three missing sites. The weighted Vandermonde Hankel from \(T(P_4 X^j)=\ell(P_4 X^j/q^2)\) reconstructs their monic cubic from moments through degree nine, with nonzero determinant at a proposed solution. Its determinant is a unit in the finite scalar quotient by good reduction at \(1009,t=285\). The first physical zero after \(a,b\) must be one of the missing sites, and again pays the literal cubic quotient \(F/((X-a)(X-b))\) from Section 1 because all other predecessors have clock \(\gamma\). The [finite replay](off8_fibers.py) certifies this read a unit in the reconstructed monic clock algebra.

**Active eighth stage.** Normalize the actual three-row trailing block by its nonzero weights. The reverse third gap is \(w=2-u\) in the star phase or \(w=2u\) in arithmetic, with normalized residual ratio \(q_3=k\) or
\[
        q_3=1+4u-4u^2+\frac{4u^2(3u-2)}{-2+u+4u^2-u^3}.
\]
The third clock is \(c_8=x-\gamma w\). The second polynomial gate is \((x-\gamma)h_8=q_3(c_8-\gamma)h_{10}\). The [exact resultant](tail8_projection.py) eliminates \(u\) from the two denominator-cleared rear gates, with explicit nonzero phase guards. \(Q(x)\) cannot vanish: \(h_{10}\ne0\) and the exact gcd of \(Q(x)\) and \(L_4(x)\) in \(\gamma\) is one. The resulting scalar projection in \(\gamma\) has squarefree degrees \(26,73,31,68\) in the four front/rear phase pairs and is again coprime to the constant-\(Q\) and shared-root supports. All seven physical zero clocks are distinct.

The remaining five pegs \(a,b,c_8,c_9,x\) give the degree-nine weighted Hankel determinant as in the half-diagonal case. An exactly detected degree-eight factor of each scalar projection is where the first rear polynomial drops from degree three in \(u\) to degree two. Treat those as distinct monic fibers, with the degree-three fiber on the complementary factors. In each of the eight finite towers the [verification](tail8_fibers.py) shows that the sum of the other rear gate and this Hankel determinant has invertible multiplication at \(1009,t=285\). A true solution would annul both. Every coefficient denominator, leading pivot, and monic basis used in reduction is checked, so the test excludes the characteristic-zero solution, not just finite-field points.

## Replay and scope

Run `python3 four_active.py`, `python3 center.py`, `python3 off8_fibers.py`, and `python3 tail8_fibers.py` with `sympy==1.14.0` and `python-flint==0.9.0`. Once installed these replays need no network. The Lean file checks the two silent-tail scalar read identities; tableau saturation, chronology and the finite-quotient exclusions are the source proof, not a single full Lean theorem.

The [two-stage follow-up](../sdirk-eight-silent-two-unequal/README.md) excludes unequal residuals at the common invisible clock. Equal residuals and one off-zero stage remain separate.
