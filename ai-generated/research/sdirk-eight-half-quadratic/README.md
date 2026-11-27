# A finite coprime quadratic profile chart for the half-diagonal SDIRK8 endpoint pair

Work in the [all-active endpoint-pair chart](../sdirk-eight-half-equal/README.md) for a ten-stage strict SDIRK tableau of order at least eight over a field of characteristic zero. The two off-zero rows are the endpoints, \(g_1=g_{10}=1/8\), \(c_1=c_{10}=\gamma=1/2\), and \(b_1=-b_{10}\). Put \(\boldsymbol h=(A-\gamma I)\boldsymbol g\). We have a relation on the eight physical zero rows
\[
                    q(c_i)h_i=p(c_i),\qquad
              p\in\operatorname{span}(L_3,L_4,L_5),\quad \deg q\le 2 ,
\]
where \(L_j\) are shifted Legendre polynomials. Polynomial and coprime linear profiles were excluded in the [previous packet](../sdirk-eight-half-line-pole/README.md).

**Result.** The remaining **coprime** \(q\) monic quadratic profiles \((p,q)\) and the eight zero-stage clock placements lie in a finite set in each relative endpoint phase. The literal fourth clock \(s\) has a nonzero univariate eliminant, described below without expanding its coefficients. For each \(s\) there are at most two literal fifth clocks and at most two \((p,q)\) per fifth clock. This also covers the singular three-corner system, repeated roots of \(q\), and repeated physical zero clocks permitted by the earlier reductions. It is not a construction or an exclusion of the finite survivors. The stage interval remains **10–11**.

## 1. A quadratic equation for the literal fifth clock

Let \(a,b\) be the first two zero clocks (physical rows two and three), and \(c,d\) the rear zero clocks (physical rows nine and eight, in reverse order). Let \(h_a,h_b\) be their front defect values, and \(k,l\) the two nonzero *normalized reverse* defect values at \(c,d\). Thus \(l h_c=k h_d\) for the forward profile. These constants belong to \(K_0=\mathbb Q(t)\), \(t^2=1/2\). Fix the front sign and allow both rear signs; for a rear star pair changing sign only swaps its two clock/value pairs. All six resulting phases are checked. No ordering on the tableau's coefficient field is assumed.

Let \(s=c_4,y=c_5\). The actual first three low moment reads determine the three strict taps in physical row four through the nonsingular tap matrix in the [rational reduction](../sdirk-eight-half-rational/README.md). They give a cubic \(h_s=H_{\rm tap}(s)\). We already know \(s\ne a,b\) by the literal twin argument. At row five write \(H=h_y\). The first strict tap is \(H/g_1\), so the other three taps, to \(a,b,s\), have the three moments
\[
 M_0=y-\gamma-H/g_1,\quad
 M_1=y^2/2-\gamma y-\gamma H/g_1,\quad
 M_2=y^3/3-\gamma y^2+(2/3)H-\gamma^2 H/g_1 .
\]
For a coprime profile, equal clock gives equal \(h\); if \(y=a,b,s\), the known earlier row with zeros inserted before its diagonal has the same four reads. The three-clock Vandermonde makes the row a literal twin, contrary to the ten-stage floor. Thus \(a,b,s,y\) are distinct even when one of \(s,y\) equals a *later* clock.

The three profiles \(\boldsymbol h,C\boldsymbol h,L_4(\boldsymbol c)\) span \(F_4|_U\) on the eight zero rows \(U\). (Dependence involving \(C\boldsymbol h\) would give the excluded front/rear line-pole ratio.) Consequently the pure columns \(A\boldsymbol h\) and \(A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\) each have a zero rank-four determinant with those basis columns at \((a,b,s,y)\). At the first three rows, all entries are obtained from the literal taps. At \(y\) the fourth entry uses \(M_0,M_1,M_2\) above, and the three basis entries are \(H,yH,L_4(y)\). Multiplying the last row by \(\mathcal V=(a-b)(a-s)(b-s)\) clears the three-tap Vandermonde. For example, the numerator of the tap to \(a\) is \((b-s)(M_2-(b+s)M_1+bsM_0)\).

Use the four polynomials \(\mathcal U_0,\mathcal U_1,\mathcal V_0,\mathcal V_1\) computed from those determinants after dividing out the known nonzero \((s-a)^2(s-b)^2\). The necessary equations are
\[
   \mathcal U_0(s,y)+H\mathcal U_1(s,y)=0,\qquad
   \mathcal V_0(s,y)+H\mathcal V_1(s,y)=0.
\]
The script verifies these affine degrees, the exact divisions and the following elimination. The determinant \(\mathfrak d(s)\) of the three pure basis columns at \(a,b,s\) factors as \((s-a)(s-b)v(s)\) with \(\deg v=2\). If \(v(s)=0\), the determinant obtained by replacing \(L_4\) by \(A\boldsymbol h\) must vanish since \(h,Ch\) are independent at \(a,b\); its exact gcd with \(v\) is one. Thus \(v(s)\ne0\). Defining
\[
 R(s,Y)=\frac{\mathcal U_0\mathcal V_1-\mathcal U_1\mathcal V_0}
                   {(Y-a)(Y-b)(Y-s)v(s)}
\]
gives a polynomial quadratic in \(Y\), and \(R(s,y)=0\). For the front star phase, its two permitted clocks are \(y=3s/2-1/4\) and \(y=103/72-s\). For the front arithmetic phase, the script computes \(R\) as a quadratic directly from the tap data. Its three coefficients in \(K_0[s]\) have gcd one in both phases, so it never vanishes identically in \(Y\) at any \(s\). Also \(\mathcal U_1,\mathcal V_1\) cannot both vanish at a true site: then both constant terms vanish, and the three resultants
\(\operatorname{Res}_Y(\mathcal U_1,\mathcal V_1),\operatorname{Res}_Y(\mathcal U_0,\mathcal U_1),\operatorname{Res}_Y(\mathcal V_0,\mathcal V_1)\)
have no common root outside \(\mathfrak d=0\). Thus \(H\) is uniquely determined even at special fifth-clock fibers.

## 2. Finite denominator pencil at every literal clock pair

The four front values give four linear homogeneous equations on the six coefficients of \(p,q\) (retaining the leading coefficient of \(q\) as a variable), with rows
\[
      [L_3(x),L_4(x),L_5(x),-h_x,-xh_x,-x^2h_x]\quad (x=a,b,s,y).
\]
The Legendre block has rank three: the first two rows are independent, and the determinants for adding \(s\) or \(y\) cannot simultaneously vanish off the twin and \(\mathfrak d\) guards. This is an exact resultant with \(R\) in the spectral variable \(Y\) and a gcd in \(s\). The full four-row matrix has rank four. For either allowed choice of the nonzero \(H\) divisor, form the three augmented determinants using \(\boldsymbol h,\boldsymbol c\odot\boldsymbol h,\boldsymbol c^{\odot2}\odot\boldsymbol h\). Clear that divisor and remove only the twin factors. To test simultaneous zero, first project by \(R\) into a finite set of \(s\) roots using exact resultant gcds. Then check the common \(Y\) factors in each exact \(K_0[s]/(M)\), where \(M\) runs over the irreducible factors of that scalar projection. All common roots violate a known nonzero guard in both pivot cases. The common factors are checked in these finite quotients, not discarded merely because a guard's projected root appears.

Thus monic \(q\) describes a line, if a witness exists. The remaining corner equation
\[
                            l q(d)p(c)-k q(c)p(d)=0
\]
restricts to a quadratic on that line. It is not identically zero on any admissible line, including singular corner charts. For the exact check write \(Q_c,Q_d,P_c,P_d,L\) for evaluation of \(q,p\) at \(c,d\) and the leading coefficient of \(q\). Let \([u,v]\) denote the \(6\)-by-\(6\) determinant appending \(u,v\) to the four front rows, with a fixed common clearing factor. If \([Q_c,Q_d]\ne0\), the two \(Q\)'s are coordinates on the two-dimensional kernel of the front equations. Identity of the rear quadratic would force
\[
     [Q_c,P_c]=[Q_d,P_d]=l[P_c,Q_d]-k[Q_c,P_d]=0 .
\]
If \([Q_c,Q_d]=0\), the restrictions of \(Q_c,Q_d\) are proportional (neither vanishes on a coprime witness). Then \(D=[Q_c,L]\) and \(E=[Q_d,L]\) are nonzero: otherwise a nonzero kernel vector with \(L=0\) would give a linear \(q\) vanishing at both distinct rear nodes, and then \(p=0\) by Legendre rank. In the coordinate pair \((Q_c,L)\) the identity would now force
\[
             l E[P_c,L]-k D[P_d,L]=0,\qquad
             l E[Q_c,P_c]-k D[Q_c,P_d]=0.
\]
The [exact fiber replay](check_exceptional_fibers.py) applies the same projection and finite-quotient guard checks to both sets of equations in every phase. Since the leading monic condition selects a nonempty affine part of the projective line, at most two denominators and numerators remain per \((s,y)\). This argument never assumes a generic nonzero corner determinant.

## 3. A nonzero univariate projection using the six literal sites

The preceding chronological relations hold without using the full zero-row ordinary moments. Work temporarily over \(K_0(s)\). Take the monic degree-two quotient by \(R(s,Y)\), recover \(H=-\mathcal U_0/\mathcal U_1\), then determine each coefficient of \(p\) as an affine function of \(\alpha,\beta\) for \(q=X^2+\alpha X+\beta\), using its values at \(a,b,s\). Use \(y\) to solve for \(\alpha\) in terms of \(\beta\). Take the monic degree-two quotient by the rear ratio in \(\beta\). This is a finite algebra of dimension four over \(K_0(s)\). The inverses and both degree-two leading coefficients used here are verified in the good-reduction receipt below. Outside their finitely many scalar poles/zeros, every actual profile of this phase is a specialization of this tower.

Let \(P_6(X)\) be the product of the six literal factors at \(a,b,s,y,c,d\), with multiplicities if clocks repeat. The four paid residue conditions determine the moment functional \(\ell(f/q^2)\) through degree eleven, as in the [square-denominator reconstruction](../sdirk-eight-half-rational/README.md). Cramer's rule scales it by the nonzero residue determinant \(\rho\); write \(T_j=\rho\ell(P_6 X^j/q^2)\). This computation uses only monic division by \(q^2\) and the ordinary moments through seven. Six actual rows vanish under the \(P_6\) factor, so only the two remaining physical zero rows contribute. Necessarily
\[
                            G=\det[T_{i+j}]_{i,j=0}^2=0 .
\]
In particular this does **not** require six distinct clocks, different residual clocks, or nonzero individual residual weights. With a coprime profile there is never a true pole at a physical clock; a repeated root of \(q\) itself is allowed.

The [finite projection replay](check_finite_projection.py) proves \(G\) a **unit** in the dimension-four generic algebra. Use \(1009\), \(t=285\) (so \(2t^2=1\) modulo \(1009\)), then specialize \(s=1\) in the front star phase or \(s=3\) in the front arithmetic phase. These are polynomial determinant nonvanishing tests, not an assumption that a proposed tableau reduces at the prime. At these specializations the degree-two \(Y\) quotient is split separable, with both roots explicitly checked. In each component the front interpolation determinant, the coefficient for solving \(\alpha\), and the leading coefficient of the rear quadratic are nonzero. The monic degree-two \(\beta\) quotient has \(G\) coprime to its defining polynomial in each component. All rational coefficient denominators are checked in reduction. Therefore the indicated multiplication determinants on the generic monic free bases are nonzero; the same argument certifies the preceding pivot inverses. The numerator of the multiplication determinant of \(G\), together with the finitely many projection-denominator zero factors, is a nonzero univariate eliminant in \(s\). Every actual solution lies in its zero set. Section 2 covers all its exceptional fibers, so none of them is a positive-dimensional family of coprime denominator profiles.

Once \((s,y,p,q)\) is fixed, the remaining two physical clocks have finitely many possible positions. Indeed there are seven or eight distinct ordinary sites and no canceled groups by the previous coprime census. On the as-yet unpegged distinct sites the moment functional \(T_j\) has nonzero scalar weights and at most two sites. The signed Vandermonde Hankel system gives their monic nodal factor as in the earlier reconstruction. If fewer than two new sites remain, place any leftover physical row at one of the already recovered sites. This discussion bounds the clock/profile data, not every free tableau entry.

## 4. Common factors are a separate supported-vector problem

Write \(d_0=\gcd(p,q)\ne1\), \(p=d_0p_0,q=d_0q_0\). The reduced relation cannot hold on **all** zero rows. If \(\deg q_0=1\), then \(\deg p_0\le4\); the paid \(h\) moments and ordinary polynomial moments through seven would force \(p_0\propto L_4\), giving the incompatible front/rear simple pole from the half-diagonal proof. If \(q_0\) is constant, the same moment probes give \(p_0\propto L_4\), contrary to the independent front \(h,L_4\) readings. In particular a nontrivial common factor with no actual physical zero clock at one of its roots is impossible.

The real issue is the **discrepancy vector**
\[
 \boldsymbol u=q_0(\boldsymbol c)\odot\boldsymbol h-p_0(\boldsymbol c)
                        +\frac{p_0(\gamma)}{g_1}\boldsymbol g.
\]
It is nonzero and supported on the zero rows whose clocks are actual roots of \(d_0\). For \(\deg d_0=1\) it belongs to \(E_4\). If the discrepancy occurs at just one literal row then \(h_i=0\) there, since \(\boldsymbol h\in F_3\) and \(\boldsymbol u^{\mathsf T}B\boldsymbol h=0\). With repeated clocks this conclusion is only a local weighted identity, not an individual vanishing:
\[
       q_0(r)\sum_{c_i=r,\,i\in U} b_i h_i^2
                   =p_0(r)\sum_{c_i=r,\,i\in U} b_i h_i.
\]
If \(q_0(r)=0\), then \(p_0(r)\ne0\), and this forces the local cubic-defect moment to vanish. It does not permit division at that clock.

If \(q\mid p\) and \(\deg q=2\), \(q_0=1\) and \(\boldsymbol u\in E_3\). A discrepancy supported at only one distinct clock \(r\), even with repeated rows, is impossible. Pair with \((C-rI)C^j\boldsymbol 1\), \(0\le j\le3\). The scalar trace \(-p_0\) yields that \((X-r)p_0\) is a nonzero multiple of \(L_4\). Thus \(r\) is a fourth Gauss clock. None of the four pegged clocks is such a clock (exactly checked in the fiber script), so the incompatible front/rear line-pole read applies at all four. This also rules out the common-factor linear \(q\mid p\) case with \(\deg(p/q)\le3\). A full shared quadratic must therefore have **two distinct actual discrepancy clocks**. Multiplying \(\boldsymbol u\) by \(C-r'I\) isolates the other clock in \(E_4\); it has the same local weighted identity, and a singleton discrepancy again forces \(h_i=0\). The case of a double root with only a *linear* common factor is not excluded. Shared-root branches satisfying these necessary conditions remain open, with no use of a canceled denominator at a physical stage.

## 5. Replay and proof boundary

Python 3 dependencies: `sympy==1.14.0` and `python-flint==0.9.0`. For example:
```sh
python3 -m venv .venv
.venv/bin/python -m pip install sympy==1.14.0 python-flint==0.9.0
.venv/bin/python check_exceptional_fibers.py
.venv/bin/python check_finite_projection.py
```
No network is needed for the replays once dependencies are installed. The [Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8HalfQuadraticReceipts.lean) checks the Vandermonde-cleared three-tap read, affine elimination, and the six-peg Hankel determinant over an arbitrary commutative ring. The tableau reductions, polynomial projections, and finite quotient receipts are exact source mathematics and replay, not an end-to-end Lean nonexistence theorem.
