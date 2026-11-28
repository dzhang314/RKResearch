# Two-singleton front versus rear D,S,S arithmetic: no reused terminal D

Assume a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, all physical quadratic defects nonzero, exactly seven distinct clocks, and exactly one singleton physical endpoint. Orient from that singleton. Suppose the actual front has two S labels and one D, and the doubled end opens D,S,S with a genuine nonzero-tap arithmetic third row. **The front double cannot have the terminal clock label.** This exclusion covers both the regular and zero-rank graph-ratio branches. The terminal-new and rear one-extra-D cases are separate; this is not a change to the general 10–11 stage interval.

## Two measured front singletons and the paid reverse ratio

Normalize the diagonal to one, let \(y=x-1\), \(m=1/(2\gamma)\), \(H=2(m-1)\), and evaluate the monic Legendre modes \(L_3,L_4\) at \(t=y-H/2\). The first singleton has label \(0\) and defect \(1/2\); the terminal double has label \(H\ne0\). In this packet the later front double is also at \(H\). The other front singleton \(s\), the two known front defects \(f_H,f_s\), and all actual first-three taps are given by the [literal phase table](../sdirk-eight-all-dirty-seven-quadratic-two-s-front-dss-star/README.md#actual-front-pairs-and-reverse-star-axis) at \(d=H\). The A2/A3 phases place the D second/third in forward arithmetic. Both actual front star orders give the same two prescribed pairs; no permutation of an actual method is made. The first-departure condition at the singleton front forbids its actual gap being two.

The rear singleton clocks in original coordinates are \(p=H-v,\ q=H-2v\). Put
\[
 \kappa=1+2v-v^2,\quad D=-2+v+4v^2-v^3,\quad
 \widehat q=D-v(v-2)(3v-2).
\]
Their normalized rear defects are \(\kappa/2,\ \kappa\widehat q/(2D)\). The true rear guards include nonzero \(v,\kappa,D,\widehat q,3v-2\); the doubled reverse first clock does not by itself forbid \(v=2\). The four singleton labels \(0,s,p,q\) are distinct and disjoint from the D label \(H\). Let \(\lambda\ne0\) be the actual reverse-to-original scale, and \(\mu=\kappa\lambda=2R(p)\). The true singleton graph is genuinely quadratic; its paid front values give
\[
 R(y)=\tfrac12+a y+b y(y-s),\qquad a=(f_s-\tfrac12)/s,\qquad b\ne0 .
\]
The two actual rear graph readings satisfy \(D R(q)=\widehat q R(p)\). Cancel only the genuine nonzero \(v\) in the difference, giving \(V+b U=0\), where
\[
 \begin{split}
 U&=D(2H-3v-s)-(v-2)(3v-2)p(p-s),\\
 V&=D a-(v-2)(3v-2)(\tfrac12+a p).
 \end{split}
\]
These formulas are polynomial in \(v\). The reduced ratio is computed before imposing either branch, and no pivot is assumed until the branch split.

## True terminal and nodal equations on either branch

For a specified curvature \(b\), set \(W=R/b\) monic. The [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) has \(\mathcal Q=L_3-F_*L_4\) proportional to \(P R\), where \(P\) is cubic on the D labels and \(F_*\) is affine nonconstant. Consecutive Legendre coprimality makes \(L_4\) a unit modulo \(W\); this holds at Hermite or nonsplit \(W\) as well. Hence fit \(F_*=(L_3/L_4)\bmod W\), form the exact cubic \(M_3=\mathcal Q/W\), and impose \(M_3(H)=0\). This never divides by \(W(H)\), so any common graph and doubled-clock root is retained. Also \(M_3(0)\ne0\) because \(0\) is not a D label.

Let \(S_4=y(y-s)(y-p)(y-q)\). Those are all actual singleton roots, so the true quartic is \(\mathcal H=L_4-RC=h_4 S_4\), \(C=A_2+B R\), \(h_4\ne0\). Write \(L_4\bmod W=l_0+l_1y,\ S_4\bmod W=z_0+z_1y\). Then \(l_i=h_4 z_i\), hence the scalar nodal condition \(l_0 z_1-l_1 z_0=0\). The two component polynomials
\[
             C_i=(z_i L_4-l_i S_4)/R,\quad i=0,1,
\]
are exactly \(z_i C\) at a valid mesh. When computing necessary equations symbolically, take the quotient part of polynomial division, whose remainder is zero under the actual nodal identities. If one component vanishes, its scale is not inverted; both fits are kept. All actual nonzero graph readings \(R(p),R(q)\) and the nonzero curvature are retained as guards.

There is one genuine physical terminal overlap: the two roots of the D residual quadratic at \(H\) are the front defect \(f_H\) and original rear terminal defect \(\lambda/2\). Their true product fixes \(\beta=B\lambda=-2L_4(H)/f_H\). Thus \(\mu B=\kappa\beta\), and the paid front D equation yields, for \(i=0,1\),
\[
     \mu\big(z_i L_4(H)-f_H C_i(H)\big)
           -z_i\beta\kappa f_H(f_H-R(H))=0 .
\]
No inverse of an unknown fit coefficient or of \(R\) at the double is used. The literal overlap also gives \(\mu-2\kappa f_H\ne0\), since the two physical residual roots at a double are distinct. The replay audits every nonconstant denominator against actual phase, clock, graph and Legendre guards, including the matrix determinant for division by \(L_4\bmod W\).

## Regular and zero-rank fields, with exact curvature replay

**Regular \(U\ne0\).** The curvature is \(b=-V/U\) and \(V\ne0\) follows from \(b\ne0\). Substitute two observed physical phases into \(M_3(H)\), the nodal determinant and both paid D component equations. Take each integer resultant against \(M_3(H)\) in \(v\), removing only known nonzero \(H\)-guards, then the gcd in \(H\). The three projected degree lists are \((242,361,406)\), \((112,192,211)\), \((142,226,243)\) for front A2, A3, star. Their respective irreducible \(H\)-degree/multiplicity lists are \((15,3)\), \((3,2),(5,2)\), and \((9,3)\). The exact simultaneous \(v\)-gcd in each of these four fields is linear before guards, but becomes a unit after removing only true known guards, including \(U,V\ne0\) where appropriate. No dropped specialized leading coefficient defines a loss.

**Rank zero \(U=0\).** Necessarily \(V=0\), and this is not discarded as a failed pivot. The two equations \(D q(q-s)=\widehat q p(p-s)\) and \(D(\tfrac12+a q)=\widehat q(\tfrac12+a p)\) imply, by one cross multiplication and the known \(D(p-q)\ne0\),
\[
                         p+q-s+2a p q=0.
\]
Take pairwise integer resultants of these three rank-zero scalar conditions in \(v\). After specialization-safe guards the only irreducible \(H\) factors have degree 15 (A2), 5 (A3), or 9 (star), each once. Each exact field has one genuine linear \(v\)-gcd satisfying all rank-zero equations. Leave \(b\) free in that exact field. The cubic quotient, nodal and both actual D equations above have numerator degrees \((4,2,3,3)\), \((3,2,3,3)\), \((4,2,3,3)\) in \(b\), respectively. Their gcd is already a unit in each field before any additional curvature guard, so every algebraic or transcendental curvature in any characteristic-zero coefficient extension is excluded. This includes potentially nonsplit quadratic graphs and any common roots with D, and it is not an extrapolation from a finite-prime scan.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_reused_terminal.py` using SymPy 1.14 and python-flint 0.8. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoSDssArithmeticReuse.lean) verifies the exact scalar rank-zero and scaled-fit identities. The complete rooted-order ingress and polynomial eliminations are a mathematical proof with exact replay, not an end-to-end native Lean or positive-characteristic theorem.
