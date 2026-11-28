# Nine active labels: the switched flank of the single-mixed two-triple chart is impossible

**Scope.** Continue the [nine-label nonzero-first-pool chart](ERK11-NONZERO-FIRST-POOL-NINE-LABEL-OVERLAPS.md) of the all-live, half-clock, two-carrier, two-new-boundary order-eleven equality problem. In the thirteen-active two-plateau-triple chart take the mixed overlap \(a=e\), so that \(d=2a-1\), and put the foreign \(a\)-read at physical 15. This note rules out the foreign \(d\)-read at physical **6 or 7** over characteristic zero, conditional on those inherited tableau premises. The other orientation is reflected. Together with the [middle exit](ERK11-NONZERO-NINE-SINGLE-MIXED-MIDDLE-EXIT.md) and the prior double-overlap exit, this disposes of every mixed overlap in the ordered nine-label thirteen-active two-triple chart. It does not dispose of non-overlapping two triples or change the unrestricted ERK11 stage interval.

## 1. Width and front data, with the exact forbidden right fiber removed

Let \(F\) be the physical grade-three pure response, and \(K\) the cubic pooled profile. In particular \(F_i=K(c_i)\) on every singleton active label. Let \(h=a/2\) and \(b=1-d\) (the reflected width). The individual weights are \(b_i\). Only rows 6 and 7 are in play here. Write \(u\) for the other of their two clocks, so \(u\) and \(h\) are singleton active labels. The two reverse extras, at physical 11 and 12, are also singleton active labels. The three middle clocks \(x=c_8,y=c_9,z=c_{10}\) are all singleton and pairwise distinct. All these seven singleton labels are distinct from \(a,d\).

By the earlier Jacobi and support arguments the width satisfies the octic \(O_8(a)=0\), and
\[
 R_0(X)=R_5(a)R_4(X)-R_4(a)R_5(X),\quad
 K_0=R_0/[(X-a)(X-d)],\quad K=\beta K_0,\quad
 \beta=a^2/(8K_0(h)).
\]
The normalization uses the calibrated singleton \(h\). The replay checks that \(O_8\) retains degree eight and is irreducible modulo 19, \(R_0\) retains degree five and is squarefree, and all displayed denominators are units. Let \(L(X)=X^2(a-X)/a\) and \(L^\star(X)=(1-X)^2(X-d)/b\) be the actual lateral response profiles. The remaining singleton \(u\) solves the monic quadratic proportional to \((K-L)/(X-h)\). No assumption is made about which of these two roots is physical 6 or 7.

For reverse extra sum \(Z\), product \(M\), and hull \(A_R=X^2-ZX+M\), the actual [first inverse-Gram contact](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md) uses
\[
 L_0=(a-d)(a-u),\quad L_1=-du,\quad
 R_0^{\rm row}=M-dZ+d^2,\quad R_1^{\rm row}=-(1-Z+M).
\]
Put \(\alpha=L_0+T_4(a)L_1,\ \beta_1=T_4(b)L_0+U_{4,4}(a,b)L_1\). Then \(\alpha R_0^{\rm row}+\beta_1 R_1^{\rm row}=0\) and
\[
 M=v_0+v_1Z,\qquad
 v_0=\frac{\beta_1-\alpha d^2}{\alpha-\beta_1},\quad
 v_1=\frac{\alpha d-\beta_1}{\alpha-\beta_1}.
\]
The pivot is a unit at both possible residues of \(u\). On the right extras \(L^\star(c_i)=\kappa K(c_i)\), with \(\kappa\ne0\) the ratio of the two physical response scales. Reduce \(L^\star,K\) modulo \(A_R\), with coordinate rows \((r_0,r_1),(q_0,q_1)\). Their determinant \(G(Z)=r_0q_1-r_1q_0\) is of degree at most two by the denominator-free cubic-remainder gate of the middle note. Reduction proves its degree is exactly two, with unit leading coefficient at both \(u\) residues.

There is an **exact** ghost factor \(Z-(1+d)\), not a factor that appears only modulo 19: for the virtual roots \(1,d\) both inverse-Gram entries \(R_0^{\rm row},R_1^{\rm row}\) are zero, so \(M(1+d)=d\); then \(L^\star\) vanishes on both roots, giving \(G(1+d)=0\). Actual reverse extras cannot include \(d\), their own repeated plateau. Therefore \(Z\) is a root of the remaining linear factor, whose leading coefficient is a unit. In those two genuine reduced fibers \(q_1,r_1\) are both units, so \(\kappa=r_1/q_1\) is defined and a unit. No zero-scale residue is silently dropped.

## 2. A monic middle cubic from the ghost-root measure

Write \(w=X(1-X)\) and \(\nu_\xi=k/D'(\xi)\) for the first-response pool at each distinct active clock \(\xi\), where \(D\) is the nine-label hull and \(k\ne0\). The [ghost-root moment derivation](ERK11-NONZERO-NINE-SINGLE-MIXED-MIDDLE-EXIT.md#3-the-ghost-root-equations-use-only-ordinary-scalar-payment) depends only on the two plateau triples, not on the positions of their foreign rows. With \(D_1=D/[(X-a)(X-d)]\), \(\lambda=k/\beta\), and
\[
 M_R(X)=\int_0^1 w(t)\frac{R_0(t)-R_0(X)}{t-X}\,dt,
\]
it reads \(D_1 M_R\equiv-\lambda w\bmod K_0\). In this switched chart \(D_1=(X-h)(X-u)A_R M_{\rm mid}\), where \(M_{\rm mid}\) is the monic cubic with roots \(x,y,z\). The reduction verifies
\[
 H_g=(X-h)(X-u)A_R M_R\bmod K_0
\]
is a unit modulo \(K_0\) at both genuine \(u,Z\) fibers. Inverting multiplication by \(H_g\) on the degree-below-three quotient therefore gives
\[
 M_{\rm mid}=K_0/\operatorname{lc}(K_0)
     +\lambda\,[-wH_g^{-1}\bmod K_0].
\]
A monic basis is used in the quotient. Thus its coefficients are affine in \(\lambda\) with integral coefficients at the chosen place. This pivot is a computed unit, not an assumed nonzero Lagrange weight at a root of \(K_0\); the derivation of the residue equation itself divides by no ghost weight.

## 3. A finite outer-clock projection with degree exactly four

Let \(V_L,V_R\) be the actual grade-four square-clock vectors with models \(V=X^2(X-a)^2,\ W=(1-X)^2(X-d)^2\). Set \(p=AV_L,\ r=A^\star V_R\) with primitive models \(P=JV,\ Q=\bar J W\). Strictness gives \(V_L=0\) through 7, \(V_R=0\) from 11, \(p=0\) through 8, \(r=0\) from 10. The [four split primitive payments](ERK11-NINE-SITE-CENTRAL-REPEATED-PAIR-IDENTITY.md) induce an actual equation \(\mathcal B(x,z)=A_0xz+B_0x+C_0z+D_0=0\) at the physical outer clocks \(x=c_8,z=c_{10}\), where
\[
 H=\int PW=\int VQ,\quad C_1=\int XPW,\quad C_2=\int XVQ,\quad
 J_0=\int PQ,\quad I_j=\int X^j VW,
\]
\[
 A_0=H^2-J_0I_0,\quad B_0=J_0I_1-HC_1,\quad
 C_0=J_0I_1-HC_2,\quad D_0=C_1C_2-J_0I_2.
\]
This is a necessary condition for either switched row, independent of the front overlap. Use the norm \(\mathcal N(\lambda)=\prod_{i\ne j}\mathcal B(t_i,t_j)\), where the three formal roots \(t_i\) of \(M_{\rm mid}\) are counted with multiplicities. This is symmetric of individual root degree at most four, since each root occurs in four of the six factors. Hence it has ordinary degree at most four in the elementary symmetric polynomials: in lexicographic elimination a leading exponent tuple \(e_1\ge e_2\ge e_3\) is removed by \(s_1^{e_1-e_2}s_2^{e_2-e_3}s_3^{e_3}\), of total exponent \(e_1\le4\), and the subtraction also has individual degree at most four. The coefficients \(s_j\) are affine in \(\lambda\), so the norm has degree at most four in \(\lambda\).

For the omitted root \(y\), let \(s=x+z,\ t=xz\), which are \(s_1-y,\ s_2-ys\) by the cubic. The opposite-orientation product is
\[
 (A_0t+D_0)^2+(B_0+C_0)(A_0t+D_0)s+B_0C_0s^2+(B_0-C_0)^2t.
\]
It is evaluated by its multiplication determinant modulo the monic cubic, and interpolation at five distinct residues checks the norm has degree four and unit leading coefficient. This earns integrality of the algebraic \(\lambda\). Both quartics split into four distinct nonzero roots in \(\mathbb F_{19^{32}}\). At each such root, reduce the equations \(M_{\rm mid}(x)=0\) and \(\mathcal B(x,z)=0\). With \(t=A_0x+C_0,\ v=B_0x+D_0\), the eliminated cubic \(t^3M_{\rm mid}(-v/t)\) is a polynomial, also valid without assuming \(t\) live. The replay computes a linear gcd with \(M_{\rm mid}(x)\) in every fiber and verifies \(t\) is a unit at that root. The reduced \(z=-v/t\) and \(y=s_1-x-z\) follow. Each tuple has three distinct clocks, all distinct from the plateau labels and with nonzero \(D'\) and \(K\). Thus orientation is tested through all possible ordered pairs, not selected by a real root ordering.

## 4. The primitive comparison on five distinct actual sites

The endpoint-only grade-five vector in the [two-clock support theorem](ERK11-NONZERO-FIRST-POOL-NINE-LABEL-OVERLAPS.md#2-a-two-clock-jacobi-gate-at-q9) earns point exactness and ordinary reverse order eleven here. In particular the original and reverse pure grade-five spaces coincide. On noncarriers this common space is spanned by \(F,CF,C^2F\) and one measured grade-five advance; the fifth generator \(s\) has zero noncarrier read. The pure deviation \(p-P(C)\) has nonzero coefficient of the extra advance: early rows 4 and 5 both have clock \(a\), distinct responses, \(p=0\), and the same nonzero residual \(-P(a)=-a^5/30\). A scalar quadratic multiple of \(F\) cannot have these two equal nonzero reads. Therefore some scalar \(\gamma\) and some polynomial \(D_2\) of degree at most two satisfy
\[
 [r_i-Q(c_i)]/F_i-\gamma[p_i-P(c_i)]/F_i=D_2(c_i)
\]
at every active noncarrier. This uses only common grade five, not equality of higher pure spaces.

Here are the actual reads used in this comparison.

* At the three singleton middle clocks, \(b_i=k/[D'(c_i)K(c_i)]\). Their \(V_L,V_R\) reads are \(v_L(X)=V(X)+a(X-a)K(X)\) and \(v_R(X)=W(X)-b(X-d)\kappa K(X)\). In addition to \(p_x=r_z=0\), the actual grade-nine and ten payments for \(pV_R\), \(V_Lr\) and their clock shifts give
\[
 b_y p_y v_R(y)=\frac{C_1-zH}{y-z},\qquad
 b_z p_z v_R(z)=\frac{C_1-yH}{z-y},\qquad
 b_x v_L(x)r_x=\frac{C_2-yH}{x-y},\qquad
 b_y v_L(y)r_y=\frac{C_2-xH}{y-x}.
\]
The exact replay checks each displayed divisor after all finite projections.
* At the foreign plateau row of a clock \(\xi=a,d\), let \(P_f,E_f,U_f\) denote its own-direction primary and foreign known responses and its unknown fifth response, all in the original \(F\) scale. At \(a\), \(P_f=-a^2/2,\ E_f=L^\star(a)/\kappa\); at \(d\), \(P_f=-b^2/(2\kappa),\ E_f=L(d)\). Write
\[
 \ell_\xi=\frac{M_R(\xi)}{R_0'(\xi) w(\xi)}.
\]
These two plateau masses are units by the replay. The whole triple's ordinary moments in the **response** variable through degree three agree with mass \(\ell_\xi\) at zero and mass \(\nu_\xi/K(\xi)\) at \(K(\xi)\). Indeed the ordinary clock pool was \(B_\xi=\ell_\xi+\nu_\xi/K(\xi)\) by exact plateau isolation, and the three response moments are \(\nu_\xi,\nu_\xi K(\xi),\nu_\xi K(\xi)^2\). The last follows from the two paid \(\eta\) tests and exactly two repeated labels. The triple values are distinct: the primary and fifth differ, and if there were only two distinct nonzero response values, the first two moments of its deviation charges \(b_i(K(\xi)-F_i)\) would force both charges after pooling to be zero, contrary to their total \(\ell_\xi K(\xi)\ne0\). Applying the local cubic hull gives
\[
 U_f^{-1}=K(\xi)^{-1}+
  \frac{\ell_\xi P_f E_f}{\nu_\xi(K(\xi)-P_f)(K(\xi)-E_f)}.
\]
The degree-two Lagrange numerator at \(E_f\) gives its deviation charge as \(\ell_\xi K(\xi)P_fU_f/[(E_f-P_f)(E_f-U_f)]\). Finally, the paid one-clock primitive mean from the two-clock theorem isolates only this foreign row: at \(a\) the two own rows have \(p=0\) and the foreign physical 15 has \(r=0\); at \(d\) the two own rows have \(r=0\) and the foreign physical 6 or 7 has \(p=0\). Thus its lone possibly nonzero primitive is
\[
 p_{15}=P(a)\frac{E_f-P_f}{P_f}(E_f/U_f-1)
 \quad\hbox{or}\quad
 r_{6\text{ or }7}=Q(d)\frac{E_f-P_f}{P_f}(E_f/U_f-1).
\]
In the first equation use the \(a\)-responses, in the second the \(d\)-responses. The primitive mean tests are actual grade ten: one other-clock mask on the grade-three \(T\), one endpoint mask \(C\) or \(1-C\), and the grade-five primitive.

Apply the shared-mode comparison at these five distinct physical clock labels \(a,d,x,y,z\). For each, write \(v_i=(p_i-P(c_i))/F_i,\ u_i=(r_i-Q(c_i))/F_i\), and let \(\omega_i=1/\prod_{j\ne i}(c_i-c_j)\) on those five labels. For \(j=0,1\), put \(V_j=\sum_i\omega_i c_i^j v_i,\ U_j=\sum_i\omega_i c_i^j u_i\). Both of these tests kill every quadratic, by interpolation on five nodes. Hence \(U_j=\gamma V_j\), so the necessary determinant \(U_0 V_1-U_1 V_0\) vanishes. This mark uses the actual common pure response space and local primitive reads, not merely the scalar quadrature.

## 5. Complete finite lift and scope

Embed any algebraic width \(a\) in \(\overline{\mathbb Q}_{19}\) and extend to \(u,Z,\lambda,x,y,z\) as reconstructed. They are integral sequentially by the nonvanishing leading terms above. One octic residue representative suffices: all roots of the irreducible degree-eight reduction are Frobenius conjugate and the whole test uses prime-field coefficients. Both quadratic left residues and all four quartic roots in both genuine right fibers are checked. The exact replay separately checks width, scale, remainder-inverse, plateau-response, barycentric, and middle divisions in every applicable residue fiber, plus the final determinant is nonzero in all eight. It uses explicit comparisons against field zero for scalar guards. Thus the characteristic-zero candidate would force a vanishing reduction at a checked fiber and is impossible. The adjacent Lean file checks the scalar response hull, foreign deviation, opposite pair product, and shared-mode elimination over a commutative ring. The actual tableau, support, and finite-place ingress are the mathematical proof, not a native full-tableau exclusion.

The [kernel logs and exact replay](erk11-nine-single-mixed-flank-audit/)
document the scalar checks. The [portable primitive gates](../lean/RKCert/ReviewedNative/ERK11SwitchedPlateauPrimitiveGate.lean)
pass on all four requested core Lean versions; the physical chart proof is mathematical.
