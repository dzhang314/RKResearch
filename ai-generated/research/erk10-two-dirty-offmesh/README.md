# The two-dirty ERK10 Lobatto chart is exhausted

This closes the off-mesh branch of the [two-dirty projection](../erk10-two-dirty-projection/README.md). Together, the packets exclude fourteen-stage order-ten tableaux in the canonical five-opening/four-Lobatto-pair chart with two genuine zero-weight dirty high rows at distinct clocks, neither colliding with a donor. High taps, high row order, and individual normal weight splits are arbitrary. This is not an unrestricted stage floor: the real-algebraic **14–15** interval remains open. No new order-nine tableau is asserted.

## Readable donor coordinates

Retain the first packet's notation. The dirty high clocks are \(a,b\); the donors \(p,q\) are both off the high mesh; \(c,d\) are the two normal high interiors. Write \(S=\{a,b,c,d\}\), \(Q=(X-p)(X-q)\), \(P=XQ\), \(T=X\prod_{\xi\in S}(X-\xi)\), \(D_\xi=T'(\xi)\). The previous rooted proof gives the following:
* All non-dirty high physical rows are truly local through derivative size six, and read the actual early-null size-five source \(X\mathcal P_3\) as \(J_x\).
* At the two dirty rows the actual high functionals are \(\varphi_i=E_i+\psi_i\) with nonzero \(\psi_i\in\langle E_p,E_q\rangle\). The size-four early-null polynomial model is \(KP\).
* Let \(\alpha,\beta\ne0\) be the two dirty coordinates of \(\mathbf d_3\) and \(s_k=\alpha\psi_{a,k}+\beta\psi_{b,k}\). The paid mark gives \((a-k)\alpha\psi_{a,k}+(b-k)\beta\psi_{b,k}=0\) at \(k=p,q\). The high aggregate plus \(s_p,s_q\) annihilates \(X\mathcal P_4\).

The annihilator on the six nonzero sites is one-dimensional. Its coefficients are \(\lambda\) times the barycentric row with
\[
 \omega_\xi=(D_\xi Q(\xi))^{-1}\quad(\xi\in S),\qquad
    [T(p)(p-q)]^{-1},\quad [T(q)(q-p)]^{-1}
\]
at \(S,p,q\), respectively, where \(\lambda\ne0\). This is the leading-coefficient interpolation identity, with a division by each clock to annihilate degrees 1 through 5 rather than 0 through 4. The terminal high coordinate of \(\mathbf d_3\) is zero. Let \(\widehat\alpha=\alpha/\lambda,\ \widehat\beta=\beta/\lambda\).

For the cardinal basis \(\ell_\xi=T/((X-\xi)D_\xi)\) of \(X\mathcal P_3\), the marked equation resolves to \((b-a)\alpha\psi_{a,k}=(b-k)s_k\). Substituting the explicit barycentric donor pair gives
\[
  \psi_a(\ell_\xi)=\tau_a(b-\xi)\omega_\xi,\qquad
  \psi_b(\ell_\xi)=\tau_b(a-\xi)\omega_\xi,\qquad
  \tau_a=-[(b-a)\widehat\alpha]^{-1},\
  \tau_b=-[(a-b)\widehat\beta]^{-1}.
\]
For example
\((b-p)/(p-\xi)-(b-q)/(q-\xi)=(q-p)(b-\xi)/((p-\xi)(q-\xi))\).
The general field lemmas project_axis and missing_cardinal prove the relevant marked scalar identities.

In particular \(\varphi_a(\ell_b)=\varphi_b(\ell_a)=0\). If only one dirty preceded the first non-dirty row, that row's \(J_x\) would see only this one read and would kill the opposite cardinal, contrary to the 60 predecessor hulls in the first packet. With no preceding dirty a nonzero read is already impossible. Hence **both dirty rows precede all clean rows**, and we label \(a\) first, \(b\) second. Let \(x\) be the first non-dirty high clock and \(y\ne x\) the next distinct non-dirty high clock; repeats at \(x\) expose only \(E_x\). Both are interior.

## Two causal reads determine the donor sum and product

Write \(j_{v,k}=J_v\ell_k\), all nonzero for interior \(v,k\) by the predecessor hulls. The first exact \(J_x\) must read only \(\varphi_a,\varphi_b\). Its two nonzero coefficients on the \(a,b\) cardinals force \(\theta_i=\varphi_i(\ell_i)\ne0\). Normalize each read by \(\theta_i\), with \(\eta_i=\tau_i/\theta_i\). In \(a,b,c,d\) order the normalized rows are
\[
 \begin{aligned}
 \mathbf f_a&=(1,0,\eta_a(b-c)\omega_c,\eta_a(b-d)\omega_d),\\
 \mathbf f_b&=(0,1,\eta_b(a-c)\omega_c,\eta_b(a-d)\omega_d).
 \end{aligned}
\]
Comparing the other two coefficients of \(J_x\) gives, for \(k=c,d\),
\[
 j_{x,k}D_kQ(k)=j_{x,a}\eta_a(b-k)+j_{x,b}\eta_b(a-k).
\]
The determinant is \(j_{x,a}j_{x,b}(b-a)(c-d)\ne0\). Thus \(\eta_a,\eta_b\) are homogeneous linear functions of \(Q(c),Q(d)\).

The next distinct \(J_y\) lies in the span of the two normalized rows and \(E_x\). For \(x=a\) compare over \(k=c,d\) the necessary coefficient
\[
 \bigl(D_kQ(k)j_{y,k}-j_{y,b}\eta_b(a-k)\bigr)/(b-k).
\]
For \(x=b\) interchange \(a,b\) and their \(\eta\)'s. If \(x=c\) or \(x=d\), compare the other normal coefficient \(k\), giving
\[
 D_kQ(k)j_{y,k}-j_{y,a}\eta_a(b-k)-j_{y,b}\eta_b(a-k)=0 .
\]
Each gives \(R_0Q(c)+R_1Q(d)=0\), both coefficients units at a verifying reduction for the case. This fixes \(r=Q(c)/Q(d)=-R_1/R_0\) and the two normalized rows independently of the common scale \(Q(d)\).

With \(s=p+q,\ t=pq\), the equation \(Q(c)=rQ(d)\) is affine in \(s,t\). A second affine equation is the **literal** first-stage test \(\varphi_a(JP)=0\): applying the actual primitive to the size-four early-null \(P\) has zero first-high value by strictness. Equivalently
\[
 \mathbf f_a\cdot(J_\xi P)_{\xi\in S}=0,\qquad
 J_\xi P=\xi^4/4-s\xi^3/3+t\xi^2/2 .
\]
The two-by-two determinant is a unit at the chosen reduction in each case, so \((s,t)\) is now fixed over the original Lobatto coefficient field. Recover the physical tilts by
\[
 \theta_a^{-1}=1-\eta_a(b-a)\omega_a,\qquad
 \theta_b^{-1}=1-\eta_b(a-b)\omega_b,\qquad
 \varphi_i=\theta_i\mathbf f_i.
\]
Then \(\tau_i=\eta_i\theta_i\) gives \(\widehat\alpha,\widehat\beta\). Every denominator used in an accepted case has a unit residue. No individual donor roots need to be selected.

## A single actual rooted read closes all 144 cases

The size-five early-null model \(XP\) has ordinary high values \(E(XP)\) because it vanishes at both donors. Its actual unary attachment gives zero at the first dirty, and \(B_{b_d,a_d}\,aP(a)=a\varphi_b(JP)\) at the second, by the literal primitive of the size-four early-null \(P\). At every non-dirty high row it gives \(J_\xi(XP)\) by the true size-six local purity. All early physical values remain zero. True order ten forces \(\mathbf d_3 A\) to kill this actual \(XP\) source (a size-five source, one unary, and the four letters in \(\mathbf d_3\)). Divide by \(\lambda\); the aggregate model and two dirty corrections then give
\[
 0=\sum_{\xi\in S}\omega_\xi J_\xi(XP)
     -\widehat\alpha J_a(XP)
     +\widehat\beta\bigl(a\varphi_b(JP)-J_b(XP)\bigr),\qquad
 J_\xi(XP)=\xi^5/5-s\xi^4/4+t\xi^3/3 .
\]
Neither dirty row is assumed to be primitive-exact on size four.

The 12 ordered dirty labels and 12 ordered first/second distinct clean labels give 144 cases, keeping \(c,d\) in the fixed complement-label order. The displayed scalar has **nonzero** residue in every case: 133 at 227 with radicals \(177,190,149\), and the remaining 11 at 251 with radicals \(76,42,107\). They are reductions of \((x,y,z)=(\sqrt3,\sqrt7,\sqrt{147+42\sqrt7})\) in the authenticated degree-eight field used by the previous packet. Its interior labels are \((1+u)/2\) for \(u\in(-z/21,-xy/z,xy/z,z/21)\). Thus the scalar is nonzero in the original coefficient field and every characteristic-zero extension containing the stated mesh, even if tableau coefficients were not otherwise restricted to it. No approximate roots enter.

## Replay

    sha256sum -c sources.sha256
    python3 check_offmesh.py --emit-lean /tmp/ERK10TwoDirtyOffMeshMod.lean
    lean /tmp/ERK10TwoDirtyOffMeshMod.lean

Core checks exact 144-label coverage, both prime counts and all 144 nonzero pressure values on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. Generic field identities were typed and audited on Mathlib/Lean 4.36.0. The actual rooted bridge and geometry above are mathematical, not a single native all-tableau theorem.
