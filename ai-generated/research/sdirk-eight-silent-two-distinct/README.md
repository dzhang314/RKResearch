# Closing the last two invisible one-clock stages at strict SDIRK8

Consider an actual ten-stage strict SDIRK tableau of order at least eight over a characteristic-zero field. Exactly two physical stages have a nonzero quadratic residual, both weights are zero, and their physical clock is the same. The [unequal-tag](../sdirk-eight-silent-two-unequal/README.md), [equal-tag low](../sdirk-eight-silent-two-low/README.md), [midpoint and seven-active](../sdirk-eight-silent-two-high/README.md), and [Gauss-double](../sdirk-eight-silent-two-gauss-double/README.md) exclusions reduce the problem to equal tags, \(r_2=1\), non-midpoint diagonal, and eight distinct active zero-residual clocks. This packet closes that last chart. Thus **two individually invisible stages at one physical clock are impossible** in this family. A single invisible stage and distinct invisible physical clocks are not covered. No change to the unrestricted **10–11** interval.

## 1. Necessity of the affine profile without dividing by it

Let \(\boldsymbol w=\boldsymbol b^{\mathsf T}M\), \(\boldsymbol h=(A-\gamma I)\boldsymbol g\), \(x=1-\gamma=c_{10}\), and \(p(X)=L_4(X)=70X^4-140X^3+90X^2-20X+1\). The two invisible stages are stage one and one of physical \(6,7,8\), both at \(\gamma\). Their \(h\) values are zero, and their \(w\) values sum to zero. On actual active coordinates the supported pure reverse row gives
\[
 \boldsymbol h^{\mathsf T}B=\lambda \boldsymbol w(C-\gamma I),
 \qquad \lambda\ne0 ,
\]
by non-midpoint, \(r_2=1\), and the active nonzero front defect. For the eight distinct active clocks let \(D(X)\) be their monic nodal polynomial. The site numerators of \(\boldsymbol w\) and \(w_i h_i\) have degrees at most one and four: the six and three paid scalar moments vanish, including the invisible sites whose contributions cancel. Write those numerators \(T,S\), so
\[
  T(c_i)=D'(c_i)w_i,\qquad S(c_i)=T(c_i)h_i .
\]
Ordinary precision seven and the paid \(b h\) moments imply \(I(S f)=0\) for all cubics \(f\), using \(\deg(Tf)\le4\). Hence \(S=\sigma p\), with \(\sigma\ne0\) since the two literal front \(h\)'s and their \(w\)'s are nonzero at distinct clocks. Thus \(p(c_i)=q(c_i)h_i\) with \(q=T/\sigma\) affine, and \(q\) is not the zero polynomial. No division by \(q(c_i)\) occurs below, so constant \(q\), coprime affine \(q\), and a root shared with \(p\) are all retained.

Denote the normalized front clocks by \(A_0=a/\gamma,B_0=b/\gamma\) and their normalized defects \(H_a=h_a/\gamma^3,H_b=h_b/\gamma^3\). In the exact calculations we scale the affine profile as \(Q(X)=Q_0+Q_1 X\), where
\[
 Q_0=\gamma\{B_0 H_b p(\gamma A_0)-A_0H_a p(\gamma B_0)\},
 \quad Q_1=H_a p(\gamma B_0)-H_b p(\gamma A_0).
\]
Equivalently \(Q(c_i)(h_i/\gamma^3)=\Lambda p(c_i)\) with \(\Lambda=\gamma(B_0-A_0)H_a H_b\ne0\). This normalization uses only the two actual nonzero front values. Both \(p(a),p(b)\ne0\): if \(Q\) vanished there then \(T\) and \(w\) would vanish there, forcing \(h=0\). The same argument at the nonzero terminal weight (\(w_{10}=-\gamma^2b_{10}\ne0\)) gives \(Q(x),p(x)\ne0\), so \(p(\gamma)\ne0\) by reflection.

## 2. Literal finite diagonal, gap, and row-four projections

Let \(u=(x-c_9)/\gamma\ne0\), \(k=1+2u-u^2\), \(c=x-\gamma u\). The actual terminal and penultimate reverse reads give
\[
 F_9^{\rm raw}=(x-\gamma)p(c)Q(x)-k(c-\gamma)p(x)Q(c)=0.
\]
Exactly divide by the artificial factor \(u\). When physical stage eight is silent, it is the second invisible and its clock is \(\gamma\). The actual two successor taps require \(F_8=2(\gamma-x)-\gamma k(u-2)=0\). When eight is active, its literal reflected clock \(d\) is \(x-\gamma(2-u)\) in star or \(x-2\gamma u\) in arithmetic. The analog of \(F_9^{\rm raw}\) at \(d\) uses normalized reverse residual \(k\) in star and, in arithmetic, the exact cleared pair
\[
 H=-2+u+4u^2-u^3,\quad
 H k_d=(1+4u-4u^2)H+4u^2(3u-2).
\]
We use the cleared polynomial and do not divide by the reverse residual, by \(H\), or by either profile evaluation.

The exact resultant in \(u\) of \(F_9^{\rm raw}/u\) and the selected \(F_8\) is nonzero in all six front/rear types. Its only discarded diagonal factors divide \(\gamma(2\gamma-1)p(\gamma)p(a)p(b)Q(x)\), already nonzero. The squarefree retained diagonal degrees in rear order silent, star, arithmetic are \(29,34,73\) for the star front and \(29,40,68\) for the arithmetic front. Their exact irreducible factors have degrees
\[
 (29),\ (4,4,8,8,10),\ (8,10,55)
 \quad\hbox{and}\quad
 (29),\ (8,9,10,13),\ (8,10,50)
\]
respectively. The method also works if a projection factor contains only an infinity artifact: after specializing there, the actual leading degree of the necessary gap polynomial is computed in characteristic zero and the finite nonzero remaining degree is used.

Physical row four is active and precedes the second invisible. Its normalized clock \(s=c_4/\gamma\) and literal normalized defect \(H_4(s)\) are computed from the three actual strict taps at \(1,A_0,B_0\), replacing the third moment coefficient of the sole invisible donor by \(2/3\). The profile requires \(Q(\gamma s)H_4(s)-\Lambda p(\gamma s)=0\). This polynomial has the two exact factors \(s-A_0,s-B_0\): padded earlier rows solve those literal equations, and an actual repeat is excluded by the same unique strict tap solve and stage saturation. Divide by these factors **before** any reduction. Every retained exact diagonal factor now has a positive finite row-four degree. Both this degree and the specialized gap degree are checked in every chosen reduction component.

## 3. A linear nodal identity, including shared roots

Define \(W_D(X)=I_t((D(X)-D(t))/(X-t))\) and \(E_p(X)=I_t((p(X)-p(t))/(X-t))\), where \(I_t\) is ordinary exact polynomial integration on \([0,1]\). The degree-seven Lagrange cardinal gives \(W_D(c_i)=b_i D'(c_i)\). Since \(T\) is a nonzero scalar multiple of \(Q\), the two pointwise transport equations imply
\[
 p(c_i) W_D(c_i)=\xi(c_i-\gamma) Q(c_i)^2
\]
for a common scalar \(\xi\). This is a cross multiplication, not a division by \(p\) or \(Q\). The polynomial \(p W_D-E_pD\) has degree at most three. One way to see this is to use the formal series \(J(X)=I_t((X-t)^{-1})\): \(W_D,E_p\) are the polynomial parts of \(DJ,pJ\). The negative part \(pJ-E_p=I_t(p(t)/(X-t))\) starts at \(X^{-5}\) by the four \(L_4\) orthogonality moments, while \(DJ-W_D=O(X^{-1})\). Therefore
\[
 pW_D-E_p D=D(pJ-E_p)-p(DJ-W_D)
\]
has polynomial degree at most three. The identity at eight distinct physical clocks then gives
\[
 \boxed{pW_D-E_pD=\xi(X-\gamma)Q^2.}
\]
The left side is linear in the coefficients of \(D\). In the [arithmetic replay](nodal.py) the coefficient of \(X^j\) in \(W_D\) is simply \(\sum_{k>j}D_k/(k-j)\).

If eight is active the six distinct pegs \(a,b,c_4,c_9,c_8,x\) leave a monic quadratic factor of \(D\). Its two coefficients and \(\xi\) satisfy four linear equations from the boxed identity. The augmented \(4\times4\) determinant is a unit in every retained tail/row-four fiber, so there is no solution. If eight is silent then the five distinct pegs \(a,b,c_4,c_9,x\) leave a monic cubic. The corresponding square \(4\times4\) system has unit determinant in every fiber, hence reconstructs that cubic.

In the latter case physical row five is one of the three unknown roots, and precedes the second invisible. Write its normalized clock \(y=c_5/\gamma\), normalized defect \(H_5=h_5/\gamma^3\). The actual stage-one strict tap is \(2H_5\) in scaled units. The other strict taps at \(A_0,B_0,s\) are fixed by the moments
\[
 y-1-2H_5,\quad y^2/2-y-2H_5,\quad y^3/3-y^2-4H_5/3 .
\]
These solve a guarded Vandermonde; the last equation uses the literal cubic residual \(2H_5/3\) at a quadratic-zero row. Compute the actual values of \(A\boldsymbol h\) and \(\boldsymbol\tau_4=A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\) from those taps. The four physical columns \(\boldsymbol h,C\boldsymbol h,A\boldsymbol h,\boldsymbol\tau_4\) lie in \(F_4|_U\) of rank three. Their determinant on rows two through five must vanish. The last row gives an affine polynomial \(D_0(y)+H_5 D_1(y)\). Multiply by \(Q(\gamma y)\) and substitute \(\Lambda p(\gamma y)\) for \(Q(\gamma y)H_5\). The resulting polynomial \(Q(\gamma y)D_0(y)+\Lambda p(\gamma y)D_1(y)\) is necessary even at a shared zero of \(p,Q\). Its multiplication determinant in the reconstructed monic cubic is a unit in all four silent fibers, which excludes them without a shared-root assumption. See [fifth.py](fifth.py).

## 4. Exact replay and lift

Run `python3 check_eight.py` with `sympy==1.14.0` and `python-flint==0.9.0` against the earlier sibling chart code. This is an offline finite proof, not a bounded numerical search. It uses the fixed reductions \((1009,285),(1039,315)\) for \(t^2=1/2\); the latter covers one degree-eight and one degree-thirteen factor.

For each exact irreducible diagonal factor, localize the coefficients of \(\mathbb Q(t)\) at the selected prime and take the monic diagonal quotient. Its reduced factors are all checked, with squarefree reduction and denominator guards. The true characteristic-zero gap degree is computed by polynomial remainders modulo that diagonal factor; its leading coefficient is a unit on **every** reduced diagonal component. The same holds for the row-four polynomial after the exact twin factors are removed. Therefore the joint diagonal/gap/row-four algebra is finite over the local base with fixed monic bases. Further quotient by the required \(F_8\). In each reduced diagonal field the gcd of the two gap equations is factored and every irreducible factor is retained. If this gcd is a unit, that component has no solutions (there was no degree loss in the finite gap polynomial). If a reduced gap factor has multiplicity, unit checks in its residue field also hold in the Artinian component; no roots are deleted by modular-only saturation. The final active determinant, or the silent square-system pivot and final cubic multiplication determinant, is checked on every retained component. The unit checks lift in the fixed finite algebras: a finite quotient with no reduced components cannot give an actual characteristic-zero solution. The chosen prime is not assumed to be a prime of good reduction for the hypothetical tableau itself.

The [Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8InvisibleNodalTransport.lean) verifies the denominator-free scalar identity over commutative rings and its bounded-degree global consequence for distinct clocks over fields. It compiled in Lean/Mathlib 4.36.0 with standard axioms. The saturation reductions and computational units above are the exact source-level proof, not an end-to-end Lean bound theorem.
