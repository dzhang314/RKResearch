# External affine root: both finite-gap reflected phases are impossible

Consider strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field. Suppose exactly eight physical components of \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\) vanish at eight distinct clocks, and the reverse pure numerator is affine with a root \(\rho\) outside those labels. The [separate reduction](../sdirk-eight-eight-zero-low-labels/README.md) gives the two distinct silent off rows 1 and 2. This packet treats the silent-eighth and live reflected arithmetic phases. The [actual live-star phase](../sdirk-eight-eight-zero-external-star/README.md) is excluded separately.

**Result.** Both remaining external phases are impossible in characteristic zero. The phase mask and fourth-read elimination do not divide by the constant masked mean or assume weights of any sign. Together with the [dependency ledger](../sdirk-eight-eight-zero-char-zero/README.md), this finishes the exactly-eight-zero exclusion, not a general 11-stage lower bound.

## 1. Literal relative cardinals supply a fixed two-moment plane

Normalize \(A'=A/\gamma\), \(\mathbf x=\mathbf c/\gamma\), \(D=1/\gamma\), \(I_D(T^j)=D^j/(j+1)\). Let \(s=D-1,\ t=s-v,\ r=t-v\) be the actual rear clock labels, and use \(Y=T-t,\ w=\rho-t\). The first five zero clocks have monic polynomial \(P_5\), and
\[
 P_8=P_5 S_3(Y),\qquad S_3(Y)=Y(Y^2-v^2).
\]
Here \(S_3(w)\ne0\) because the root is external. The exact ghost gap satisfies \(H(v)=0\) and the live arithmetic gap satisfies \(T_6(v)=0\) as in the [finite-gap ingress](../sdirk-eight-eight-zero-affine-early-finite/README.md#1-the-affine-cardinal-rows-and-the-individual-jump). Write \(\kappa=1+2v-v^2\), \(Q(v)=4v^3-12v^2+3v+2\), \(H(v)=v^3-4v^2-v+2\).

Let \(B(j)=I_D(P_8/(T-j))\) at any label. Because \(z_iP_8'(x_i)=\Theta(x_i-\rho)\), the literal reverse residual ratios give a nonzero common scale \(\ell\) with \(B(s)=\ell(v-w)\), \(\kappa B(t)=\ell(-w)\). In the ghost \(B(r)=0\); in live arithmetic \(\kappa_3 B(r)=\ell(-v-w)\) and \(H\kappa_3=-\kappa Q\). These relations are from the actual rear rows, not from a reflected tableau with all weights invertible. By cardinal interpolation for the three rear sites \(v,0,-v\), the first three moments \(n_j=I_D(Y^jP_5)\), \(j=0,1,2\), satisfy
\[
 n_j=\lambda(p_{j+1}-w p_j),\qquad
 p_j=\sum_{y_i\in\{v,0,-v\}} a_i y_i^j,
\]
using \(a=(\kappa,-2,0)\) for the ghost or \(a=(\kappa Q,-2Q,-H)\) for live arithmetic, and some \(\lambda\ne0\). For example the three cardinal denominators are \(2v^2,-v^2,2v^2\), respectively; common scalings \(2\kappa v^2\) and \(2\kappa Q v^2\) give exactly the displayed \(a\). The coefficients here are *auxiliary* phase moments and need not be positive. The replay verifies \(v,\kappa\), also \(Q,H\) in arithmetic, are nonzero in the small exact gap fields.

In each phase \(p_3=v^2p_1\). Also \(\Delta=p_0p_2-p_1^2\ne0\): the ghost value is \(-2\kappa v^2\), and in arithmetic the replay checks this element in the exact degree-six gap field with \(T_6(v)=0\). Thus the monic phase mask
\[
 S(Y)=Y^2+s_1Y+s_0,\quad
 s_1=(p_1p_2-p_0p_3)/\Delta,\quad
 s_0=(p_1p_3-p_2^2)/\Delta
\]
annihilates the two rows \((p_0,p_1,p_2)\), \((p_1,p_2,p_3)\). In the ghost \(S=Y(Y-v)\). Consequently the actual ordinary masked row is \(I_D(SP_5)=0\).

## 2. The Cauchy row removes the external root in both actual reads

Use the exact external \(\Lambda_\rho\) defined with the full \(P_8\). Consider any trace of the form
\[
 W=(Y-w)E+(U+VY)P_5
\]
with the two ordinary zero means and Cauchy zero row \(I_D(W)=I_D(YW)=\Lambda_\rho(W)=0\). Put \(E_j=I_D(Y^jE)\). Factoring \(P_8=P_5S_3(Y)\) in the divided means gives
\[
 \Lambda_\rho(W)/P_5(\rho)
 =S_3(w)(E_0+V n_0)-(U+wV)[n_2+w n_1+(w^2-v^2)n_0].
\]
This uses \((S_3(Y)-S_3(w))/(Y-w)=Y^2+wY+w^2-v^2\). Now the phase moment representation gives
\[
       n_2+w n_1+(w^2-v^2)n_0=-\lambda S_3(w)p_0
\]
because \(p_3=v^2p_1\). Cancel the actual nonzero \(S_3(w)\). Since \(n_0=\lambda(p_1-wp_0)\), the Cauchy row becomes \(R_0=0\), where
\[
       R_j=E_j+\lambda(Up_j+Vp_{j+1}),\quad j=0,1,2.
\]
The two ordinary rows are \(R_1-wR_0=0,\ R_2-wR_1=0\), hence all three \(R_j=0\). It follows that \(I_D(S E)=0\). This collapse never divides by \(n_0\) or \(n_1-n_0\), which might vanish in the finite-gap phases.

Write the first three zero labels as \(a,b,c\), the fourth and fifth as \(d,e\). Let \(\sigma=(T-a)(T-b)(T-c)\), \(\xi_d=d-t,\ \xi_e=e-t,\ \tau=(Y-\xi_d)\sigma\). The [actual read-mask model](../sdirk-eight-eight-zero-affine-external-root/READ-MASKS.md) gives the fifth transformed pure error \(W_5=(Y-w)(\tau-J\tau)+(U_5+V_5Y)P_5\). Its preceding literal inputs vanish. Collapse with \(E=\tau-J\tau\) gives \(I_D(S(\tau-J\tau))=0\). At the fourth read write \(E=\sigma-J\sigma\). Its actual error is \(W_4=(Y-w)E+(U+VY)\tau\), with three zero means and Cauchy row zero. Then \((Y-\xi_e)W_4\) satisfies the two means and Cauchy row of the collapse, since \(\Lambda_\rho((Y-\xi_e)W_4)=P_8(\rho)I_D(W_4)+(w-\xi_e)\Lambda_\rho(W_4)\). This yields \(I_D(S(Y-\xi_e)E)=0\). Thus, exactly as in the live-star proof, the late labels satisfy
\[
 \xi_d L_0=L_d,\quad \xi_e L_0=L_e,\quad
 L_0=I_D(SE),\quad
 L_d=I_D(S(Y\sigma-J(Y\sigma))),\quad L_e=I_D(SYE).
\]
Here \(J\) integrates in the original \(T\) coordinate. Neither root recovery is imposed on the singular \(L_0=0\) branch.

For the extra fourth constraint use the unmultiplied ordinary row. Put \(e_j=I_D(Y^j E)\), \(t_j=I_D(Y^j\tau)\), and \(\widetilde E_j=e_{j+1}-\xi_e e_j\). The first two \(R_j=0\) on the multiplied fourth trace give
\[
 \lambda\Delta U=-p_2\widetilde E_0+p_1\widetilde E_1,\qquad
 \lambda\Delta V=p_1\widetilde E_0-p_0\widetilde E_1.
\]
The phase shape gives \(\lambda\Delta=p_0n_1-p_1n_0\) and \(w\lambda\Delta=p_1 n_1-p_2 n_0\). Substitute these into the unmultiplied \(I_D(W_4)=e_1-we_0+U t_0+Vt_1=0\), and use \(n_j=t_{j+1}-\xi_e t_j\). All \(\xi_e\) terms cancel. The resulting necessary equation is
\[
 (p_2t_1-p_1t_2)e_0+(p_0t_2-p_2t_0)e_1+(p_1t_0-p_0t_1)e_2=0 .
\]
This uses only already verified actual-row rank and gives a second line on \(\xi_d\). All ordinary degrees stay at most seven.

## 3. Small exact projections and fixed coprimality certificates

Let \(M_j=I_D(Y^j\sigma)\), \(r_j=M_{j+2}+s_1M_{j+1}+s_0M_j\), and, for \(j=0,1\), put
\[
 F_j=(p_2M_{j+1}-p_1M_{j+2})e_0+
     (p_0M_{j+2}-p_2M_j)e_1+
     (p_1M_j-p_0M_{j+1})e_2 .
\]
The actual ordinary \(I_D(SP_5)=0\), the two root lines, and the extra fourth line give the same two cleared equations as in the star:
\[
 A_0=L_0^2 r_2-L_0(L_d+L_e)r_1+L_dL_e r_0=0,\qquad
 A_1=L_0 F_1-L_d F_0=0.
\]
If \(L_0=0\), both \(L_d,L_e\) must also vanish. No rank at a residue sample is being used as an exact necessary condition.

The exact initial field is the verified field of \(u+b+2v\), degree 18 for ghost and 36 for arithmetic. The genuine forward \(a,b,c\) gates include \(C_3(c;D)=\ell_2c^2+\ell_1c+\ell_0=0\). When \(\ell_2\ne0\), use \(L=\ell_2 c\) in its monic quadratic. The exact scaled norms have the same degree table as the star:
\[
\begin{array}{c|c|c}
\text{equations}&\text{raw degrees}&\text{guarded degrees}\\ \hline
L_0,L_d,L_e&20,22,22&16,18,18\\
A_0,A_1&62,58&46,42 .
\end{array}
\]
Only exact powers of \(\ell_2\) or \(D\) are removed. At the fixed simple primitive residues, both norm groups retain all their degrees and have constant gcd. At the leading drop use the preserved-degree \(\ell_2\), \(\ell_1\) a unit there, and substitute \(c=-\ell_0/\ell_1\) after clearing the indicated powers; both common gcds are again constant.

| Phase | Fixed simple primitive residue \((p,z_0)\) | Singular / generic / two leading-drop gcd degrees |
|---|---:|---:|
| Ghost | \((59,1)\) | \(0,0,0,0\) |
| Live arithmetic | \((103,65)\) | \(0,0,0,0\) |

The degree-preserving reductions force any hypothetical diagonal root integral under an extension of the valuation from the chosen simple residue embedding. The constant gcds are checks of whole polynomials, so include nonsplit geometric roots. The characteristic-zero contradiction is not a finite-sample inference and does not assert positive-characteristic nonexistence.

## 4. Replay and verification scope

Run `python check_external_finite.py PHASE` for `PHASE=ghost,arith` with SymPy 1.14 and Python-flint 0.8. Both fixed exact arithmetic replays are tested; no prime search is run. The [Lean companion](../../lean/RKCert/Research/SDIRKEightEightZeroExternalFinite.lean) is **staged scalar source** (not a fresh stock build in this packet). It states the phase-moment cancellations over a commutative ring. The actual tableau ingress, Cauchy transformation, and number-field comparisons are the source proof, not an end-to-end native theorem.
