# Mixed grade-six elimination for the early nine-site return

Assume the nonzero-mass early-return chart of the [nine-site chronology](README.md). The first actual nonterminal live rows are \(d_1,v,d_2,u\), and the first additional distinct live label after \(u\) is \(w\), allowed to be the duplicate numerical reflected zero if such a live row exists. Intervening ghosts have no weighted cubic or head entries. All ratios below refer to genuine weighted defects and only normalize live physical weights.

Let \(\alpha,\gamma\) be the ordinary ghost-tap Jacobi coefficients from the [rank-two tap profile](../dirk12-fifteen-rank3-invisible-four-ghost-variable-high-sites/tap-rank-and-moments.md). This whole early-return chart requires \(\gamma\ne0\). More precisely the grade-six reverse ghosts give an **explicit value of \(\alpha/\gamma\)** from the scalar grid and its genuine early reverse reads. In particular, after the other scalar data are fixed, the ordinary first-four-live \(10\times5\) moment bridge reduces to a \(10\times4\) linear system. This is a condition on the existing equality chart, not a new unrestricted lower bound.

## A nonzero divided difference of the actual grade-six lift

First use normalized reverse units, scaling both numerical clock and actual \(N\) by \(1/d\) as in the chronology. Write \(1,r,t\) for \(d,v,u\), \(\sigma=1/6,\ \lambda=3(r-1)(r-2),\ k=(r-\tfrac12)/\lambda,\ D=r^2-4r+1,\ W=5r^2-14r+5\). The head at \(t\) is \(h_*=-r^3(r+1)^2(2r-1)W/[36(r-1)D^4]\) and its actual diagonal is zero, including the zero-pivot exception. Thus \(W\ne0\). The two true affine polynomials \(\varphi,\psi\) for the quartic-input error and \(N\mathbf H\) are as in the chronology note.

Let \(\mathbf Z=N(Y\mathbf H)\) be the **genuine** grade-six lift. For each of the four distinct labels \(1,r,t,w\), read \(z_x=Z_i/H_i\), using the second \(1\)-row if \(x=1\). All denominators \(H_i\ne0\) come from the true nine-site barycentric head. At the first three such labels, causality and the previous affine head give
\[
 z_1=\psi(1)+h_r/(r k),\qquad
 z_r=r\psi(r),\qquad
 z_t=\psi(t)+(r-1)h_r T_r^{(t)}/h_* .
\]
Here \(T_r^{(t)}\) is the actual scalar aggregate tap at \(t\) to the earlier \(r\)-row. Indeed subtract \(xN\mathbf H\) from the literal row of \(\mathbf Z\) at each actor, and use the previously determined \(r\)-tap or the zero diagonal at \(t\). Let \(Q\in P_2\) interpolate these three ratios. We claim \(z_w\ne Q(w)\).

**A nonzero fourth label \(w\).** At its actual first live row, the only possible prior nonzero scalar inputs are \(1,r,t\); any prior ghosts have zero weights, and the previous chronology excluded extra live zero through \(t\). Let \(h=H_i/b_i\ne0\). The actual aggregates \(T_1,T_r,T_t,T_w\) to the four scalar labels, including its possible diagonal, follow from the true input degrees one to four. For \(x\in\{1,r,t,w\}\), with the other three nonzero labels \(p,q,s\), they are
\[
        T_x=\frac{J[X(X-p)(X-q)(X-s)](w)
                    +\left(\varphi(w)-\lambda(p+q+s)\right)h}
                         {x(x-p)(x-q)(x-s)}.
\]
As before the literal \(N\mathbf G\) equation identifies the extra split tap by \(\delta T_{1_2}=h-\sigma T_1\). Therefore the actual \(N\mathbf H\) equation is the quadratic identity
\[
 F(h)=(k+T_w-\psi(w))h+h_rT_r+h_*T_t-k\sigma T_1=0.
\]
If \(z_w=Q(w)\), subtract \(wN\mathbf H\) from the actual \(\mathbf Z\) read. That makes the second identity linear in \(h\):
\[
 E(h)=(1-w)k(h-\sigma T_1)
                +(r-w)h_rT_r+(t-w)h_*T_t-(Q(w)-w\psi(w))h=0.
\]
The exact arithmetic replay constructs the coefficient lists \(E=e_1h+e_0,\ F=f_2h^2+f_1h+f_0\) from the genuine row taps and verifies
\[
 f_2e_0^2-f_1e_0e_1+f_0e_1^2=
 -\frac{r w^3(r+1)(r-w)(w-1)(r^2-r+1)
                    (Dw+r(r+1))^3}
             {1200(r-1)(r-2)^2(2r-1)D^2 W^2}.
\]
A common root would make the left side zero without any division by \(e_1\). The right side cannot vanish: all clock factors are guarded, \(Dw+r(r+1)=D(w-t)\ne0\), and \(r^2-r+1>0\) over the reals. Thus \(z_w\ne Q(w)\).

**A new live zero label \(w=0\).** The actual scalar quartic relation on \(0,1,r,t\) at this row requires \(\varphi(0)=(1+r+t)\lambda\), since \(h\ne0\), and the three nonzero aggregate taps satisfy the exact zero leading moments. The replay gives
\[
 \varphi(0)-(1+r+t)\lambda=
     \frac{9r(r-1)(r+1)(3r^2-7r+3)}{5(2r-1)D}.
\]
This rules out \(r^2-3r+1=0\) in this zero-label position, as the remaining quadratic reduces to \(2r\ne0\). For the other \(r\), the three taps divided by \(h\) are \(\lambda\) times the leading cubic coefficients of the node cardinals on \(0,1,r,t\). The actual \(\mathbf Z/H\) read has no current diagonal term, because \(Y=0\) here. It differs from the same earlier quadratic by
\[
 z_0-Q(0)=
 -\frac{3r(r-1)^2(r+1)^2(r^2-3r+1)(r^2-r+1)}
                 {4(r-2)(2r-1)D^2 W}\ne0 .
\]
This treats a duplicate numerical zero without pretending its own weight or head is zero.

Thus the third divided difference of \(\mathbf Z/\mathbf H\) on these four distinct labels is nonzero. The conclusion is true in physical units as well: restoring \(d\) multiplies the ratios by \(d^2\) and the third divided difference by \(1/d^3\). The analytic proof did not assume that \(\mathbf Z\) had zero ghosts, or that any nonterminal singleton was clean.

## The actual ghost feeds solve the coefficient ratio

Return to physical clock \(y\) and matrix \(N\). Let \(\mathbf E_6=N\mathbf W(X^5)-\mathbf W(X^6)/6\) and let \(\rho\ne0\) be the barycentric scalar of the genuine aggregate \(\mathbf H\) on the nine nonterminal live labels. The [two exact ghost feeds](../dirk12-fifteen-rank3-invisible-four-ghost-variable-high-sites/reverse-grade-six.md) are
\[
 \mathbf Z_{\rm ghosts}=-24024\rho\gamma\,\boldsymbol\ell,\qquad
 (\mathbf E_6)_{\rm ghosts}
    =(\alpha/462-24024\gamma\varepsilon_{12})\,\boldsymbol\ell,
 \quad\varepsilon_{12}=\sum_i b_i c_i^{12}-1/13 .
\]
The unpaid \(\varepsilon_{12}\) is an actual scalar discrepancy, never set to zero. The ghost-zero subspace of the genuine \(\mathcal B_6\) is precisely \(\langle\mathbf G,\mathbf H,Y\mathbf H,Y^2\mathbf H\rangle\). On the first \(d\)-row, \(\mathbf E_6/\mathbf G=2d^3\) by the actual diagonal \(d/2\), while \(\mathbf Z=\mathbf H=0\) at that row.

At the four chosen live labels define
\[
 C_Z=\sum_s \frac{(Z_i/H_i)}{\prod_{q\ne s}(s-q)},\qquad
 C_E=\sum_s \frac{((E_{6,i}-2d^3 G_i)/H_i)}{\prod_{q\ne s}(s-q)} .
\]
These are taken in physical \(y\) with the same second \(d\)-row convention, and \(C_Z\ne0\) by the previous section. A true linear combination of \(\mathbf E_6\) and \(\mathbf Z\) cancelling their ghosts has no surviving third divided difference after subtracting its known \(\mathbf G\) component. Equivalently,
\[
              \frac{C_Z\alpha}{462}
               +24024(\rho C_E-\varepsilon_{12} C_Z)\gamma=0 .
\]
If \(\gamma=0\), \(\alpha=0\) follows, contradicting independent ordinary ghost rows at the first two live nonzero clocks. Thus
\[
            \frac{\alpha}{\gamma}
                  =462\cdot24024\left(
                       \varepsilon_{12}-\rho C_E/C_Z\right).
\]
This is the desired mixed coefficient elimination in the \(10\times5\) ordinary moment system: replace the \(\alpha\) column by its displayed multiple of \(\gamma\). If both the actual scalar grid and ghost amplitudes are specified, the remaining calculation is linear in \(\mu,\nu,\gamma,\eta\), with \(\nu,\gamma\ne0\). No exact general real hull solution or unrestricted stage exclusion is asserted.

## Replaying and extending

Run the local exact symbolic script (Python with SymPy) to reconstruct the third, fourth nonzero and fourth zero identities from the true cardinal formulas. The analytic couple between the two respective actual flags is not a complete native theorem. The root calculations use only characteristic-zero arithmetic and the real nonzero bound for \(r^2-r+1\); signed physical weights and the possible unpaid scalar discrepancy are retained.
