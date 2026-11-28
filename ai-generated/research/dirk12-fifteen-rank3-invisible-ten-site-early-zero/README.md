# DIRK12/15: the earliest extra reflected zero on the ten-site grid

Work in the [actual ten-site quotient](../dirk12-fifteen-rank3-invisible-four-ghost-variable-grid/README.md) for real ordinary fifteen-stage order-twelve \(C(2),f_5=3\), invisible weighted forward cubic, and four distinct cubic-dirty ghosts. There are ten distinct **nonterminal live** numerical labels; the true weighted reverse cubic \(\mathbf G\) is nonzero at each, with label values \(\rho/D'(y)\). Through grade five, \(\mathcal B_j=\mathbf G P_{j-3}(\mathbf y)\). The [true grade-six ghost kernel](../dirk12-fifteen-rank3-invisible-four-ghost-variable-high-sites/reverse-grade-six.md) is \(\mathbf G P_3(\mathbf y)\). In particular no nonterminal live row is clean for the whole grade-five flag.

Suppose there is an extra live row at numerical reflected clock zero (in addition to the literal terminal). It cannot occur before the second distinct nonzero live label. In this note suppose it occurs in its **earliest possible position**, after the first two nonzero live labels \(d,v\) and before the third \(u\). Then the actual third diagonal is zero and
\[
                 (r^2-4r+1)t+r(r+1)=0,\qquad r=v/d,\quad t=u/d.
\]
In addition the top \(L_7'\) coefficient \(\gamma\) of the two ordinary ghost-tap modes is necessarily nonzero, and an exact grade-six mixed equation fixes \(\alpha/\gamma\). This is a restriction on one chronology, not a new real stage minimum; the interval remains **15–16**.

## Live first clocks and two true quadratic ratios

Normalize the reverse clock and actual matrix by \(1/d\), so the early live physical rows after the literal terminal are \(1,r,0,t\). No ghost has any weight or low weighted defect. A nonterminal live reflected zero earlier than the first two nonzero labels would have \(\mathbf G=0\): its exact leading \(X\) moment kills the aggregate tap to the only possible earlier nonzero clock, so it also has zero \(X^2\) primitive. This contradicts the complete ten-site barycentric support. Hence the selected chronology is literal, including any interspersed unweighted ghosts.

Use \(\sigma=G_{1}/b_1=1/6\), and \(g=G_r/b_r\ne0\), in normalized units. The true \(\mathbf E_4/\mathbf G\) is affine, where \(\mathbf E_4=N\mathbf W(X^3)-\mathbf W(X^4)/4\). Its value is \(3/2\) at the first nonzero row \(1\). At the actual live zero, writing \(g_0=G_0/b_0\ne0\) for that nonterminal row, the true \(X\) and \(X^2\) moments give taps \(T_1=-g_0/(r-1),\ T_r=g_0/[r(r-1)]\). Thus the affine ratio has value \(r+1\) there, and is
\[
                               \varphi(X)=r+1+(\tfrac12-r)X .
\]
At the first \(r\)-row the actual taps are \(T_1=(r^3/6-g)/(r-1)\) and \(T_r=r/2-T_1/r\) from the true \(X,X^2\) moments. Computing its cubic-input error and using \(\varphi(r)\) gives the exact equation \(6(2r-1)g+r^2(r-2)=0\). Since \(r\ne0\) and \(g\ne0\), this rules out \(r=1/2,2\). Hence
\[
 g=-\frac{r^2(r-2)}{6(2r-1)},\qquad
 p_1=\frac{r^2(r+1)}{3(2r-1)},\qquad p_r=\frac{r(4r-5)}{6(2r-1)},
\]
where \(p_1,p_r\) are the actual taps at \(r\).

The exact grade-five ratios \(\chi,\psi\in P_2\) for the scalar quartic-input discrepancy and for the actual lift \(N(Y\mathbf G)\) are fixed on \(0,1,r\):
\[
\begin{array}{c|ccc}
   X&0&1&r\\ \hline
 \chi=(\mathbf E_5/\mathbf G)&r^2+r+1&9/5&(p_1+r^4p_r-r^5/5)/g\\
 \psi=(N(Y\mathbf G)/\mathbf G)&(g-\sigma)/(r-1)&1/2&
                           (\sigma p_1+rgp_r)/g .
\end{array}
\]
At the extra live zero, the zero-clock sources (the literal terminal and its diagonal) disappear from the \(Y\mathbf G\) read; the expressions use its true physical \(g_0\ne0\) and do not require its value to equal a particular scalar. No grade-six reverse condition has been used yet.

## Third nonzero clock and its actual zero diagonal

At \(t\), write \(h=G_t/b_t\ne0\) in normalized units. The three nonzero aggregate scalar taps satisfy
\[
 T_x=\frac{J[X(X-a)(X-b)](t)+(\varphi(t)-a-b)h}
                   {x(x-a)(x-b)},\qquad
      \{x,a,b\}=\{1,r,t\},
\]
from the actual scalar inputs of degrees \(1,2,3\). The true duplicated zero clocks do not enter these cardinals. The quartic nodal test \(X(X-1)(X-r)(X-t)\) then gives the affine-in-\(h\) equation
\[
 E(h)=J[X(X-1)(X-r)(X-t)](t)
  +[\chi(t)-(1+r+t)\varphi(t)+(r+t+rt)]h=0 .
\]
The genuine \(N(Y\mathbf G)\) row gives the quadratic in \(h\)
\[
 F(h)=\sigma T_1+rgT_r+t h T_t-\psi(t)h=0.
\]
Writing \(E=A h+B,\ F=q_2 h^2+q_1 h+q_0\), exact expansion yields
\[
 q_2 B^2-q_1 AB+q_0 A^2
       =\frac{t^5(r-t)(t-1)[(r^2-4r+1)t+r(r+1)]^2}
                          {200(r-2)^2(2r-1)} .
\]
This does not divide by \(A\); the common-root identity makes the left side zero. All prefactors are nonzero and the claimed normalized ratio follows. Put \(D=r^2-4r+1,\ P=r^2-3r+1,\ W=5r^2-14r+5\). The clocks guard \(D\ne0,r+1\ne0\), and \(t=-r(r+1)/D\). At that value the affine coefficient is \(3r^2(r+1)^2 P/[10(r-2)D^2]\), and if \(P\ne0\) the exact solution is
\[
                     h_*=-\frac{r^2(r-2)(r+1)W}{6D^3},
                     \qquad T_t=0 .
\]
If \(P=0\), then \(t=r+1\) and \(A=B=0\); the actual polynomial \(F\) is \(q_2(h-h_*)^2\) after the exact quadratic specialization. Its quadratic coefficient is \((1/2-r)t/[(t-1)(t-r)]\ne0\). Thus the same \(h_*\) and zero diagonal are forced. In all cases \(W\ne0\) as \(G_t\ne0\).

## The fourth nonzero label forces a nonzero grade-six divided difference

Let \(w\) be the next actual live nonterminal label after \(t\), necessarily nonzero and different from \(1,r,t\). Let \(\mathbf Z=N(Y^2\mathbf G)\), an actual grade-six vector. The four observed ratios \(Z_i/G_i\) on \(0,1,r,t\) are
\[
 \frac{rg-\sigma}{r-1},\qquad
 \tfrac12,\qquad
 \frac{\sigma p_1+r^2g p_r}{g},\qquad
 \frac{\sigma T_1^{(t)}+r^2g T_r^{(t)}}{h_*}.
\]
The last omits the actual zero diagonal at \(t\). Let \(Q_3\) interpolate those four values; the claim is \(Z_w/G_w\ne Q_3(w)\).

At \(w\), write \(h_w=G_w/b_w\ne0\). For \(x\) among \(1,r,t,w\) and the other three nonzero labels \(a,b,c\), the actual scalar tap from the first four nonconstant degrees is
\[
 T_x=\frac{J[X(X-a)(X-b)(X-c)](w)
       +[\chi(w)-(a+b+c)\varphi(w)+ab+ac+bc]h_w}
                        {x(x-a)(x-b)(x-c)}.
\]
The row for the genuine \(\psi\) ratio yields the quadratic equation
\[
 F_4(h_w)=\sigma T_1+rgT_r+t h_*T_t+w h_w T_w-\psi(w)h_w=0.
\]
If the observed new \(\mathbf Z/\mathbf G\) were \(Q_3(w)\), its row minus \(w\) times the \(\psi\) row would also give the affine condition
\[
 E_4(h_w)= (1-w)\sigma T_1+r(r-w)gT_r+t(t-w)h_*T_t
                          -(Q_3(w)-w\psi(w))h_w=0.
\]
Here the extra live zero contributes neither to \(Y\mathbf G\) nor to \(Y^2\mathbf G\); it is not deleted from the underlying matrix. The replay verifies the guarded common-root eliminant, with the same coefficient convention \(E_4=A h_w+B,\ F_4=q_2 h_w^2+q_1 h_w+q_0\):
\[
 q_2 B^2-q_1AB+q_0A^2=
 \frac{r w^5(r+1)(r-w)(w-1)(r^2-r+1)
                         [Dw+r(r+1)]^3}
      {200(r-2)(2r-1)^2 D^2 W^2}\ne0 .
\]
All literal guards were paid above; \(Dw+r(r+1)=D(w-t)\ne0\), and \(r^2-r+1>0\) over the reals. A common root is therefore impossible without any leading-pivot division. We have proved the actual fourth divided difference of \(\mathbf Z/\mathbf G\) on \(0,1,r,t,w\) is nonzero.

## Mixed ordinary/reverse consequence

Restore physical units. If \(C_Z,C_E\) are the fourth divided differences on these five physical labels of \(\mathbf Z/\mathbf G\) and \(\mathbf E_6/\mathbf G\), respectively, then \(C_Z\ne0\); normalization multiplies both by the same nonzero scaling power. The exact ghost feeds are \(\mathbf Z_{\rm ghosts}=-24024\rho\gamma\boldsymbol\ell\) and \((\mathbf E_6)_{\rm ghosts}=(\alpha/462-24024\gamma\varepsilon_{12})\boldsymbol\ell\). Their proper cancelling combination belongs to the live grade-six kernel \(\mathbf G P_3(\mathbf y)\), whose fourth divided difference is zero. Consequently
\[
         C_Z\alpha/462+24024(\rho C_E-\varepsilon_{12}C_Z)\gamma=0 .
\]
Exact rank two of the ordinary ghost-tap matrix rules out \(\alpha=\gamma=0\), so \(\gamma\ne0\) and \(\alpha/\gamma=462\cdot24024(\varepsilon_{12}-\rho C_E/C_Z)\). Substitution in the true ordinary \(10\times5\) bridge again leaves four unknown coefficients for fixed geometry. The degree-twelve scalar discrepancy stays unpaid; the result does not claim an unrestricted stage exclusion.

Execute the accompanying exact Python/SymPy replay with no numerical tableaux or reductions of unknown real coefficients. The arguments and resultant here are analytic, not a new native theorem for the actual ten-site chart.

    python3 -B verify.py
