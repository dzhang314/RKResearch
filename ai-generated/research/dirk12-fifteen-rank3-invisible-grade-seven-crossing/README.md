# DIRK12/15: true grade-seven split-free crossing on the two early reverse charts

Use the real ordinary order-twelve \(C(2),f_5=3\) invisible four-distinct-dirty-ghost frame on either the nine-site early reverse return with unique literal terminal or the ten-site earliest extra reflected zero. By the [complete nine-site terminal-repeat exclusion](../dirk12-fifteen-rank3-invisible-nine-site-fourth-terminal-exclusion/README.md), all first five ordinary nonzero live clocks are different from 1 in both charts. Thus their five reflected clocks are nonzero, including \(E=1-e\) and \(w=1-f\) for the fourth and fifth ordinary live nonzero rows.

The exact grade-seven crossing below uses uniquely determined aggregate weights and paid rooted spaces, with no physical weight split. It supplements, rather than replaces, the true grade-six mixed \(\alpha/\gamma\) relation. It does not eliminate all scalar candidate grids or change the real DIRK12 interval **15–16**.

## Late ordinary fourth and third rows read without unknown taps

After the early reverse \(d,v,d,u\) (nine sites) or \(d,v,0,u\) (ten sites), the next two actual reverse nonterminal live receivers are \(w,E\). The earlier [fourth-diagonal theorem](../dirk12-fifteen-rank3-invisible-nonzero-fourth-exclusion/README.md) gives literal \(A_{ee}=0\), and \(E\) is a singleton, so its reverse self tap is zero. Its four remaining nonzero-clock taps to \(d,v,u,w\) are exactly determined by paid scalar input degrees 1 through 4, using the actual barycentric amplitude at \(E\) and the same elementary cardinal formula as at \(w\). Zero-clock source terms may be present in the physical rows but make zero contribution to the positive scalar and positive-clock lift reads. At nine sites the only nontrivial repeated physical source split obeys \(\Delta T_{d_2}=h_E-\sigma T_d\) from the true \(\mathbf H=N\mathbf G-(d/2)\mathbf G\), giving the \(\mathbf H\) contribution \(k(h_E-\sigma T_d)\) without a pair split.

The same taps test the paid low \(\psi\) lift at \(E\), the mixed grade-six ghost-zero polynomial already determined through \(w\), and the literal bridge \(B_wA_{f,e}=d B_E T_w\). The ordinary live-only normalized read of the quartic \(P=T(T-1)(T-x)(T-y)\) at \(f\) has only its \(e,f\) sources, so \(A_{f,e}P(e/a)=a\mathcal A(P)(f/a)-A_{ff}P(f/a)\). The diagonal \(A_{ff}\) follows from the corresponding nodal quintic.

For the subsequent reflected \(C=1-c\) (ordinary third nonzero live receiver), its own diagonal is already known as \(a\omega\). The ordinary cardinal supported at the third ordinary live clock, of degree three and zero on \(0,a,b\), determines the actual \(A_{e,c}\) at \(e\). These two known physical reverse coefficients let us subtract the sources \(E,C\), again leaving a four-source exact degree-1-to-4 solve on \(d,v,u,w\). The same \(\psi\), cleared grade-six mixed continuation, and direct \(A_{f,c}\) gates are exactly computable; the latter ordinary read subtracts the known \(e\) and \(f\) sources of the third-clock cardinal. See [the exact E and C receiver code](next_reverse.py).

## The genuine grade-seven ghost cancellation

In reflected units put \(P_n(Y)=(1-Y)L_n'(1-Y)\). Write \(\mathbf U=\mathbf G\) in the ten-site chart and \(\mathbf U=\mathbf H\) in the nine-site chart, and put \(j=2\) or 1 respectively. Use
\[
 \mathbf Z_0=N(Y^j\mathbf U),\qquad
 \mathbf Z_1=N(Y^{j+1}\mathbf U),\qquad
 \mathbf E_7=N\mathbf W(Y^6)-\mathbf W(Y^7)/7.
\]
Here \(N=A^{\mathsf T}\), \(Y\) acts componentwise by the reflected clock, and \(\mathbf W(F)=\mathbf b\odot F(\mathbf y)\). The first two words have grades six and seven and \(\mathbf E_7\) has grade seven. All three are zero at the literal terminal by its reverse-first chronology and \(Y=0\). This does not assert that a separate nonterminal numerical-zero receiver is zero.

Define two scalar functionals
\[
 \mathfrak U_k(F)=\sum_{s\ \mathrm{nonterminal\ labels}}
             U_{\rm agg}(s)s^kF(s),\qquad
 \mathfrak W_6(F)=\sum_{s\ \mathrm{all\ labels}} B_s s^6 F(s).
\]
The true aggregate \(\mathbf U\) is barycentric, with \(U_{\rm agg}(s)=\rho/D_{\rm live}'(s)\). The ordinary ghost tap \(\ell_g[(\mu+\nu c_g)P_6+\alpha P_5+\gamma P_7]\) in physical units gives the \(g\)-coordinate of each transpose output: replace \(P_n\) in this formula by \(\mathfrak U_j(P_n),\mathfrak U_{j+1}(P_n)\), or \(\mathfrak W_6(P_n)\), respectively. Barycentric degree annihilation gives
\[
 \mathfrak U_j(P_5)=\mathfrak U_{j+1}(P_5)=\mathfrak U_j(P_6)=0,\quad
 \mathfrak U_{j+1}(P_6)=5544\rho,\quad
 \mathfrak U_j(P_7)=-24024\rho .
\]
These follow by the actual distinct nonterminal hull and leading coefficients, not positivity of weights.

With real \(\gamma,\nu,\rho\ne0\), use the cancellation coefficients
\[
   q_6=\frac{\mathfrak W_6(P_6)}{5544\rho},\qquad
   \beta=
   \frac{(\alpha/\gamma)\mathfrak W_6(P_5)+\mathfrak W_6(P_7)
          -q_6\mathfrak U_{j+1}(P_7)}{-24024\rho}.
\]
Thus \(\mathbf V=\mathbf E_7-q_6\mathbf Z_1-\beta\mathbf Z_0\) is a genuine **ghost-zero** grade-seven state. The unknown \(\mu,\nu\) cancel with the common \(P_6\) mode; no specific live weight split enters \(\rho\) or these sums. The scalar ordinary moments inside \(\mathfrak W_6\) have degrees as high as 13 and are computed as actual quadrature quantities, not set equal to their integrals. This retains both unpaid next discrepancies. \(\alpha/\gamma\) is the actual forward coefficient ratio from the first three ordinary clocks.

## Exact live degree and receiver cutoff

By the paid \(7+4=11\) pairing, \(\mathbf V\) is orthogonal to all degree-at-most-four scalar inputs. On ten nonterminal live physical rows that gives a kernel of dimension five, because at least nine distinct labels make the five scalar tests independent. At ten sites the actual five independent vectors \(\mathbf G P_4(Y)\) in that kernel span it. At nine sites they are the pair line \(\mathbf G\) and \(\mathbf H P_3(Y)\), where the first \(d\)-row has \(H=0\). The claimed independence follows from distinct labels and the nonzero aggregate barycentric entries, including the signed early \(d\)-pair. This characterizes only the live kernel, not the full reverse grade-seven flag.

At ten sites the divided difference of \(\mathbf V/\mathbf G\) on the six labels \(d,v,0,u,w,E\) must vanish. The internal zero row is read using its actual normalized amplitude cancellation; no zero weight is assigned. At nine sites the genuine \(\mathbf G\) component of \(\mathbf V\) is \((15/7)d^4\mathbf G\), as read at the literal first \(d\)-row whose actual diagonal is \(d/2\). Subtract it and take the fourth divided difference on \(d_2,v,u,w,E\) using \(\mathbf H\) ratios. At \(d_2\), the normalized scalar error after this subtraction is
\[
       \left[(r^5-1)/(r-1)-15/7\right]/k
\]
by the same \(\Delta\) cancellation as the grade-six crossing; its new high lift has normalized ratio \(\psi(1)+(r+1)h_v/(rk)\). Earlier nonzero and internal-zero ratios use actual available positive-degree taps, and at \(E\) use the forced-zero diagonal four-source solve. In normalized \(Y/d\) units divide the coefficient of the lower lift by \(d\); the high lift and \(\mathbf E_7\) have the same scaling.

    python3 -B grade7.py

This runs the exact barycentric constants, coefficient-ratio path, and grade-seven arithmetic in two rational negative controls. A nonzero residual rejects a candidate; a zero does not establish a tableau. The new gates also vanish in sampled degree-36 midpoint residue fibres, which is not a real existence result or exhaustion in that sector. No native rooted theorem is claimed for this grade-seven extension.
