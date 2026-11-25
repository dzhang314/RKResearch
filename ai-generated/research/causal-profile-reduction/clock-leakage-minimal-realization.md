# Clock leakage in a minimal Runge–Kutta realization

The full rooted scalar series determines the grouped clock interactions, including those at clocks with zero aggregate output. Consequently a nonzero mixed clock correction cannot be removed by replacing a tableau with an equivalent minimum realization. At finite order, a rank certificate can still turn the correction into a bound on repeated physical clocks. This note gives the certificate and a family showing why minimality does not replace it.

Work over a characteristic-zero field. Write \(c=A\mathbf1\) and use the actual [rooted-tree columns and order predicate](../../../RKResearch/OrderConditions.lean). Define
\[
B_t=\sum_{c_i=t} b_i,\qquad
M_{uv}=\sum_{c_i=u,\,c_j=v} b_i A_{ij},\qquad
D_{uv}=M_{uv}+M_{vu}-B_u B_v .
\]
For a finite set \(T\) of \(n\ge2\) distinct labels let \(q_t=\prod_{u\in T\setminus\{t\}}(X-u)\), \(k_t=q_t(t)\), \(r_t=k_t\mathbf1_{c=t}\), and \(h_t=q_t(c)-r_t\). The last vector is the reviewed [off-cover mask](../../lean/RKCert/ReviewedNative/HiddenClockLeakage.lean), whether or not \(T\) covers all aggregate output. Use the reviewed [symmetric bilinear form](../../lean/RKCert/ReviewedNative/NativeSymplecticPairing.lean)
\[
\mathcal B(f,g)=b^{\mathsf T}(f\odot Ag)+b^{\mathsf T}(g\odot Af)
                 -(b^{\mathsf T}f)(b^{\mathsf T}g).
\]
Bilinearity gives \(K=\widetilde D+L\), where
\[
K_{uv}=\mathcal B(q_u(c),q_v(c)),\qquad
\widetilde D_{uv}=k_u k_v D_{uv},\qquad
L_{uv}=\mathcal B(r_u,h_v)+\mathcal B(h_u,r_v)+\mathcal B(h_u,h_v).
\]

## What the observations recover

Suppose two finite tableaux have identical full rooted scalar series. Choose a polynomial cardinal selector \(\ell_u\) on the **union** of their actual clock sets. Then \(B_u=b^{\mathsf T}\ell_u(c)\) and \(M_{uv}=b^{\mathsf T}(\ell_u(c)\odot A\ell_v(c))\). By `Φ_bushyTree` and the reviewed graft recursion these are linear combinations of scalar tree outputs, using the same coefficients for both tableaux. Thus \(B\) and \(M\) agree, extending by zero on absent clock labels. For fixed \(T\), \(K\) is also determined by the series, so \(L=K-\widetilde D\) is identical. This recovers grouped weighted interaction, not individual entries of \(A\). With finite data the cardinal selectors on the union may cost more than the visible order budget.

There is a positive erasure criterion. Let \(\mathcal R\) be the span of all actual tree-stage columns. This is a coordinatewise algebra by `Φ_rootedSum` and is \(A\)-invariant by grafting at the leaf. Let \(\mathcal N\subseteq\mathcal R\) consist of columns killed by every full rooted context, including immediate output. Closure of contexts under grafting and multiplication by tree columns gives \(A\mathcal N\subseteq\mathcal N\), \(\mathcal R\odot\mathcal N\subseteq\mathcal N\), and \(b^{\mathsf T}\mathcal N=0\). Substitution in \(\mathcal B\) gives \(\mathcal N\subseteq\operatorname{rad}(\mathcal B|_{\mathcal R})\) term by term. The masks \(r_t,h_t\) are polynomial functions of the finite clock vector, so if the hidden masks lie in \(\mathcal N\) the correction vanishes before and after quotienting. This argument does not require a characterization or uniqueness theorem for the minimum profile quotient.

For finite actual observations, let \(Z\) contain the literal columns \(r_t,h_t\) in the stated observation domain and \(O\) be the observation stack. Write \(G=Z^{\mathsf T}\mathcal BZ\). The pairing descends to the observed image of these columns exactly when
\[
\ker(OZ)\subseteq\ker G
\quad\Longleftrightarrow\quad
\operatorname{rank}\begin{pmatrix}OZ\\G\end{pmatrix}
 =\operatorname{rank}(OZ).
\]
The rank condition says every row of \(G\) is a linear combination of actual observation rows. Under this condition \(Oh_t=0\) erases the corresponding hidden contributions. For a contrast packet, apply the same test just to its combined stopped and hidden masks. Neither zero aggregate weight nor the degree of the **uncut** selector proves this hypothesis on the hidden mask.

## Affine payment and repeated clocks

By [clock evaluation in the graded tree space](../../lean/RKCert/ReviewedNative/GradedPrimitives.lean) and `symplecticPair_zero_on_paid_tree_spaces`,
\(\mathcal B(F(c),G(c))=0\) when \(\deg F+\deg G+2\le p\). At \(p\ge2n-2\), the only possibly unpaid monomial pairings of two \(q\)'s have bidegrees \((n-1,n-1),(n-1,n-2),(n-2,n-1)\). The coefficients of \(X^{n-1}\) and \(X^{n-2}\) in \(q_t\) are \(1\) and \(t-\sum_{u\in T}u\). Hence
\[
 K_{uv}=\alpha+\beta\left(u+v-2\sum_{t\in T}t\right),\qquad
 \beta=\mathcal B(c^{n-2},c^{n-1}),\quad
 \alpha=\mathcal B(c^{n-1},c^{n-1}).
\]
In particular \(P^{\mathsf T}KP=0\) for any zero-sum contrast columns \(P\). Directly, each difference \(q_a-q_z\) is of degree at most \(n-2\), so two such differences pay the same budget.

For lower-triangular \(A\), put \(d_t=\sum_{c_i=t} b_iA_{ii}\) and \(E_t=M_{tt}-d_t\), the net weighted strict same-clock entry sum. Nonzero \(E_t\) forces an actual same-clock pair \(i<j\) with \(b_j A_{ji}\ne0\). Set \(b^0_t=k_t^2(2d_t-B_t^2)\) and \(\delta_t=2k_t^2E_t\). Let \(D^0\) retain the actual off-diagonals of \(\widetilde D\) and have diagonal \(b^0\). With \(C=D^0+L\), the paid contrast identities give
\[
\delta_a+\delta_z=2C_{az}-C_{aa}-C_{zz},\qquad
\delta_a=C_{az}+C_{av}-C_{zv}-C_{aa}\quad(a,z,v\ \text{distinct}).
\]
The second uses two contrasts sharing only the designated label \(a\).

For a rank test on \(m\ge3\) selected labels, let \(H\) be a symmetric reference completion of the **actual scaled off-diagonals** on those labels and \(P\) a basis matrix of their zero-sum hyperplane. Put \(g_t=b^0_t+\delta_t-H_{tt}\) and \(r=\operatorname{rank}(P^{\mathsf T}(H+L)P)\) on this set. The affine identity gives \(r=\operatorname{rank}(P^{\mathsf T}\operatorname{diag}(g)P)\). If one \(g_a=0\), use \(e_i-e_a\) as basis to read this rank as the number of nonzero \(g_i\). If all \(g_i\ne0\), a radical vector must have coordinates \(\lambda/g_i\), since the product by \(\operatorname{diag}(g)\) lies in the span of \(\mathbf1\). The radical has dimension at most one, so \(r\ge m-2\).

Therefore **if \(r\le m-3\), at least \(\#\{t:b^0_t\ne H_{tt}\}-r\) fibres have nonzero strict weighted edges** (clip at zero). Indeed each reference gap with \(g_t=0\) forces nonzero \(\delta_t\). For ERK the baseline is \(-(k_tB_t)^2\); for common diagonal \(\gamma\) it is \(k_t^2B_t(2\gamma-B_t)\). For arbitrary DIRK the literal weighted diagonal is part of the premise. This is a conditional stage count on occupied labels, not an unrestricted lower bound.

## Minimum realizations with unavoidable leakage

Use \(n\ge3\) positive quadrature sites in \((0,1)\) over the real algebraic field. We realize their weights on \(n\) singleton live fibres of a strict explicit tableau. The [pure donor construction](../quadrature-donor-realization/realization.md#1-the-donor-step-on-the-actual-tree-columns) can reserve a nonzero coefficient from the immediately preceding stage: when appending a row of purity grade \(g\), subtract that pure predecessor's monomial contribution from the \(g-1\) right-hand sides and solve on \(g-1\) other distinct pure donors of grade at least \(g-1\). This preserves the literal child primitive and hence all tree profiles through grade \(g\). Start with leaf-pure clocks \(0,z\) and \(A_{21}=z\ne0\). Use \(g+1\) rows in each hidden grade-\(g\) bank so that the next interpolation has enough donors even after reserving the predecessor. Use fresh distinct hidden clocks. Between consecutive active rows insert a pure hidden connector one grade lower, receiving the reserved edge from the preceding active row. Each weighted row then reads only hidden stages, so \(M_{T,T}=0\), while every adjacent strict coefficient is nonzero and the last row carries nonzero weight.

This is minimal for its **complete rooted scalar series**, independently of profile quotient uniqueness. The reviewed [Volterra operator](../../lean/RKCert/ReviewedNative/NonsingularDIRKStageFloor.lean) has matrix \(V=\operatorname{diag}(c)A-A\operatorname{diag}(c)-A^2\). Here it is strictly lower triangular with each \(V_{i,i-1}=(c_i-c_{i-1})A_{i,i-1}\ne0\). For \(s\) stages, the \(s\) vectors \(V^j\mathbf1\) have successive first nonzero coordinates, and the \(s\) covectors \(b^{\mathsf T}V^j\) have successive last nonzero coordinates. Their scalar Hankel matrix \((b^{\mathsf T}V^{i+j}\mathbf1)_{0\le i,j<s}\) therefore has rank \(s\). Its entries are combinations of full rooted outputs, since \(A\) grafts at a leaf and multiplication by \(c\) adds a leaf at the root. Any equivalent tableau has the same Hankel and at least \(s\) stages. This argument uses full outputs, not a finite paid observability claim.

With [Gaussian sites and weights](hidden-clock-moment-ladder.md#4-sharpness-on-actual-erk-and-positive-common-diagonal-sdirk), give the active rows purity grade \(2n\). The actual order is \(2n\) and \(K=0\). Since \(\widetilde D=-ww^{\mathsf T}\) for \(w_t=k_t B_t\), the nonzero leakage \(L=ww^{\mathsf T}\) has rank one, even though all live fibres are singleton.

The affine threshold itself admits a nonconstant example. For monic uniform orthogonal polynomials \(\pi_j\), take the nodes of \(P_\epsilon=\pi_n+\epsilon\pi_{n-2}\) for sufficiently small nonzero rational \(\epsilon\), with Lagrange integral weights. Disjoint sign brackets around the simple Gaussian roots survive for small \(\epsilon\), and the weights are continuous in the distinct nodes, so they stay positive. Dividing a polynomial of degree at most \(2n-3\) by \(P_\epsilon\) leaves a quotient of degree at most \(n-3\), orthogonal to both summands. The monic \(P_\epsilon\pi_{n-2}\) has zero quadrature and nonzero integral \(\epsilon\int_0^1\pi_{n-2}^2\), so the first unpaid moment fails. Use active purity grade \(p=2n-2\). This makes the tree order exact and still integrates the two leading monomial actions in \(\beta\), since \(n-1\le p-2\). Writing \(\mu_j=\sum_t B_t t^j\) gives
\[
\beta=\frac{2n-1}{n(n-1)}
\left(\mu_{2n-2}-\frac{1}{2n-1}\right)\ne0 .
\]
Here \(K\) has rank two and \(L=K+ww^{\mathsf T}\) has rank three: \(w_t=\int_0^1 q_t\) is monic of degree \(n-1\) in \(t\) by synthetic division, so \(w\) is independent of \(1,t\) on the \(n\) nodes. This gives genuine affine payment, low-rank leakage, and no repeated live fibre in a minimum realization. By full-series invariance the correction cannot be made zero by changing the realization.

The affine, rank, and realization statements here are mathematical proofs. The linked Lean sources supply the reviewed tableau definitions and paid pairing, not a kernel check of these conclusions.
