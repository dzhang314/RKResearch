# Sharp stage minimum for an exact polynomial dense derivative decoder

## Convention and scope

Let \(K\) be a field, \(q\ge1\), and assume the casts of \(1,\ldots,q-1\) to \(K\) are nonzero. Let \(A\in K^{s\times s}\) be lower triangular with **each diagonal entry nonzero**; the entries need not be equal for the lower bound. Put \(c=A\mathbf1\) and \(M=\operatorname{diag}(c)\). For an unlabeled rooted tree, use the stage elementary weight convention
\[
 \Phi_\bullet=\mathbf1,\qquad
 \Phi_{[t_1,\ldots,t_a]}=\bigodot_{j=1}^a A\Phi_{t_j}.
\]
A stage derivative grade is the number of vertices, including the root. Write \(\mathcal I X^i=X^{i+1}/(i+1)\), only in the paid range. The exact derivative profile is
\[
 g_\bullet=1,\qquad g_{[t_1,\ldots,t_a]}=\prod_j\mathcal I g_{t_j}.
\]
Thus \(g_t\) is a scalar times \(X^{|t|-1}\). The consistent rooted-tree symmetry factors, if used in the derivative series, multiply both elementary weights and exact profiles. The statements here are identities of elementary weights and do not require those factors to be invertible. A **dense derivative decoder through grade \(q\)** is a fixed \(K\)-linear map \(D:K^s\to K[X]_{<q}\) such that \(D\Phi_t=g_t\) for every \(|t|\le q\). Equivalently its polynomial coefficients are linear combinations of the actual stage derivatives, the same combinations for every tree. It is not assumed that stages are individually exact, that clocks are distinct, that weights are positive, or that there is any special layer or depth. In characteristic zero, integrating the polynomial readout gives a dense *step* of order at least \(q\); the derivative and step conventions differ by this integration.

## Lower bound and finite-sample version

More generally let \(\lambda:K[X]_{<q}\to V\) be any linear target and suppose \(D_\lambda\Phi_t=\lambda(g_t)\) for all paid trees, with \(D_\lambda:K^s\to V\) linear. Then
\[
 s\ \ge\ \sum_{j\ge0:\ q-2j>0}\dim_K\lambda(K[X]_{<q-2j}). \tag{1}
\]
To prove this, attach a unary root for \(A\), and attach a new leaf to the current root for \(M\). Each raises the grade by one, with polynomial actions \(\mathcal I\) and \(X\). The matrix
\[
 \Pi=MA-AM-A^2
\]
is lower triangular with diagonal entries \(-A_{ii}^2\), hence invertible. Its polynomial action is zero because \(X\mathcal I-\mathcal I X=\mathcal I^2\), as seen on monomials. For each \(j\) choose polynomials \(P_{j,k}\) of degree less than \(q-2j\) whose images give a basis of \(\lambda(K[X]_{<q-2j})\). The vectors \(\Pi^j P_{j,k}(M)\mathbf1\) are independent: in a putative relation divide by the least power \(\Pi^j\) still present, then apply \(D_\lambda\). At that point each column is a linear combination of paid trees (start with the star \(M^i\mathbf1\), of grade \(i+1\)). Terms with a positive remaining power have zero polynomial image; the terms of least power map to the independent \(\lambda(P_{j,k})\). Thus their coefficients vanish, contradicting the least choice. This proves (1).

For the dense decoder take \(\lambda=\mathrm{id}\). The bound is
\[
 L(q):=\sum_{j\ge0}(q-2j)_+=\left\lfloor\frac{(q+1)^2}{4}\right\rfloor. \tag{2}
\]
For a decoder paying only \(k\) distinct anchors \(x_1,\ldots,x_k\in K\), take \(\lambda(P)=(P(x_a))_{a=1}^k\). Then \(\dim\lambda(K[X]_{<n})=\min(k,n)\): if \(n\le k\), polynomial interpolation is injective by the root bound; if \(k\le n\), cardinal polynomials of degree less than \(k\) give surjectivity. This proves (1) with the corresponding sum of \(\min(k,q-2j)\), irrespective of whether the anchor readouts are physical stage coordinates, signed combinations of those coordinates, or have arbitrary dependence across coordinates. Coincident anchors count only once. For dependent combinations of anchors, derivatives, or other linear functionals one must use the actual restriction ranks in (1), not the formal number of outputs. The sharpness assertion below is for the fully dense case, not arbitrary given finite anchoring data.

## Attainment with a common diagonal (and exact arithmetic scope)

Here assume characteristic zero, \(\gamma\ne0\) is the prescribed common diagonal, and each polynomial \(W_k=k!(\mathcal I-\gamma)^k1\), \(1\le k\le q\), is split with distinct roots in the working field. This holds over \(\mathbb R\) for every real \(\gamma\ne0\). If \(\gamma\) is real algebraic, the construction lies in \(\mathbb Q(\gamma,\text{selected roots})\subset\overline{\mathbb Q}\cap\mathbb R\); rationality of those roots is not assumed. To check the real-root assertion, \(W_k(\gamma U)=\gamma^k(-1)^k k! L_k(U)\), where \(L_k=e^U(d/dU)^k(e^{-U}U^k)/k!\). Integrating by parts shows this polynomial is orthogonal to degrees below \(k\) for \(e^{-U}dU\) on \((0,\infty)\); a degree-\(k\) real orthogonal polynomial must have \(k\) simple roots there (otherwise multiply by the product of its sign-changing roots to contradict orthogonality). Scaling by nonzero \(\gamma\) preserves distinctness.

Here are the actual construction and verification, also valid at a larger cap \(m\ge q\). Write \(T=\mathcal I-\gamma\). Temporarily define the full polynomial profile \(F_k(t)\) of degree less than \(k\) by \(F_0(t)=0\) and, for \(k\ge1\),
\[
 F_k([t_1,\ldots,t_a])=
 \operatorname{rem}_{W_k}\prod_j( T F_{k-1}(t_j)+\gamma F_k(t_j)). \tag{3}
\]
This is a structural recursion in the tree at each layer, with the empty product for the one-vertex tree. It prescribes the usual common-diagonal stage at each root of \(W_k\), with strict row obtained by evaluating \(T\) applied to the preceding chart. Every profile has degree at most \(|t|-1\).

For completeness, the paid band is
\[
 g_t-F_k(t)\in\operatorname{span}\{W_j:2k+1-|t|\le j\le |t|-1,\ j\ge0\}. \tag{4}
\]
Coefficient comparison in \(W_j=\sum_{a=0}^j\binom ja(-\gamma)^{j-a}(j!/a!)X^a\) gives
\[
 TW_j=W_{j+1}/(j+1),\qquad
 XW_j=W_{j+1}+\gamma(2j+1)W_j+\gamma^2j^2W_{j-1},
\]
where the last term is zero at \(j=0\). Thus multiplying by a polynomial of degree \(d\) lowers the first possible mode by at most \(d\). Prove (4) by induction on \(k\), then tree grade. The error for a child state in (3) is \(T(g_{t_j}-F_{k-1}(t_j))+\gamma(g_{t_j}-F_k(t_j))\) and has first possible mode \(2k-|t_j|\) or higher. Telescope the product against the exact product. Every other child factor has degree at most its tree grade, so each product error has first possible mode \(2k+1-|t|\) or higher. Taking the remainder adds a multiple of \(W_k\) of degree at most \(|t|-1\), which has the same band by the multiplication bound. The base \(k=0\) and the leaf follow directly. This proves (4), in particular exact dense through grade \(k\).

Only \(h_k=\min(k,m+1-k)\) of the \(k\) roots of \(W_k\) are needed physically at layer \(k\). Cache the first \(k-h_k=\max(0,2k-1-m)\) coefficients in the \(W_j\) basis from the preceding chart. By (4), they agree with those of the current full chart for every tree of grade at most \(m\). Evaluate the actual \(h_k\) A-rows by applying \(T\) to that preceding reconstructed chart, and add diagonal \(\gamma\) on each row. There are no within-layer edges. At a root \(\xi\) of \(W_k\), \(W_{k-1}(\xi)\ne0\) by the three-term recurrence and \(W_0=1\). Divide the high-mode evaluations by it: backward recursion gives \(W_{k-1-a}(\xi)/W_{k-1}(\xi)\) as the evaluation at \(\xi\) of a polynomial of exact degree \(a\). For \(0\le a<h_k\) this gives an invertible evaluation matrix at any \(h_k\) distinct selected roots. Reconstruct the high coefficients by that matrix after subtracting the cached low part. This is a fixed linear map on stage data. Induction on layers and on tree grades shows the selected rows give exactly (3) at their nodes and the reconstructed chart equals (3) up to the cap. All coefficients use only \(\gamma\) and selected roots. Clocks are indeed the selected roots: at layer 1 the sole clock is \(\gamma\), and subsequently \(T1+\gamma=X\).

Take \(m=q\). This realizes \(D\Phi_t=g_t\) through \(q\) with \(\sum_{k=1}^q\min(k,q+1-k)=L(q)\) actual rows. Thus (2) is sharp even if competitors may use varying nonzero diagonals and arbitrary depths. This is a minimum for the dense donor abstraction, **not** a minimum for ordinary fixed-output Runge–Kutta order \(q\) or for the full method using the donor.
