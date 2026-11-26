# A single live explicit origin saves stages in a dense derivative decoder

## Statement and scope

Fix an integer \(q\ge1\) and a prescribed real \(\gamma\ne0\). There is a lower-triangular tableau with exactly one diagonal zero, at its first stage \(o\), and all other diagonal entries equal to \(\gamma\), together with a fixed linear readout
\[
 B:K^s\longrightarrow K[X]_{<q},
 \qquad B\Phi_t=g_t\quad (|t|\le q),
 \qquad s=1+\left\lfloor q^2/4\right\rfloor.
\]
Here \(K=\mathbb R\) is allowed. If \(\gamma\) is real algebraic, \(K\) can be a finite real algebraic extension of \(\mathbb Q(\gamma)\). For \(q\ge2\), the first row is the unique zero-clock row and is a strict ancestor of a nonorigin stage with a nonzero readout coefficient. It is also a strict ancestor of a nonorigin active weight when the readout is integrated to an ordinary step. For \(q=1\) the tableau consists only of the correctly read explicit origin; if a genuinely used origin with a nonorigin successor is required, assume \(q\ge2\).

The convention is \(\Phi_\bullet=\mathbf1\), \(\Phi_{[u_1,\ldots,u_a]}=\bigodot_j A\Phi_{u_j}\), with the tree grade \(|t|\) counting every vertex. Put \(\mathcal I X^d=X^{d+1}/(d+1)\), \(g_\bullet=1\), \(g_{[u_1,\ldots,u_a]}=\prod_j\mathcal I g_{u_j}\), and \(T=\mathcal I-\gamma\). In particular, \(g_t\) is proportional to \(X^{|t|-1}\), and \(\Phi_{[\bullet]}=A\mathbf1=c\). A coefficient of \(B\) is a polynomial in the readout variable: the same readout is used for every tree. The result concerns dense derivatives; in characteristic zero integration from zero gives dense step coefficients, and evaluation at 1 gives an ordinary order-at-least-\(q\) endpoint rule. No stability or ordinary fixed-output minimum is asserted.

The argument adapts the nonzero-diagonal polynomial chart and paid-band reconstruction of the published DENSE-POLYNOMIAL-DONOR-MINIMUM.md (commit 3cca81b…). Its change is to install and keep one actual explicit-origin stage, shifting the mode basis on the invariant ideal \(XK[X]\). The lower bound in the zero-diagonal class, if used to conclude sharpness, is a separate result and is not derived here.

## Anchored shifted modes

Set \(W_0=1\) and
\[
 W_k=k!T^{\,k-1}X
     =\sum_{a=0}^{k-1}\binom{k-1}{a}(-\gamma)^{k-1-a}
                   \frac{k!}{(a+1)!}X^{a+1}\qquad(k\ge1).
\]
These are monic, \(W_1=X\), and the modes \(W_j\) for \(j\ge1\) span the polynomials with zero constant term. For \(j\ge1\),
\[
 TW_j=W_{j+1}/(j+1),\qquad
 XW_j=W_{j+1}+2\gamma j W_j+\gamma^2j(j-1)W_{j-1}.
 \tag{1}
\]
The last term is absent for \(j=1\). For a quick derivation, \([X,T]=\mathcal I^2\) on monomials and \(\mathcal I^2\) commutes with \(T\). With \(n=j-1\), use \([X,T^n]=nT^{n-1}\mathcal I^2\) (absent when \(n=0\)), \(X^2=2\mathcal I X\), and \(\mathcal I=T+\gamma\). Then
\[
 XT^nX=\big((n+2)T^{n+1}+2\gamma(n+1)T^n+
                    \gamma^2 nT^{n-1}\big)X.
\]
After multiplication by \(j!\) this is (1). In particular, multiplying any anchored mode band by a polynomial of degree \(d\) lowers its first possible index by at most \(d\) and never introduces index zero.

For the real existence assertion, with \(n=k-1\) one has
\[
 W_k(\gamma U)=\gamma^k(-1)^n n!\,U L_n^{(1)}(U),\qquad
 L_n^{(1)}(U)=\sum_{a=0}^n(-1)^a\binom{n+1}{a+1}U^a/a!.
 \tag{2}
\]
The coefficient equality follows from \(\binom{n+1}{a+1}=(n+1)\binom n a/(a+1)\). By differentiating the product, this \(L_n^{(1)}\) equals \(e^U U^{-1}(d/dU)^n(e^{-U}U^{n+1})/n!\). Integrating by parts \(n\) times therefore makes it orthogonal to all polynomials of degree below \(n\) for weight \(Ue^{-U}\) on \((0,\infty)\); every boundary term is zero at both ends. If there were fewer than \(n\) sign-changing zeros in \((0,\infty)\), multiplying by the product of the corresponding linear factors would give a nonzero constant-sign integrand, contradicting orthogonality. Thus \(L_n^{(1)}\) has exactly \(n\) distinct positive roots and \(L_n^{(1)}(0)=n+1\). Each \(W_k\) consequently has its simple root zero and \(k-1\) distinct nonzero roots, scaled by \(\gamma\). Their algebraicity follows from the explicit coefficients in (2).

## Exact auxiliary chart and its paid band

The starting chart is the constant polynomial \(F_1(t)=g_t(0)\), supplied by the single actual zero row \(o\). For \(2\le k\le q\), define auxiliary profiles of degree \(<k\) by
\[
 F_k([u_1,\ldots,u_a])
 =\operatorname{rem}_{W_k}
   \prod_j\big(TF_{k-1}(u_j)+\gamma F_k(u_j)\big).
 \tag{3}
\]
This is a structural recursion in the tree at a fixed layer, after defining the preceding layer. The empty product is 1. The degree of every profile is at most \(|t|-1\): before taking the remainder every child factor has degree at most its child grade, and taking a monic remainder cannot raise degree.

For every paid tree the error band is
\[
 g_t-F_k(t)\ \in\
 \operatorname{span}\{W_j:\ \max(1,2k+1-|t|)\le j\le |t|-1\}.
 \tag{4}
\]
An empty interval means zero. For \(k=1\), the leaf error is zero, and for \(|t|\ge2\) the difference has zero constant term and degree at most \(|t|-1\), as needed. For \(k\ge2\) use induction on \(k\), then on tree grade. For a child \(u\) the exact factor minus its factor in (3) is
\[
 \mathcal I g_u-(TF_{k-1}(u)+\gamma F_k(u))
 =T(g_u-F_{k-1}(u))+\gamma(g_u-F_k(u)).
\]
By (1) and the induction hypotheses, its first possible anchored mode is at least \(\max(1,2k-|u|)\). In a telescoping difference of the two products, the remaining factors have combined degree at most \(|t|-1-|u|\). Multiplication therefore gives first index at least \(\max(1,2k+1-|t|)\). The correction from taking the remainder is a multiple of \(W_k\) with quotient of degree at most \(|t|-1-k\), if it is nonzero. Its first possible index is also at least \(\max(1,2k+1-|t|)\), again by (1). The upper end follows from the degree bound. This proves (4).

In particular \(F_k(t)(0)=g_t(0)\) at every layer. In (3) the equation at zero also follows directly: each child factor evaluates to \(-\gamma F_{k-1}(u)(0)+\gamma F_k(u)(0)=0\). Thus zero is a permanent exact anchor supplied by the same physical explicit row, not a newly staged implicit fixed point or an additional stage per layer.

## Actual rows, reconstruction, and arithmetic

For layer \(k\ge2\), put
\[
 \ell_k=\max(1,2k-1-q),\qquad
 h_k=k-\ell_k=\min(k-1,q+1-k).
\]
By (4) the coefficients of \(W_j\) for \(0\le j<\ell_k\) in the preceding and current charts agree for every paid tree: both agree there with \(g_t\). Cache these coefficients from the preceding chart. The mode \(W_0\) thus always comes directly from the first physical stage.

Choose \(h_k\) distinct nonzero roots \(\xi\) of \(W_k\) and build one actual row per selected root. Let \(R_{k-1}\) be the already constructed fixed linear reconstruction from all physical stages in the preceding layers. The strict row at \(\xi\) has linear action on such data \(v\) given by \((T R_{k-1}v)(\xi)\); put \(\gamma\) on its diagonal and no other entries within its layer. Start with \(R_1\) taking the value at the origin and returning the constant of that value. A row may use earlier layers through the cache; there is no adjacency assumption on the physical strict support.

Define \(R_k\) by copying the cached low coefficients and solving for indices \(\ell_k,\ldots,k-1\) using the new stage data as evaluations at the chosen roots, after subtracting the cached polynomial. This evaluation matrix is invertible. Indeed \(W_{k-1}(\xi)\ne0\) at any nonzero root of \(W_k\): a common nonzero root would propagate down (1) to \(W_1(\xi)=\xi=0\). For \(a=0,\ldots,h_k-1\), the ratios \(W_{k-1-a}(\xi)/W_{k-1}(\xi)\) are the values of polynomials of degree exactly \(a\). This follows by running (1) backward from \(W_k(\xi)=0\) and ratio \(W_{k-1}(\xi)/W_{k-1}(\xi)=1\), dividing at each step by \(\gamma^2j(j-1)\) with \(j\ge2\). The leading term of each next polynomial comes from multiplying the current one by \(X\) and dividing by that nonzero scalar. Thus after row scaling and reversing columns the evaluation matrix is the matrix of a degree-ordered polynomial basis at \(h_k\) distinct nodes, which is a nonsingular Vandermonde change of basis. In particular \(R_k\) is a fixed linear map on arbitrary stage data, not a function of the input tree.

Induct on layers and tree grade. The strict application on a child agrees with \(TF_{k-1}\) by the preceding reconstruction, and the self contribution agrees with \(\gamma F_k\) at the node by the smaller-tree induction. Therefore the physical stage jets in each new row are the evaluations of (3); taking a remainder does not change their values there. The copied low coefficients and unique high solve identify \(R_k\Phi_t=F_k(t)\) for all paid trees. At \(k=q\), (4) implies \(F_q(t)=g_t\) for \(|t|\le q\). The promised polynomial-valued readout is \(B=R_q\).

All operations in this construction use only \(\gamma\), the selected roots, and inverses of nonzero field elements. More abstractly it suffices that the field have the units \(1,\ldots,q\), \(\gamma\ne0\), and the prescribed number of distinct nonzero roots of every needed \(W_k\); no ordering is used in (1), (3), (4), or in actual reconstruction. The real argument (2) supplies these roots simultaneously, including when \(\gamma<0\). For real algebraic \(\gamma\) only a finite extension is needed, with no assertion of an optimal field degree. The grade and coefficient calculations never use a formal integration denominator above \(q\) (the profiles alone need only up to \(q-1\)); if a finite-characteristic version is used, the characteristic-zero dense-step conclusion has to be interpreted with its own integration units.

## Literal clocks, liveness, and savings

The first physical row is zero, has clock zero, and gives the exact anchored leaf and nonleaf values. At a new row the row sum is \((T1)(\xi)+\gamma=\xi\), since reconstruction sends the all-ones leaf data to 1. In particular no other clock is zero. Layer 2 has its single selected nonzero root \(2\gamma\) and strict coefficient \(\gamma\) to the origin. At every layer \(k\ge3\), the size-three tall tree is exactly \(X^2/2\) in (4), so \((Ac)_i=c_i^2/2\) for each such physical stage. A row with no strict donor would have \(c_i=\gamma\), \((Ac)_i=\gamma^2\), an impossibility. Every nonorigin stage thus has a strict incoming edge, and following such edges backward must reach the single origin. For \(q\ge2\), \(B(c)=X\) forces some nonorigin coordinate to have nonzero polynomial coefficient in \(B\). More strongly, \(B(v)(0)=v_o\) on arbitrary physical data, by the permanent constant mode. Upon integrating at endpoint 1, the ordinary output satisfies \(b^Tc=1/2\), so some nonorigin weight is active there too. Hence the reused explicit origin has a literal strict path to active output, not merely an unused leading zero.

Writing \(n=k-1\), the stage count is
\[
 1+\sum_{n=1}^{q-1}\min(n,q-n)=1+\lfloor q^2/4\rfloor.
\]
It is \(r^2+1\) at \(q=2r\), and \(r(r+1)+1\) at \(q=2r+1\). Relative to the sharp nonsingular dense minimum \(\lfloor(q+1)^2/4\rfloor\), the saving is \(\lfloor(q-1)/2\rfloor\), positive from grade 3, and at grade 20 this gives 101 instead of 110. The source of the saving is the missing constant mode at each full physical bank: it is supplied by a single reusable, exact, physical origin.

## Separate rational upper; no rational sharpness claim

The sharp-size construction needs algebraic roots as stated: for example the nonzero roots of \(W_3\) are \(\gamma(3\pm\sqrt3)\), so those selected clocks are not rational when \(\gamma\) is rational and \(q\ge3\). This is a limitation of this chart, not a rational lower bound.

For comparison a direct rational dense decoder exists for every prescribed \(\gamma\in\mathbb Q^\times\). Grade 2 uses the origin and trapezoid at \(2\gamma\). For grade 3 and higher first create a second nonzero rational clock \(x\ne2\gamma\) with row coefficient \(a=x(x-2\gamma)/(4\gamma)\) to the trapezoid, \(x-\gamma-a\) to the origin, and diagonal \(\gamma\). Its row sum is \(x\) and \((Ac)_i=x^2/2\), so these three distinct clocks all have exact jets through grade 3. For each \(k=4,\ldots,q\), use the origin plus the preceding \(k-2\) nonzero exact-grade-\((k-1)\) nodes as \(k-1\) interpolation points. For each of \(k-1\) new distinct nonzero rational clocks choose the strict row by evaluating \(T\) of that donor interpolation at the new clock, with diagonal \(\gamma\). For children of grade at most \(k-1\) the donor chart is the exact profile by interpolation. Self recursion on the child grade then gives exact jets through grade \(k\) at every new node. Finally interpolate the exact jets at the origin and the last \(q-1\) nodes to get a polynomial readout of degree \(<q\). All nonorigin rows again have a strict donor and the origin is live. For \(q\ge3\) this gives \(q(q-1)/2\) rational stages; the \(q=2\) case has two. This is a simple comparison, not a claim that this upper is best over \(\mathbb Q\).
