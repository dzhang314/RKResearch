# The rational DIRK order-ten minimum is twelve stages

The [literal tableau](tableau.json) is an ordinary, unequal-diagonal DIRK with **12 distinct stages and exact order ten over the rationals**. Together with the [rational lower bound](../causal-profile-reduction/dirk-order10-rational-lower-twelve.md), this proves the rational minimum is **12**. The real-algebraic minimum remains 11. The lower proof is mathematical, with separate Lean receipts for key steps.

The same literal upper witness applies to all characteristic-zero fields, and to every **nonzero commutative unital ring** where
\[
 D=101588047290852467338246934187117072000
\]
is invertible. The stage and weight denominators divide \(D\). The eleventh bush has raw defect \(1/27371520\), so its factorial-scaled defect is \(1/2488320\), with \(2488320\mid D^2\). This is an exact localization upper bound, not a universal factorial-only ring bound or a minimum in every specialization.

## Seven opening rows with a rank-one correction

Set
\[
 (c_1,\ldots,c_7)=(0,1/7,1/24,u,p,q,r),\qquad
 (u,p,q,r)=(1/12,1499/3106,3/4,1/4).
\]
The first row is zero. Rows 2 through 5 use anchored interpolatory quadrature on physical slots \((1,2),(1,2,3),(1,3,4),(1,3,4,5)\) respectively, including the row being constructed. Row 4 is Simpson since \(c_3=u/2\). Let \(\Pi\) be interpolation in \(P_4\) on slots \(1,4,5,6,7\), and let \(Jf(X)=\int_0^Xf(z)\,dz\). Put
\[
  H(X)=X(1-14X+56X^2-84X^3+42X^4),\qquad
  \sigma=(A_{4,\bullet}-J_u\Pi)/H(u),
  \qquad J_v f=(Jf)(v).
\]
For the remaining opening rows take the actual rows
\[
      A_{6,\bullet}=J_q\Pi+H(q)\sigma,\qquad
      A_{7,\bullet}=J_r\Pi+H(r)\sigma .
\]
The only potentially noncausal coefficient is \(A_{6,7}\). Its numerator is the equation
\[
 H(u)J_q[X(X-u)(X-p)(X-q)]-
 H(q)J_u[X(X-u)(X-p)(X-q)]=0,
\]
which is linear in \(p\) and gives the displayed \(1499/3106\). The coefficient is literally zero.

The opening row conditions imply that every decoder slot is locally exact through size five, and \(\sigma\) annihilates every actual opening derivative vector through size four. In the replay both assertions are tested against those tree families; some size-five input is detected by \(\sigma\). This is a genuinely nonzero correction, not a third pure size-six port.

For a tree \(t\) of size \(n\) define the scalar derivative \(f_t(X)=nX^{n-1}/t!\) and residual \(\rho_t=f_t-\Pi\boldsymbol{\Phi}_t(A_{\rm old})\). The actual size-six residual space \(F_5\) has dimension three. It consists of the polynomials in \(P_5\) vanishing at zero whose values at \(u,q,r\) are proportional to \((H(u),H(q),H(r))\). Indeed the only nontrivial port error at size six is the primitive of a size-five source, and the three literal port rows add the common \(\sigma\) with the indicated factors. The replay checks the rank and port relation exactly. In particular, **\(H\in F_5\)**.

## Reverse payment and the third actual merge

The nine scalar sites are symmetric about \(1/2\), with centered coordinates \(0,\pm1/3,\pm5/6,\pm1/2,\pm1\). Their interpolatory quadrature has degree nine. Assign the zero-site weight to the old origin. The other clocks in reverse order are
\[
 \mathbf x=(1,2/3,1/3,11/12,1/2,r,q,u),\qquad
 \mathbf y=\mathbf1-\mathbf x .
\]
Write \(\mathbf w\) for their weights. As in the [two-port construction](../dirk10-thirteen-rational-two-ports/README.md), choose the reflected normalized weighted transpose \(L\) from
\[
    L\mathbf1=\mathbf y,\qquad
    L\mathbf y=\mathbf y^2/2,\qquad
    L\mathbf y^2=\mathbf y^3/3+\mathbf g .
\]
At one \(g_i=0\). At each proper site \(g_i=\tau/(w_i x_i P_7'(x_i))\), where \(P_7\) is the proper-site hull and \(\tau\) is fixed by the second row. The actual vector \(\mathbf g\) kills every positive power of \(\mathbf x\) through degree six. This pays all size-six and size-seven source residuals and the primitives of the size-six residuals. The two other tests, for \(\mathbf h=L\mathbf y^3-\mathbf y^4/4\) and \(\mathbf k=L\mathbf g\), are
\[
    \langle\mathbf h,E F_5\rangle_{\mathbf w}=0,\qquad
    \langle\mathbf k,E F_5\rangle_{\mathbf w}=0 .
\]
The 6-by-5 system and its augmentation both have rank five. The single joint compatibility uses the line of \(F_5\) which vanishes at \(1/2,u,q,r\), namely \(X(X-1/2)(X-u)(X-q)(X-r)\). It is precisely the last-four-site hull test from the two-port family, so the same rational mesh factor allows the solve. The replay independently checks both exact systems.

Let \(\boldsymbol\eta=E H\) on the proper sites, changing its value at physical \(1\) by \(-J_1 H/w_1\), with \(w_1\) the weight at physical one. The four weighted Jacobi tests for \(X(1-X)(H/X)\) yield
\(\langle\boldsymbol\eta,\mathbf x^j\rangle_{\mathbf w}=0\) for \(0\le j\le4\).
The cofactor moments also give orthogonality to \(\mathbf g,\mathbf y\odot\mathbf g\). The change at physical one is invisible to \(\mathbf h,\mathbf k\), whose first reflected values are zero. Since \(H\in F_5\), both these pairings with \(\boldsymbol\eta\) are zero. These are all deviations from ideal scalar words through length four. The implementation separately verifies annihilation for **every one of the 31 true word vectors** through length four, formed from the actual \(L\) and multiplication by \(\mathbf y\).

In the forward order, with suffix block \(T\) and evaluation \(E\), take the literal cross block
\[
                 (EJ-TE)\Pi+\boldsymbol\eta\,\sigma .
\]
Its primitive error is exactly the old projected error, the propagated suffix error, and the added term \(\boldsymbol\eta\,\sigma(\boldsymbol{\Phi}_t(A_{\rm old}))\). A projection error first enters at derivative grade six; a correction error first enters at grade five. Two errors cannot multiply through grade nine. For the old part, the [primal/dual gluing argument](../../lower-bounds/proof-dependencies/rk_first_overlap_primal_dual_gluing_20261123.md) requires words of length at most three and the moment tests already paid. For the added part every relevant word has length at most four and the stated genuine annihilation pays it.

The first suffix rows are at \(u,q,r\). They have no suffix taps, and their full padded rows agree entry-by-entry with old slots **4, 6, 7** respectively. The constructor verifies the three complete row identities \((4,8),(6,9),(7,10)\) before redirecting all uses and weights. The resulting physical width is \(7+8-3=12\); this is not an aggregate site count.

## Reproduce the exact proof data

The constructor and selection-factor check use SymPy. The independent literal checker uses only the Python standard library and all **1,205** unordered rooted shapes through order ten, plus a nonzero next-order test. It does not import the constructor, its projections, or its stage contractions.

    python3 -B audit_tableau.py
    python3 -B check_selection_gate.py
    python3 -B build12.py --emit /tmp/dirk-twelve-rebuilt.json
    cmp tableau.json /tmp/dirk-twelve-rebuilt.json
    sha256sum -c arithmetic-sha256.txt

The [end-to-end Lean upper certificate](../dirk10-twelve-native-upper/README.md) checks exact order, triangularity, and specialization over any nonzero commutative ring inverting the displayed denominator on Lean/Mathlib 4.36.0.
