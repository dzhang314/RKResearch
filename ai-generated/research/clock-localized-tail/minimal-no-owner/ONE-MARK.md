# One root mark, exact graded order contacts, and the final projected primitive

Consider the direct strict SDIRK construction with a canonical minimum closed Laguerre block through order \(m-1\) and zero output weights on its stages. The late block has pairwise distinct abscissae, evaluation map \(E\) at those abscissae, and strictly lower matrix \(T\). If \(D_F\) denotes the early polynomial decoder, its strict feed from the early block is \(EJD_F-TED_F\). The target order is \(p=m+r\), with \(r\le m\). These conditions imply true local order through \(m\) at every late stage. Write \(J=I_0-\gamma I\), \(J^*=I_1-\gamma I\), and \(\ell=\int_0^1\), where \(I_0\) and \(I_1\) integrate from \(0\) to \(X\) and from \(X\) to \(1\), respectively. Assume the coefficients lie in a characteristic-zero field in which the indicated cache is defined and \(\gamma\ne0\). The positivity statement adds real hypotheses below. None of the conclusions is an unrestricted strict SDIRK bound.

## 1. Exact lowest coordinates through all numerical copy lifts

Set \(h=m-1\), and write \(W_j=j!J^j1\) for the monic Laguerre polynomials. Let \(\alpha\) be the one actual final early clock, a root of \(W_h\). In the standard canonical cache, at level \(k\) the actual decoder for order \(\le h\) copies the first \(c_k=\max(0,2k-1-h)\) Laguerre coordinates from the preceding decoder, then matches the selected true level-\(k\) node values. The full virtual chart \(\widehat F_k\) of degree \(<k\) has exact model error \(\ G-\widehat F_k\) involving Laguerre indices at least \(2k+1-n\) on a tree of order \(n\). These are the literal cache and band of the construction summarized in [Marked early-null profiles](MARKED-SOURCE.md). At \(n=h+1\), all proper children remain within the paid cap \(h\), so the actual stage values at this level are still genuine samples of \(\widehat F_k\) at that level's chosen nodes. This is needed for the error lift, not inferred from the formal band alone.

When \(c_k>0\), put \(j_k=c_k-1=2k-2-h\). Among the copied coordinates, \(\widehat F_k-\widehat F_{k-1}\) can have a nonzero new entry only at \(j_k\), by the two band bounds. Consequently the degree-\(<k\) error of the actual decoder is the unique linear lift of two inputs: the prior cache error restricted to coordinates \(<c_k\), and a scalar multiple of the single new \(W_{j_k}\) coefficient. On the actual chosen level-\(k\) nodes that error must vanish; these are the same invertible upper-coordinate Vandermonde equations that define the actual decoder. In particular the pure unit impulse at birth level \(k\), with preceding error zero, has coefficients exactly zero below \(j_k\) and exactly \(1\) at \(j_k\). Only coordinates at least \(c_k\) can change when matching those real nodes.

Track such an impulse through every subsequent level \(l>k\). There \(c_l=c_k+2(l-k)>j_k\). The copy part of the linear lift takes *all* previous coordinates \(<c_l\) unchanged for this impulse; independently introduced later true missing coefficients are separate impulses, and are set to zero in this summand. The reconstructed high part of the lift has indices at least \(c_l>j_k\). Thus at each subsequent physical copy extension the propagated impulse has coefficient exactly \(1\) at \(j_k\) and exactly zero below it. Denote its final polynomial by \(U_k\). At the final level the virtual error \(G-\widehat F_h\) is a multiple of \(W_h\) by the band at \(n=h+1\). It follows that the actual first-excess residual image is contained in the span of \(W_h\) and these \(\lfloor h/2\rfloor\) final impulses.

This upper containment is equality on **actual** data. Through \(h\) the paid numerical columns span the whole minimum early bank of order \(L(h)=\lfloor(h+1)^2/4\rfloor\), by the usual invertible-commutator dense lower bound. Through \(h-1\) their span has dimension at least \(L(h-1)\). Applying the actual ordinary commutator to those lower columns gives \(L(h-1)\) independent numerical rows with zero model at order at most \(h+1\), because the ordinary commutator is triangular with diagonal \(-\gamma^2\). The combined numerical/model space also maps onto all \(h+1\) polynomial degrees through \(h\). Therefore the zero-numerical model image at first excess has dimension at least \(L(h-1)+h+1-L(h)=1+\lfloor h/2\rfloor\). Since the paid columns span the numerical bank, the actual decoder residual image is exactly this zero-numerical model image: subtract a matching paid column to make its numerical data zero. This proves that **each** final impulse above and \(W_h\) belongs to the true first-excess space \(K_m\). One may use the ordinary cache for the impulse calculation: expansion/contraction of identity edges is an invertible triangular change in the formal tree combinations through each order cap, so the shifted zero-numerical model image is the same residual span.

The first nonzero indices of these basis polynomials are precisely \(0,2,\ldots,h\) if \(h\) is even and \(1,3,\ldots,h\) if \(h\) is odd. For any such positive first index \(j\), multiplication by \(X\) has first index \(j-1\) with nonzero coefficient \(\gamma^2j^2\) times the old first coefficient. This follows from
\[
       XW_j=W_{j+1}+\gamma(2j+1)W_j+\gamma^2 j^2W_{j-1},
\]
and no higher original coordinate can contribute to index \(j-1\). The original basis and these once-marked polynomials therefore attain every first index \(0,1,\ldots,h\) at most once in an independent list. All vanish at the genuine final clock \(\alpha\), since the final actual decoder agrees there with the literal sampled value; the first-excess stage itself is really exact at that clock. They have degrees at most \(h+1=m\). The common-factor ambient space in that degree has dimension \(m=h+1\). Hence
\[
             K_m+XK_m=(X-\alpha)\mathbb P_{\le m-1}.          \tag{1}
\]
In particular a single root mark already saturates the ideal, stronger than the earlier modular generic growth bound. Multiplying by further arbitrary root marks gives the full space \((X-\alpha)\mathbb P_{\le n-2}\) at every order \(n\ge m+1\).

## 2. Exact contact criterion on literal rooted data

The source of a tree \(t\) is the actual polynomial \(F_t=V_t-D_F\mathbf e(t)\), with \(V_t\) the pure early-only profile. The literal \(\alpha\) row applies \(E_\alpha JD_F\), and \(E_\alpha D_F\) is the final numerical coordinate. Thus every \(F_t\) vanishes at \(\alpha\), even above the paid grade. Each has degree at most \(|t|-1\). Through \(m\) their span is precisely \(K_m\), because \(V_t=G_t\) there and paid early data can be subtracted. At \(n\ge m+1\) their span is exactly \((X-\alpha)\mathbb P_{\le n-2}\): (1) supplies a spanning set of true mark descendants of numerical-null order-\(\le m\) heads, and the ambient factor and degree bound gives the converse.

There is a stronger *literal* property of those spanning representatives. A order-\(\le m\) early-null head has actual late column \(E G_t\) by genuine local order. Adjoining the mark \(X\) in the shifted rooted algebra, \(t\#[\bullet]+\gamma t\), multiplies all true stage values by their actual clocks, preserves the early zero, and multiplies the exact model by \(X\). It also multiplies the pure polynomial by \(X\). Thus every polynomial in the saturated source span just described has an actual marked representative with **early actual zero and late actual column \(EF\)** at the stated order. This is not a substitution of the polynomial for an arbitrary high-grade numerical column.

For a true word \(w\) of length \(k\) in marks and strict primitives, let its actual adjoint row be \(a_w\) and formal adjoint polynomial \(P_w\); \(a_\varnothing=b\), \(P_\varnothing=1\). Define
\[
 {\cal S}_n =
 \begin{cases}
 K_m,&n=m,\\
 (X-\alpha)\mathbb P_{\le n-2},&n\ge m+1 .
 \end{cases}
\]
In this direct geometry, exact rooted order \(p\) is **equivalent** to scalar clock quadrature through degree \(p-1\) and the following **actual** finite contacts:
\[
        a_w EF=\ell(P_w F)
            \quad\text{for all }F\in{\cal S}_{p-k},\quad k=|w|\le r.
 \tag{2}
\]
Necessity: use the true representative just proved. Graft the \(k\) word operations above the head in their reverse order, so that the left read is \(a_w\); every unary or mark costs at most one vertex. These operations preserve the numerical early zero and act on the actual late column by \(T\) or by the actual clock diagonal, with the chosen upper adjoints on formal moments. This is a true summed rooted order test, through order \(p\), giving (2). The scalar clock rule follows from the root bushes with zero weights in the early bank. Sufficiency: on any paid tree the only correction is along the spine of its unique child of order at least \(m\); expand each exact sibling product as clock polynomials, as in the literal no-owner recurrence. Each resulting contraction uses a true \(F_t\) of order at most \(p-|w|\), so (2) pays it. Its pure output is integrated by the scalar rule. This restores all shifted order equations, hence ordinary RKOC. No outside full-polynomial test was added at length \(r\); that boundary is the smaller \(K_m\).

## 3. An inductive paid column solve and the late compatibility counts

Suppose actual rows through word length \(k-1\) are known and paid, and \(s\) first reverse positions have already been fixed at which their genuine row span \(V_{k-1}\) has full restriction rank. Keep the lower primitive responses on \(V_{k-2}\) unchanged. Before imposing responses on a basis, require that the proposed model moment targets respect every relation among the actual input rows. The lower-degree rooted tests ensure this when \(2k\le p-1\). At the balanced final shelf it also follows when the degree-\(m\) shifted Legendre polynomial is nonzero at \(\alpha\), as is the case for \(\alpha<0\); do not assume it at an arbitrary Legendre-root value of \(\alpha\). For each basis direction of \(V_{k-1}/V_{k-2}\), prescribe its next primitive response on the remaining \(d-s\) coordinates, leaving the fixed prefix response unchanged. If it has the required moments, a column-by-column physical solve on the \(s\) earlier reverse pivots realizes it, and keeps all already-paid shorter numerical responses literally unchanged. Arbitrary extra earlier taps may be assigned outside those pivots first. This induction never substitutes nominal polynomial inputs for old actual rows.

For \(k<r\), the moment rank on the free sites is \(\min(d-s,p-k-1)\), provided none of those sites equals \(\alpha\), by the genuine common-factor space in (2). If \(d-s<p-k-1\), let \(R\) be their monic nodal hull. The new row is feasible with that fixed prefix **if and only if** its fixed values already give the target contraction against
\[
          (X-\alpha)R(X)Q(X),\qquad
                         \deg Q\le p-k-2-(d-s).
 \tag{3}
\]
These are exactly the functions in the true source span vanishing at all free sites; the remaining desired contacts are obtainable by the full evaluation rank on its quotient. Thus the deficit is a common nodal-hull constraint shared across new actual directions, not a demand for unrelated scalar interpolation. For fixed prefix data both sides of (3) are linear in the coefficients of \(R\), though changing the nodes of course requires rechecking any lower responses that depended on those nodes. At \(k=r\) use \(K_m\) and the analogous actual evaluation restriction test, not a degree-based proxy.

At \(d=L(r)\), previous pivot ranks are at least \(L(k)\). On the balanced even target shapes, optimistically using that minimum, independent moment filling runs out as follows:
- \(p=16,d=20\): at \(k=5,6,7\), the free-coordinate maxima are \(11,8,4\) and the true moment dimensions \(10,9,8\), so the shortages begin at length six (one, then four per new independent response). At \(k=8\) there are no free pivot coordinates and the true final source dimension is four.
- \(p=20,d=30\): for \(k=5,6,7,8,9\), free-coordinate maxima are \(21,18,14,10,5\) and true moment dimensions \(14,13,12,11,10\), so shortages begin at length eight (one, then five). At \(k=10\) no free coordinates remain and the final source dimension is five.

These counts concern the freeze-and-fill strategy. A short fill would not by itself exclude every design; the exact missing conditions are (3). Section 4 gives a separate actual impossibility at the full boundary for the particular nonnegative-clock construction.

### Odd target orders, not just odd reverse length

Under exact order the actual reverse numerical/model decoder through length \(r-1\) exists by the genuine early-null Hilbert test in §1 of [Active tail and canonical abscissae](ACTIVE-TAIL.md). The model of \(V_{r-1}\) has dimension \(r\) and its total dimension is at least \(L(r)\), by the invertible physical commutator. At \(d=L(r)\), its model-zero kernel therefore has dimension \(d-r\). By (2) that kernel annihilates \(E((X-\alpha)\mathbb P_{\le m-1})\) of rank \(m\) when at least \(m\) distinct late clocks are different from \(\alpha\). This requires \(d-r\le d-m\). In a balanced odd target \(p=2r+1\), \(m=r+1\), it is impossible. For \(r\ge4\) the rank hypothesis is automatic at distinct clocks, even allowing a single match with \(\alpha\), since \(L(r)-1\ge r+1\). At \(p=7,r=3\), this particular argument requires no such match. It uses characteristic zero and a canonical cache defined over the coefficient field or its splitting extension, not signs or reality of the weights. The exclusions through 20 are all balanced odd \(p=9,11,13,15,17,19\) in this geometry. Beyond the older parity obstruction for \(r\) even, the new cases are \(11,15,19\), whether or not the clocks are exterior. It does not exclude methods with more late rows, different early bank or nonzero early output weights.

## 4. At balanced even minimum width, the final primitive is forced pointwise

Assume \(p=2m\) with \(r=m\), \(d=L(m)\), and that the actual late ideal \(E((X-\alpha)\mathbb P_{\le m-1})\) has rank \(m\). This is automatic on the nonnegative late grids considered below. The numerical model-zero kernel \(N_{m-1}\) has dimension \(d-m\), and (2) puts it in the annihilator of precisely this \(m\)-dimensional space. By dimension it is the whole annihilator. Appending one strict primitive to a true numerical row of this kernel gives a length-\(\le m\) word combination of zero formal model. Testing it by (2) on every \(F\in K_m\) gives \(N_{m-1} T EF=0\). Therefore \(T EF=E R_F\) for a unique \(R_F\in(X-\alpha)\mathbb P_{\le m-1}\).

Take the pure-mark rows \(bP\), \(\deg P\le m-1\), with one appended primitive. Their exact rooted moments give \(\ell(P R_F)=\ell(P JF)\), since \(bP ER_F\) is the true scalar quadrature of a polynomial of degree at most \(2m-1=p-1\). Both \(JF\) and \(R_F\) have degree at most \(m\). Their difference is therefore a multiple of the monic shifted Legendre polynomial \({\cal L}_m\), by the nonsingular lower-degree orthogonal pairing. When \(\alpha<0\), \({\cal L}_m(\alpha)\ne0\), so the required zero at \(\alpha\) determines that multiple:
\[
        T EF
        =E\left(JF-\frac{(JF)(\alpha)}{{\cal L}_m(\alpha)}{\cal L}_m\right),
                              \qquad F\in K_m .
 \tag{4}
\]
This is not merely another weighted condition; the whole final projected primitive is fixed pointwise on this true first-excess source space.

Let \(\gamma=-g<0\) be real, \(m\ge2\), and choose the early final clock \(\alpha=\gamma\lambda\), where \(\lambda>0\) is the largest ordinary normalized Laguerre root of degree \(m-1\) (hence \(\alpha\) is the smallest physical root of \(W_{m-1}\)). Suppose
\[
                              g\ge 1/(m+1).
\]
Take \(F=W_{m-1}\in K_m\); then \(JF=W_m/m\). The Legendre–Laguerre bounds below show that the polynomial on the right of (4) is strictly positive at every \(X\ge0\).

For \(0\le X\le1\), \(W_m(X)\ge W_m(0)>0\) because all its roots are negative. For standard Legendre normalization \(P_m(1)=1\), the bound \(|P_m|\le1\) on \([-1,1]\) gives \(|{\cal L}_m(X)|\le|{\cal L}_m(0)|\); for instance the usual cosine integral representation proves this by bounding the integrand's modulus. Writing \(\mathscr L_m\) for the ordinary normalized Laguerre polynomial, the ratio inequalities are
\[
 \begin{aligned}
 |W_m(\alpha)|/W_m(0)&=|\mathscr L_m(\lambda)|
       \le\mathscr L_m(-\lambda)
        =\sum_{j=0}^m {m\choose j}\lambda^j/j!,\\
 |{\cal L}_m(\alpha)|/|{\cal L}_m(0)|
       &= P_m(1+2g\lambda)
        =\sum_{j=0}^m {m\choose j}{m+j\choose j}(g\lambda)^j.
 \end{aligned}
\]
In the second sum the \(j\)-th coefficient (after \({m\choose j}\lambda^j\)) is \(\prod_{a=1}^j(g(m+a))/j!\), at least the first sum's \(1/j!\). At the endpoint \(g=1/(m+1)\) the inequality is still strict in the \(j=2\) term (as \(m\ge2,\lambda>0\)); thus the second entire sum is greater. The Legendre correction in (4) consequently has magnitude strictly below \(W_m(0)/m\) on \([0,1]\). For \(X\ge1\), \({\cal L}_m(X)>0\). The sign of \(W_m(\alpha)\) is \((-1)^{m-1}\) by the three-term recurrence on the smallest root of \(W_{m-1}\) and strict interlacing with \(W_{m-2}\); the sign of \({\cal L}_m(\alpha)\) is \((-1)^m\). Their ratio is negative, so the subtracted correction now adds a positive term. This proves the assertion on all \(X\ge0\).

The first physical late row of strict \(T\) is identically zero. Its entry of \(T EF\) in (4) is therefore zero for this true \(F\). If that clock is nonnegative, the forced projected polynomial has strictly positive value there, a contradiction. So at this minimum width and prescribed diagonal range the **first physical late clock itself must be negative**. This rules out completion of the constructed \(\gamma=-1/6\) all-nonnegative order-12, order-16 and order-20 target-order shapes, regardless of later causal repairs or their additional early word projections; in those cases \(m=6,8,10\) and the endpoint hypothesis holds. It also excludes the same nonnegative geometry at other balanced even orders meeting these hypotheses. It does not exclude a negative first late clock, an earlier non-extremal chosen final root, smaller \(g\) outside the displayed proof, a larger bank, or any unrestricted strict SDIRK at these orders.
