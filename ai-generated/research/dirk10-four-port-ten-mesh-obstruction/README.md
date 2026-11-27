# Four projected ports do not buy width twelve on the fixed ten-site mesh

This is a **scoped rational exclusion** on the paid ten-site mesh \(j/6\), \(-3\le j\le6\), not a general lower bound for DIRK12. It concerns a four-port version of the successful [compact factorial 13-stage construction](../dirk10-factorial-thirteen-compact/README.md). The no-go concerns the stated projected chronological geometry and **separate payment of the projected errors and injected word errors**. Other meshes, nonprojected methods, and genuinely coupled conditions not implied by these separate payments are outside it.

## One injected direction cannot merge four ports

Let the clean decoder interpolate at \(0,u,p,q,r\) into \(P_4\). All four proper sites \(u,p,q,r\) are supposed to be shared literal old rows, ordered as written, possibly after redirecting between merged copies and their retained rows. In a one-direction correction \(EJ\Pi+\boldsymbol\eta\sigma\) after redirect, the old \(u,p\) rows both avoid the future \(q,r\) slots. Let \(G=X(X-u)(X-p)\). The two future cardinal polynomials have numerators \(G(X-r)\) and \(G(X-q)\), which span \(G,XG\) up to nonzero scaling. Thus the two \(u,p\) primitive rows on \(G,XG\) must have rank at most one. But
\[
       J_uG\,J_p(XG)-J_pG\,J_u(XG)
                 =-\frac{p^3u^3(p-u)^3}{120}
\]
does not vanish. This part does not require any fixed scalar mesh.

## The exact rank-two leading gate

Retain the same seven opening rows: origin, trapezoid, a nonzero midpoint at \(u/2\) satisfying quadratics, Simpson at \(u\), a cubic rule at \(p\) on \(0,u/2,u,p\), and the two adjusted rows at \(q,r\). Assume the named prefix knots needed by these quadratures and the four shared clocks are distinct. Use degree-nine scalar quadrature on the fixed ten-site mesh, with origin carried by the old zero row. Write \(\mathbf w,\mathbf x,\mathbf y=\mathbf1-\mathbf x\) for its nine nonzero reflected weights and clocks, with physical 1 first. Let \(K\) be the raw reflected transpose. It pays \(K\mathbf w=\mathbf w\odot\mathbf y\), \(K(\mathbf w\odot\mathbf y)=\mathbf w\odot\mathbf y^2/2\), and
\[
 K(\mathbf w\odot\mathbf y^2)=\mathbf w\odot\mathbf y^3/3+\mathbf U .
\]
The cubic error is zero at 1 and annihilates \(X,\ldots,X^6\). On the eight proper sites every such density has the form
\[
         U_i=\frac{a+bx_i}{x_i P_8'(x_i)}
\]
where \(P_8\) is their nodal hull. This follows from ordinary cofactor interpolation and a two-dimensional kernel. The replay considers **all** projective \([a:b]\), not just the Jacobi5 direction or the known width-13 density.

The rank-two injection directions must silence the scalar moments through degree four and the two true reverse vectors \(\mathbf U,\mathbf x\odot\mathbf U\). The first five conditions give precisely
\[
        e_i=\frac{f(x_i)}{w_i P_9'(x_i)},\qquad f\in P_3 ,
\]
where \(P_9\) is the hull of the nine nonzero reflected sites. Before the last port \(r\), all three old rows at \(u,p,q\) must have zero tap into the future \(r\) slot. Thus the primitive data of \(F=X(X-u)(X-p)(X-q)\) at \(u,p,q\) must be read by an injection vector, after removing its nonzero cardinal divisor. Equivalently \(f(z)=w(z)P_9'(z)J_zF\) at these three sites. Interpolation writes \(f=f_0+t(X-u)(X-p)(X-q)\). The two reverse tests are linear in \(t\) and homogeneous linear in \(a,b\). Their compatibility determinant is a homogeneous quadratic in \(a,b\).

The [exact census](checked.log) covers all 56 unordered triples of proper sites. All leading coefficients are nonzero, so no projective point at infinity was lost. Five discriminants are negative, 49 are positive nonsquares. The two split cases, writing \(k=b/a\), are
\[
\begin{array}{c|c|c}
 \{u,p,q\}&\text{quadratic}&\text{actual compatible }k\\
 \{1/6,1/2,5/6\}&(k+5)(71k+47)&-5\\
 \{1/3,1/2,2/3\}&(16k+35)(31k+397)&-35/16 .
\end{array}
\]
At the other root in each row both slopes in the two \(t\)-equations vanish and both constant terms are nonzero, so the determinant alone would have falsely admitted it.

## The actual mixed response blocks both remaining orientations

The true size-six source space \(F_5\) contains the polynomial \(F_0=X(X-u)(X-p)(X-q)(X-r)\), from the bush. It also has two independent port-value directions. To see they are really paid by the stated prefix, on size-five input the two opening row errors at \(u=2s,p\) (with midpoint \(s=u/2\)) read the fourth monomial error and the actual error at \(s\). The latter is nontrivial: the earlier trapezoidal cubic defect at the second row is nonzero, and the midpoint's quadratic action requires a nonzero tap there. In the Simpson row the ratio of the fourth monomial error to the midpoint tap is \(s^4/5\). The cubic \(p\)-rule differs by
\[
 \bigl(A\mathbf c^{\,4}-\mathbf c^{\,5}/5\bigr)_p-A_{p,s}s^4/5
                       =\frac{p^3(p-2s)^3}{20(p-s)}\ne0 .
\]
This identifies two independent actual port error directions, not just a projected basis proposed for sufficiency. Hence \(F_5\) is all degree-at-most-five polynomials vanishing at the origin with port values in the corresponding two-dimensional injection image.

Choose the two-dimensional injection space with one direction the usual \(H=X(1-14X+56X^2-84X^3+42X^4)\), with its scalar spike at physical 1, and another direction \(\boldsymbol\eta\). Let \(F_1\) interpolate the values of \(\boldsymbol\eta\) at the four ports and zero at origin. Then \(F_1\in F_5\), and \(\mathbf D=\boldsymbol\eta-EF_1\) vanishes at all four ports. By the separate-payment hypothesis,
\[
 \mathbf h=K(\mathbf w\odot\mathbf y^3)-\mathbf w\odot\mathbf y^4/4
       \quad\text{and}\quad \mathbf k=K\mathbf U
\]
annihilate both \(EF_0\) and \(\mathbf D\).

Let \(z\) be the **last reflected nonport** among the four proper nonport sites. Take \(\mathbf V=F_0(z)\mathbf D-D(z)EF_0\), so it vanishes at every port and at \(z\). A literal merge cannot retain a tap from a forward port into an earlier unmerged high stage. Therefore each nonport reflected row has no port-column coefficients (triangularity also gives zero for its inaccessible indices). On the first four nonports, which are 1 and three proper nonports, \(\mathbf U\) is consequently read as \(\mathbf w\odot E G\), where \(G\) is the cubic interpolant of \(U_i/w_i\) restricted to these four sites. On those rows
\[
           \mathbf k=\mathbf w\odot E J^*G+g_2\mathbf U+g_3\mathbf h ,
       \qquad J^*G(X)=\int_X^1G(s)\,ds ,
\]
where \(g_j\) are the coefficients of \(G(1-Y)\). This is an identity of the actual row actions. Since \(\mathbf V\) annihilates \(\mathbf U\) by the earlier moment tests, and annihilates \(\mathbf h,\mathbf k\) by the separate top payments, necessarily
\[
                 \langle\mathbf V,\mathbf w\odot EJ^*G\rangle=0 .
\]
For each of the two rational orientations, choose the fourth port in any of the five remaining proper positions, and designate any of the four remaining proper positions as the last nonport. The 40 exact values are all nonzero. This exhausts chronology up to an irrelevant permutation of the first three proper nonport donors. Interleaving port and nonport stages does not relax the actual zero-port-column requirement.

## Closed arithmetic and a finite new-mesh scout

    python3 -B check.py
    python3 -B nine_affine_scout.py 500

The main replay uses exact fractions and SymPy rational nullspaces. The four-release core Lean arithmetic checks the 54 nonsquare discriminant receipts, the split coefficients, and the 40 nonzero mixed numerators without extra axioms. It is not a native theorem excluding unrestricted tableaux.

The second program is **bounded evidence only**. It enumerates nine integer knots up to primitive affine diameter 500 whose pairwise gaps are units in \(\mathbb Z[1/210]\), chooses every anchor pair, and tests the degree-nine nodal integral exactly. There are 216 distinct admissible degree-nine meshes in that finite search and none has a nonzero unit terminal weight together with all nonzero scalar weights. It does not bound larger or non-unit-separated meshes.
