# DIRK12/15: the fourth ordinary live diagonal must vanish in both high-site charts

Use real ordinary fifteen-stage order-twelve DIRK, \(C(2),f_5=3\), with weighted-invisible ordinary cubic and four distinct cubic-dirty ghosts. Assume either the [nine-site early reverse return](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md) or [ten-site earliest extra reflected zero](../dirk12-fifteen-rank3-invisible-ten-site-early-zero/README.md) chronology. Then the actual fourth distinct nonzero ordinary live row has **zero diagonal**. Also the actual nodal quintic through the origin and the first four ordinary nonzero live clocks cannot be corrected to zero at the four ghosts by a genuine grade-five mask.

This is a full analytic exclusion of the nonzero-fourth-diagonal subchart in both qualified reverse charts, for all first Legendre roots and nonroots, and all allowed ghost geometries and signed weight splits. It subsumes the earlier [midpoint exclusion](../dirk12-fifteen-rank3-invisible-midpoint-first-nonzero-fourth/README.md), and no enumeration of candidate scalar grids is required. The global real DIRK12 interval remains **15–16**. No scalar degree-twelve moment is paid.

## The actual grade-five mask, and a forced double-root fifth equation

Write \(a,b,c,e,f\) for the actual first five distinct nonzero ordinary live clocks. These are unique physical rows in both qualifications; in the nine-site case the only repeated nonterminal pair is in the early reverse prefix, late in ordinary order. The literal ordinary origin is the only prior live zero at these rows, and all four ghosts precede \(b\). Use physical ordinary scalar variable \(X\) and
\[
                  K(X)=X(X-a)(X-b)(X-c)(X-e).
\]
Let \(\mathcal A\) denote the actual ordinary live-only action of \(A\) on a scalar profile (the literal ghost taps are left out). Its value at a nonterminal live row is a polynomial in that row's scalar clock for every scalar input of degree at most six. In fact in input degree at most five the true scalar discrepancy is in the live \(F_6\) line \(X L_6'(X)\) and its ghost reads are the two true Jacobi modes; at degree six the whole discrepancy, including ghost reads, lies in
\[
                 X\langle L_5'(X),L_6'(X),L_7'(X)\rangle .
\]
This uses the genuine \(7+4=11\) pairing for \(F_7\). Its evaluation at the first three nonzero live rows is nonsingular, including both first-root and nonroot cases by the [actual three-mode rank proof](../dirk12-fifteen-rank3-invisible-fifth-ordinary-live/README.md).

Suppose the actual fourth diagonal is nonzero. The genuine grade-five correction criterion is the vanishing of the fourth-point divided difference of \(F(c_g)/h_g\) on the four ghosts, i.e. \(\sum_g\ell_g F(c_g)=0\) with \(\ell_g=1/[h_gD_g'(c_g)]\). This works even when a ghost shares a live clock. In the scalar two-row model this functional is \(\mathcal D\) up to nonzero scale on \(F(0)=F(a)=0\) in the nonroot case, or the scalar integral to \(a\) up to scale in the first-root case. The literal fourth-diagonal argument in the [split-free tower](../dirk12-fifteen-rank3-invisible-split-free-grid/README.md) works on any nonzero kernel combination of the quartic through the first three live rows and its linear clock lift. Its true grade-seven commutator is zero at those three rows, hence nonterminal-live-zero by the actual mode rank. At the fourth row only its diagonal contributes. For a nonzero physical diagonal this forces the kernel polynomial to vanish there too; it is necessarily a multiple of the displayed monic \(K\). Thus there is an actual grade-five state \(\mathbf S_K\) with scalar \(K\), numerically zero on ghosts and through the first four nonzero live rows.

Put \(R=CA-AC-A^2\). The genuine \(R\mathbf S_K\) is grade seven and vanishes throughout this prefix, so it is numerically zero on all nonterminal live rows by the same exact three-mode rank. This conclusion also holds if \(K\) admits a genuine ghost-zero correction without the nonzero fourth-diagonal assumption. At the fifth live row the only possible nonzero numerical input of \(\mathbf S_K\) is its own value \(K(f)\ne0\); the true commutator value is minus the square of its own diagonal times that input. Consequently the **fifth diagonal is exactly zero**. The actual \(A\mathbf S_K\) is zero on all ghosts by causality: every ghost precedes \(b\) and the state is literally zero through the first ordinary live \(a\)-row. Its live profile is \(\mathcal A(K)\), vanishing on the literal zero and the first five live nonzero rows.

Because \(\mathbf S_K\) is a genuine scalar \(K\) state, \(A\mathbf S_K-JK(\mathbf c)\in F_6\); its true profile is \(JK\) minus a single multiple of \(XL_6'(X)\). This polynomial has degree at most six and is not identically zero: its derivative at zero would force the multiple to be zero since \(K(0)=0\) and \(L_6'(0)=-42\ne0\); then \(JK\) would be zero. Hence the six actual distinct roots force
\[
                      \mathcal A(K)=\lambda(X-f)K,\qquad \lambda\ne0 .
\]
This also means that the actual fifth clock is affine-root rational over its first-four prefix on this branch.

At every nonterminal live row, \(R\mathbf S_K=0\) and the two true ghost-zero supports of \(\mathbf S_K,A\mathbf S_K\) give
\[
   X\mathcal A(K)-\mathcal A(XK)-\mathcal A(\mathcal A(K))=0 .
\]
The last read is valid in degree six since \(\mathcal A(K)=\lambda(X-f)K\) and the actual shifted input is ghost-zero. The literal terminal is not a source of any nonterminal live row. Both sides are polynomials of degree at most seven and there are at least nine distinct nonterminal live labels, so this is an exact polynomial identity. In particular,
\[
        (1+\lambda)\mathcal A(XK)=(X+\lambda f)\mathcal A(K).
\]
If \(\lambda=-1\), the nonzero right side \((X-f)\mathcal A(K)\) would be identically zero. Consequently the true fifth quotient is exactly
\[
        \mathcal A(XK)-X\mathcal A(K)=c_*(X-f)^2 K,
                   \qquad c_*=-\lambda^2/(1+\lambda)\ne0 .
\]
The degree-two repeated root is thus structural, not a numerical or modular coincidence.

## Four paid primitive pairings and the reverse moment sequence

The left side of the last equation differs from \(-J^2K\) by a member of \(X\langle L_5',L_6',L_7'\rangle\): subtract the true degree-six scalar correction for \(XK\), and use that \(X L_6'\) is a linear combination of its three Jacobi neighbors to absorb the extra \(X\)-multiple of the degree-five-input correction. These modes are orthogonal to \((1-X)P_3\) on \([0,1]\) by the genuine grade-seven line calculation (equivalently integration by parts for the shifted Legendre polynomials). Therefore, for \(0\le k\le3\),
\[
              \int_0^1 (1-X)^{k+1}
                [c_*(X-f)^2K(X)+J^2K(X)]\,dX=0 .
\]
These are grade-\(7+4\) tests, not an assumed next exactness grade.

Use reflected variable \(Y=1-X\), and \(w=1-f\) for the fixed reflected fifth ordinary live label. Define a polynomial before eliminating any repeated endpoint,
\[
 P_{\rm old}(Y)=-Y K(1-Y),\qquad
     N_j=\int_0^1Y^jP_{\rm old}(Y)\,dY.
\]
If \(P_{\rm fixed}\) is the hull of the distinct already fixed live labels, then
\[
     (Y-w)P_{\rm old}(Y)=Y^\eta P_{\rm fixed}(Y),
\]
where \(\eta=1\) exactly when the literal terminal clock is repeated among the first five ordinary live rows of the nine-site chart, else \(\eta=0\). This includes the case \(w=0\) as well as any earlier such repetition. In the ten-site chart the extra zero is in the fixed *early reverse* prefix, and is not among the five ordinary clocks being reflected; hence \(\eta=0\) there. These are distinct-label hulls only; no nonzero aggregate at the literal terminal is assumed.

Write \(m_j=\int Y^j P_{\rm fixed}\) and \(n_j=m_{j+\eta}\). All five \(n_0,\ldots,n_4\) are genuinely paid because \(\deg P_{\rm fixed}=7-\eta\); in particular the repeated-endpoint branch can use \(m_5\) without exceeding degree eleven. Then \(n_j=N_{j+1}-wN_j\).

Two scalar primitives give the exact Fubini identity
\[
      \int_0^1(1-X)^{k+1}J^2K(X)\,dX
          =\frac{\int_0^1(1-u)^{k+3}K(u)\,du}{(k+2)(k+3)}
          =-\frac{N_{k+2}}{(k+2)(k+3)} .
\]
Indeed the integral of \((X-u)(1-X)^{k+1}\) from \(X=u\) to \(1\) is exactly \((1-u)^{k+3}/[(k+2)(k+3)]\). The paired equation therefore becomes
\[
       c_*(n_{k+1}-w n_k)
                     =-\frac{N_{k+2}}{(k+2)(k+3)} .
\]
Subtract adjacent instances to eliminate \(N\); using \(N_{k+3}-wN_{k+2}=n_{k+2}\), \(C_*=1/c_*\), we get for \(k=0,1,2\)
\[
 \left[(k+4)+\frac{C_*}{k+3}\right]n_{k+2}
      -(2k+6)w n_{k+1}+(k+2)w^2 n_k=0 .
\]
All of these equations use paid scalar moments and the genuine pure-mode discrepancy, not the unpaid \(\varepsilon_{12}\).

## Why the fifth fixed label must collide with the remaining reverse \(u\)

The [split-free early reverse power sums](../dirk12-fifteen-rank3-invisible-split-free-grid/README.md) imply \(n_0,n_1,n_2,n_3,n_4\ne0\), also in the repeated-endpoint case here where \(m_5\) is paid. In fact the shifted sequence \(S_{j+1}(H_9)\) is proportional to \(S_j(H_{10})\) for \(j=0,\ldots,4\), regardless of the zero endpoint split. Set
\[
         h=\frac{3n_1}{2n_0}\ne0,\qquad q=\frac{n_0n_2}{n_1^2},\qquad z=\frac w h .
\]
The exact reverse guards give \(q\ne0,3,9/4,3/2\). The paid sequence, after dividing \(n_j\) by \(n_0h^j\), is
\[
         \left(1,\frac23,\frac{4q}{9},
             \frac{16q^2}{27(3-q)},\frac{160q^3}{81(3-q)(9-4q)}\right).
\]
These ratios use only the true aggregate nonzero \(d,v,u\) weights, not positivity or physical splits.

Insert this sequence in the three paid recurrences. The first determines
\[
                    C_*=-\frac{3(8q+9z^2-18z)}{2q}.
\]
Substitution into the second and third gives, after removing guarded nonzero scalar factors,
\[
 \begin{split}
          (-8q+9z)(6qz+2q-9z)&=0,\\
          (2qz+6q-9z)(6qz+2q-9z)&=0 .
 \end{split}
\]
If their common second factor were nonzero, the first two factors would give \(z=8q/9\) and \(q=9/8\), hence \(z=1\), which makes that common factor zero after all. Thus \(6qz+2q-9z=0\). This determines
\[
                     \frac wh=z=-\frac{2q}{6q-9}
                      =-\frac{L}{L-2}=\frac uh,\qquad
                       L=\frac{4q}{9-4q},
\]
where \(u\) is the **true remaining third reverse nonzero clock**, as prescribed by the split-free reverse shape formula. Hence \(w=u\). This contradicts distinctness of the next reverse live label \(w\) from the already occurred \(u\) in both literal chronologies. It also covers the nine-site \(w=0\) option: \(u\ne0\) there.

The contradiction rules out even a corrected genuine ghost-zero quintic \(K\), independently of how it would have arisen. In particular any survivor of either chart must have zero fourth diagonal and nonzero ghost divided difference for this quintic. Other high-site reverse chronologies are not included.

## Verification

    python3 -B verify.py

The exact symbolic replay checks the ordered-support polynomial identity, primitive Fubini coefficients, the universal reversed shape, all paid elimination factors, and the final common-factor identity. Portable kernel companions check the abstract cleared scalar implications. The stage-space and real analytic reasoning are mathematical, not a full native rooted-order theorem.
