# A literal polynomial recurrence and graded pivot induction on the forced star

Use the nowhere-zero no-mixing singleton chart of FORCED-STAR-OR-MIXED-RESIDUAL-FEED.md. In particular \(\kappa\in\mathbb R\setminus\{0,\pm1\}\), the first three rows are a star, and every strict feed joins two successive levels \(d_i\). The level \(d\) has \(n_d\) physical stages with different clocks. The sole layer-zero stage has clock \(\gamma\), and layer one consists of exactly rows 2 and 3: each such stage has only the first preceding stage as feed, and the resulting quadratic for its clock has at most two roots. The forced star attains both. The level polynomial \(B(t)\) from the preceding work has at least \(m\) distinct roots, so \(D_*\ge m\) and every level from zero to \(m\) occurs.

## Exact row recurrence once a leading set of layers commutes

Put \(\mathbf v_k\coloneqq N^k\mathbf1\) and \(G\coloneqq\operatorname{diag}(\mathbf g)\). Physical level-to-level support gives \(GN=\kappa NG\) and \(\mathbf v_k=0\) on levels less than \(k\). The commutator \([A,M]=[N,[C,N]]\), \(M=CA-AC-A^2\), uses only strict paths of two steps. In particular its rows of level \(d\) can have nonzero columns only at level \(d-2\).

The set of all physical sites of levels at most \(d\) is closed under predecessor reads, even if its chronological labels are interleaved with other sites. Suppose the commutator \([A,M]\) is zero entry by entry on this closed set. Then \(N\) commutes with \([C,N]\) there, and \([C,N^k]=kN^{k-1}[C,N]\). Applied to \(\mathbf1\), using \(M\mathbf1=-2\mathbf g\) and \(N^{k-1}G=\kappa^{-(k-1)}GN^{k-1}\), the actual equality becomes
\[
 (k+1)\mathbf v_{k+1}
 = (C-(2k+1)\gamma I)\mathbf v_k
        +k(2\kappa^{-(k-1)}G-\gamma^2 I)\mathbf v_{k-1}.
                                                                    \tag{3}
\]
At an exact layer \(d\) stage put \(w=(c_i-\gamma)/\gamma\). The physical entries \(k!(v_k)_i/\gamma^k\) are thus values of the monic polynomials
\[
 F^{(d)}_0(w)=1,\quad F^{(d)}_1(w)=w,\quad
 F^{(d)}_{k+1}(w)=(w-2k)F^{(d)}_k(w)
               +k^2(\kappa^{d-k+1}-1)F^{(d)}_{k-1}(w).
                                                                    \tag{4}
\]
The entry of \(\mathbf v_{d+1}\) is zero by literal layer support. Every such clock therefore satisfies \(F^{(d)}_{d+1}(w)=0\), so \(n_d\le d+1\). None is also a root of \(F^{(d)}_d\): the coefficients \(k^2(\kappa^{d-k+1}-1)\) are all nonzero for \(1\le k\le d\), so two consecutive zero values would propagate down to \(F^{(d)}_0=0\). Thus \((v_d)_i\ne0\) at every physical stage of that level. This is an actual reach despite arbitrary signed tap cancellations, not a nonzero-graph-path guess.

## How the first three rows pay the initial propagation

At the tied floor \([A,M]\mathbf1=0\) globally by the earlier low-degree pure argument. Its entries through level two are therefore zero: the only possible length-two source there is layer zero, with one site. Formula (4) now applies at layer two and gives the explicit cubic
\[
                 w^3-6w^2+(\kappa+1)(\kappa+3)w-4(\kappa^2-1)=0 .
\]
In particular \(\mathbf v_2\) never vanishes on the actual layer-two stages. It vanishes on the three stages of layers zero and one. The actual rooted \(E_2\) has dimension four, and its restriction to those three different clocks has rank three already on \(1,c,c^2\). Hence its kernel there is precisely the line of \(\mathbf v_2\). Now \([A,M]\mathbf c\in F_4=ME_2\), and \([A,M]\mathbf c\) is zero on layers zero, one and two. Its inverse under \(M\) lies in that same one-dimensional kernel. But \(M\mathbf v_2\) is nonzero on every layer-two stage, because on that level the only surviving contribution is its diagonal \(-\gamma^2(v_2)_i\). Consequently
\[
                              [A,M]\mathbf c=0
\]
globally. Layer-three rows of \([A,M]\) now vanish entry by entry, since they read only layer one with two distinct clocks, and both moments of orders zero and one are zero. Formula (4) at layer three gives an actual quartic \(F^{(3)}_4\) and nonzero \(\mathbf v_3\) at every stage of that layer. For example
\[
 F^{(3)}_4(w)=
 \bigl[(w-6)(w-4)+9(\kappa-1)\bigr](w^2-2w+\kappa^3-1)
                   +4(w-6)(\kappa^2-1)w .
\]

For the next step at \(p\ge7\), if layer two has at least two actual clocks, then \(E_3\) restricts to the levels zero through two with rank five. The first three stages give rank three, and the two columns \(\mathbf v_2,C\mathbf v_2\), zero earlier, give rank two on distinct layer-two clocks. The dimension of \(E_3\) is six, and \(\mathbf v_3\) is a nonzero kernel column. Since \([A,M]\mathbf c^{\odot2}\in F_5=ME_3\) and is zero through level three, the same argument forces \([A,M]\mathbf c^{\odot2}=0\) globally, hence entrywise vanishing through level four. At even order six the same rank-five calculation, together with nonzero \(\mathbf v_3\) in the kernel, instead contradicts \(\dim E_3=5\); this means a no-mixing singleton candidate at that floor would have at most one layer-two clock.

## Portable test, and where it can stop

The preceding step has an exact general formulation. Suppose the first \(r\) clock moments of \([A,M]\) vanish globally (powers \(0,\ldots,r-1\)); the commutator vanishes entrywise through level \(r+1\); and \(r+3\le p-1\). Suppose also that the restriction of the genuine \(E_{r+1}\) to levels at most \(r\) has kernel the one-dimensional span of \(\mathbf v_{r+1}\). Then \([A,M]\mathbf c^{\odot r}\in F_{r+3}=ME_{r+1}\), vanishes through level \(r+1\), and the inverse via \(M\) lies in that kernel. Formula (4) says \(\mathbf v_{r+1}\) is nonzero on each actual stage of level \(r+1\), whereas all its earlier levels are zero. Thus the next clock moment vanishes globally. The commutator now vanishes entrywise through level \(r+2\), since at that next layer the predecessor layer \(r\) has at most \(r+1\) clock values, and the moments of degrees \(0,\ldots,r\) separate them.

There is a simple **measured** sufficient condition for that one-dimensional kernel. Use the actual \(\mathbf v_d,C\mathbf v_d,\ldots\) on each layer \(d\le r\). They have grade \(d,d+1,\ldots\) and vanish on earlier layers; \(\mathbf v_d\) is nonzero on the entire \(d\)-th layer by (4). They therefore supply the independent lower-bound count
\[
                 \sum_{d=0}^r \min(n_d,r+2-d)
\]
on the restriction of \(E_{r+1}\), by ordinary Vandermonde rank and distinct layer pivots. If this reaches \(\dim E_{r+1}-1\), the known nonzero \(\mathbf v_{r+1}\) in the kernel gives equality and licenses the step. If it is lower, no propagation has been earned by this argument.

One concrete consequence concerns the first scalar collapse. Let \(N_j=\lfloor(j+2)^2/4\rfloor\) be the unrestricted number of weight-at-most-\(j\) polynomial coefficients. If all layer sizes \(n_d=d+1\) for \(0\le d\le m-2\), the measured count proves propagation through the stage of obtaining commutator zero entrywise at level \(m\): indeed for \(r\le m-2\) the count is \(N_{r+1}-1=\dim E_{r+1}-1\). At grade \(m\), the corresponding rank from layers \(0,\ldots,m-1\), plus the nonzero pivot \(\mathbf v_m\) at layer \(m\), forces at least \(N_m\) dimensions if \(n_{m-1}\ge2\), and at least \(N_m-1\) if \(n_{m-1}=1\). This uses \(\sum_{d=0}^{m}\min(d+1,m+1-d)=N_m\). The saturated dimension is \(N_m-1\) at even order and \(N_m-2\) at the tied odd order. Therefore at tied odd order some layer \(d\le m-2\) must fall short of \(d+1\); at even order either that happens or \(n_{m-1}=1\). This identifies an actual occupancy/rank obstruction, not a method for filling those layers from the abstract floor alone.

All statements here retain the nonzero-residual, singleton and single-feeding-level restrictions; the zero branch of the companion note has a different mechanism. No claim is made that the measured occupancy threshold is automatic for unrestricted tableaux, or that this raises an unconditional numerical bound.
