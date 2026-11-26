# Actual donor positions and reverse row overlap for clean weighted fibres

Use the definitions of COMPLETED-FIBRE-HERMITE-RANK.md. Clock fibres may repeat, and their aggregate weights may cancel. All derivatives and primitive identities here refer to true rooted data with paid factorials.

## Subtracting the last diagonal earns the same evaluations on an earlier prefix

Let a live clock fibre have exact normalized row \(\boldsymbol\rho_\theta=w_\theta/\bar b_\theta\) through degree \(a=p-q\). It may consist of a single clean stage or several exact weighted stages. Let \(i\) be its last actual nonzero weight index and assume \(\delta\coloneqq a_{ii}\ne0\). Define the actual shifted row
\[
                 \boldsymbol\xi_\theta\coloneqq
                                      \boldsymbol\rho_\theta(A-\delta I).
\]
Its support is strictly before row \(i\), and through degree \(a-1\) its scalar action is
\[
                   P\longmapsto (JP)(\theta)-\delta P(\theta).
                                                                    \tag{4}
\]
No assumption that earlier weights on the same clock have equal diagonal values is used to cancel the last coefficient; other coefficients must be read from the actual shifted row.

Suppose \(\boldsymbol\xi_\theta\) is supported on a literal leading prefix \(P\). That prefix pays the **entire** same primitive family \(P(x)\longmapsto(J^uP)(\theta)\), \(0\le u\le a-j\), through every grade \(j\le a-2\). Indeed for \(1\le v\le a-1-j\), right multiplication of (4) by \((\theta I-C)^v\) has scalar action
\[
         \int_0^\theta(\theta-x)^vP(x)\,dx
                         =v!\,(J^{v+1}P)(\theta).
\]
Thus \(u=2,\ldots,a-j\) are all paid. Right multiplication of (4) by \(A\) gives \((J^2P)(\theta)-\delta(JP)(\theta)\), which recovers \(u=1\) using \(\delta\ne0\). Finally (4) recovers \(P(\theta)\). All these new rows remain on \(P\), since it is a leading prefix. The recovered point row, for example, can be written as the literal expression
\[
        \delta^{-2}\boldsymbol\xi_\theta
                         \bigl((\theta-\delta)I-C-A\bigr).
\]
If the last actual coefficient of \(\boldsymbol\xi_\theta\) is at \(l\), the recovered point row's coefficient there is exactly
\(\delta^{-2}\xi_{\theta,l}(\theta-\delta-c_l-a_{ll})\); a vanishing coefficient is a measured extra saving, not a consequence of repeated clocks. When \(\theta=0\), formula (4) itself already recovers the evaluation through degree \(a-1\), and all higher primitives at zero are zero.

Consequently at any prefix one may count **both** fibres completed there and future live fibres whose actual shifted rows are there. Those receipts have the same simultaneous Hermite rank (2) through \(a-2\). At the two higher grades the older complete and shifted receipts have different budgets. At \(a-1\), the shifted functional is only \(H(\theta)-\delta H'(\theta)\) for \(H=JP\); one may use its actual scalar rank together with the complete Hermite rows. Distinct clock labels alone do not justify treating these mixed value-and-derivative tests as a full unconstrained Hermite sample. At \(a\), count only the unshifted receipts unless other exact information is present.

As a concrete necessary condition assume \(a\ge2\), \(\theta\ne0\), and the actual leading prefix through the last support of \(\boldsymbol\xi_\theta\) is nonsingular. This shifted row cannot be zero, since the argument recovers a nonzero point evaluation. Write \(l\) for its last actual coefficient. On that prefix the scalar rank through any \(j\le a-2\) is at least \(\min(j+1,a-j+1)\). Summing the ordinary nonsingular parity bound through \(a-2\) (the parity ending at \(a\), minus its last scalar count one) gives
\[
                           l\ge Q(a+1)-1 .                         \tag{5}
\]
For a singleton, \(\boldsymbol\xi_\theta\) is exactly the actual off-diagonal incoming row. A clean singleton at its \(Q(a+1)\) placement floor must therefore have a genuine nonzero adjacent tap \(a_{i,i-1}\). More generally a cut supporting several such shifted rows pays one joint Hermite sum through \(a-2\), not separate copies of (5). The diagonal hypothesis in (5) is only on the actual donor prefix; the numerical value of a common diagonal was not preserved by any rescaling.

## Actual ambient row rank and shared pivots

On a fixed leading tableau let \(\mathcal R_j\) be the ordinary row span of all \(w_\theta A_{PP}^u\) for the completed fibres, including those of zero aggregate, with \(u\le a-j\). Its restriction to \(E_j\) has rank exactly \(H_j\) by the preceding Hermite proof. Accordingly
\[
             \dim\operatorname{Ann}(E_j)\ \ge\ \dim\mathcal R_j-H_j,
                       \qquad k\ge\dim E_j+\dim\mathcal R_j-H_j.    \tag{6}
\]
One may enlarge \(\mathcal R_j\) by other true scalar rows at the same grade, using the measured rank of the full union on both sides. Knowing that the scalar functionals agree does not imply that the actual physical rows agree, nor vice versa.

For a simple measurable cut in the common-diagonal class put \(N=A_{PP}-\gamma I\), which is strictly lower triangular. For each completed fibre let \(i_\theta\) be its last physical nonzero weight row. Whenever all \(u\) actual adjacent links from \(i_\theta-u\) to \(i_\theta\) are nonzero, the paid row \(w_\theta N^u\) has last nonzero column \(i_\theta-u\) with coefficient
\[
                      b_{i_\theta}\prod_{\ell=i_\theta-u+1}^{i_\theta}
                                                   a_{\ell,\ell-1}.
\]
No earlier term in \(w_\theta\) can reach that column in \(u\) strict steps, and there is only one strict path of length \(u\) between these endpoints. Let \(I_j\) be the union of all the thus-verified physical columns \(i_\theta-u\) for \(0\le u\le a-j\), including \(u=0\). Then \(\dim\mathcal R_j\ge |I_j|\), by triangular row pivots. Use the union, not the sum of separate fibre path lengths: shared physical donor columns may overlap. Combining with (6) and the scalar parity ranks gives, for each \(0\le J\le a\),
\[
 k\ge \sum_{\substack{0\le j\le J\\j\equiv J\ ({\rm mod}\ 2)}}H_j
                                + (|I_J|-H_J)_+                    \tag{7}
\]
in a nonsingular prefix. More accurately use the strengthened scalar ranks or the exact row rank. This imposes a real overlap condition in narrow leading geometries: a design at the scalar width lower bound cannot also insist on more independently positioned adjacent donor words than its available scalar rank. Zero-sum completed fibres use the same counted union and can contribute genuine annihilator rows. For genuinely varying diagonals, (6) is exact but the adjacent coefficients in (7) are not automatically those of a strict shifted word; use the actual row ranks instead.

The paths counted here begin at the last weighted row of the stated fibre because its actual coefficient and adjacent links supplied the pivot. This is a different statement from a long path forced by a full suffix orbit in the tail visibility argument, where a path need only start at some row carrying a nonzero suffix weight, not necessarily its endpoint-clock row. None of the donor or overlap conditions are inferred for every minimizing method. No unrestricted stage-count table is changed.
