# DIRK12/15: three uniform active dirty labels are impossible

In ordinary real fifteen-stage order-twelve DIRK with \(C(2), f_5=3\), suppose there are exactly three active cubic-dirty numerical labels and at each of them all active dirty stages have the same nonzero cubic-defect amplitude. This is impossible by a **weighted reverse grade-five** primitive argument. Neither distinct clean physical rows, a fixed quadrature grid, nor any particular position or count of zero-weight rows is assumed.

Combined with the [nonuniform cancelling exclusion](../dirk12-fifteen-rank3-three-active-nonuniform-cancelling/README.md), the [noncancelling fixed-grid exclusion](../dirk12-fifteen-rank3-three-active-fixed-grid/README.md) and the [variable eight-site exclusion](../dirk12-fifteen-rank3-three-active-variable-eight-noncancelling/README.md), this closes the entire three-active-label face. That does not close an unrestricted fifteen-stage tableau; the real interval remains **15–16**.

Write \(\mathbf h=A\mathbf c^2-\mathbf c^3/3\), \(\beta\mathbf v=\mathbf b\odot\mathbf v\), and \(N=A^{\mathsf T}\). Use \(N\) in reversed **physical** chronology, with scalar reflected primitive \(J^*S(x)=\int_x^1 S\) in the original numerical clock. It is not treated as an unweighted tableau, and no inverse of \(\beta\) is used. Let \(T_j,F_j,\mathcal B_j\) be the actual forward numerical, forward pure and weighted reverse pure spaces at grade \(j\). The actual ranks of \(\mathcal B_3,\mathcal B_4,\mathcal B_5\) are \(1,2,3\). The paid grade-\((3+8)\) product puts the nonzero \(\beta\mathbf h\) in \(\mathcal B_3=\operatorname{Ann}T_8\). The three actual support labels then yield
\[
                    \mathcal B_j=(\beta\mathbf h)P_{j-3}(\mathbf c)\qquad(3\le j\le5)
\]
from the true clock-shift rules and independence on the labels. In particular \(\mathcal B_5\) is zero at every clean row. It contains the genuine scalar reverse degree-four primitive errors there, and \(N\mathcal B_4\subseteq\mathcal B_5\).

At each of the three dirty labels the first weighted amplitude moment vanishes, since the three scalar probes through degree two separate them. Uniformity and the nonzero amplitude imply the ordinary dirty mass at each label is zero. Consequently all scalar quadrature is on live clean labels. There are at least seven distinct such labels including the literal live terminal \(1\). Indeed if there were at most six, \((1-X)\) times the square of the hull of their other labels would vanish on the quadrature and have strictly positive integral, of paid degree at most eleven.

Read the live clean rows in true reverse chronology. Let \(a,b\) be the first two *distinct* relatively nonorigin numerical clean clocks encountered, ignoring repetitions of \(1\) and then of \(a\). They exist by the scalar count. The first reversed physical row is the genuine live terminal at clock \(1\). Every live clean row in the physical reversed prefix through the first occurrence of \(b\) has clock in \(\{1,a,b\}\).

For a scalar polynomial \(S\) in the two-dimensional space
\[
                         (X-1)(X-a)(X-b)P_1
\]
there is at most one linear constraint for \(S(z)/h_z\) at the three active dirty labels \(z\) to match an affine \(Q\). Thus choose a nonzero \(S\) with such an affine \(Q\). The actual weighted grade-four state
\[
                          \beta\bigl(S(\mathbf c)-\mathbf hQ(\mathbf c)\bigr)
\]
vanishes at **all active dirty stages**, by uniformity and that affine matching. It automatically vanishes at every zero-weight physical row, irrespective of its clock and numerical defect. It vanishes at every live clean row through \(b\) by the three selected scalar roots. Hence it is zero on that entire actual physical prefix, including the row of \(b\).

The actual reverse primitive of this state also vanishes through that prefix by lower triangularity in reverse. Its error from \(\beta(J^*S)(\mathbf c)\) lies in the genuine \(\mathcal B_5\), by the true scalar primitive error and \(N\mathcal B_4\subseteq\mathcal B_5\). This pure space vanishes at the two chosen live clean rows, so \(J^*S(a)=J^*S(b)=0\), dividing only their nonzero weights. At the terminal \(J^*S(1)=0\) by definition. Each of these three distinct roots is double, because the derivative is \(-S\) and \(S\) vanishes there. But \(J^*S\) has degree at most five, so it is the zero polynomial and \(S=0\), contradiction.

The entire argument uses the actual weighted low-grade reverse flag. It does not rely on an unproved claim that a normalized transposed tableau has full order. It is analytic, without a modular arithmetic stage claim.
