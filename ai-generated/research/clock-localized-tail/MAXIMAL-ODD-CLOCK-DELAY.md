# Stage-tight odd explicit methods must delay clock closure to the last possible degrees

Let \(p=2d+1\) with \(d\ge6\). Suppose an ordinary order-\(p\) explicit Runge–Kutta tableau over a field in which \(p!\ne0\) has precisely \(s=p+d=3d+1\) stages. Use \(E_g,F_g,C,Y,D\) as in the [penultimate-tap proof](PENULTIMATE-PAID-TAP.md); \(g\) is the tree degree (size minus one). Define rows and a parameter by
\[
 \mathbf h_1\coloneqq\mathbf b A-\mathbf bY,\qquad
 \mathbf h_2\coloneqq2\mathbf bYA-\mathbf bY^2,\qquad
 \epsilon\coloneqq
 \begin{cases}1&\mathbf h_1\ne0,\\0&\mathbf h_1=0.\end{cases}
\]
Let \(\mathbf e_s\) be the last coordinate vector. In the proof below, the stage bound on the truncated tableau first shows \(b_s
e0\). When \(\epsilon=0\), it then follows that \(A\mathbf e_s=Y\mathbf e_s=0\). Define
\[
 H_g\coloneqq
 \begin{cases}
   E_g &(\epsilon=1),\\
   E_g+K\mathbf e_s&(\epsilon=0),
 \end{cases}
 \qquad
 W_j\coloneqq H_d+CH_d+\cdots+C^jH_d
 \quad(j\ge0),
\]
where \(K\) denotes the coefficient field. Let \(\delta\) be the smallest \(j\) such that \(CW_j\subseteq W_j\).

**Theorem.** One has \(\delta\ge d-1\). Moreover
\[
    \dim F_d=d,\qquad
    H_{d+j}=W_j,\qquad
    \dim H_{d+j}=2d+2-\epsilon+j\quad(0\le j\le d-1).
                                                                    \tag{1}
\]
If \(\epsilon=0\), then \(\delta=d-1\) and \(W_{d-1}=K^s\). If \(\epsilon=1\), then \(\delta\) is \(d-1\) or \(d\); the complete clock closure is a hyperplane or the entire stage space, respectively. Thus at every degree through \(2d-1\) the only available new numerical direction in the augmented band comes from multiplication by \(C\), even though \(A\) and rooted products obey all their exact conditions.

This is a restriction on a hypothetical equality-stage tableau, not yet exclusion of all equality-stage tableaux. At \(p=13,15,17,19\) the respective minimum delays are 5, 6, 7, 8.

## Why the augmented band has no spare dimension

The two inputs below also give the established stage floor \(s\ge p+d\) without any clock-invariance assumption. First, the pure-space sixth-size theorem gives \(\dim F_5\ge5\) for an ordinary method of order at least six over a paid field. Its proof is in the [pure-rank bound through tree size six](../erk-dense-width/README.md). Strict pure growth through degree \(d\) gives \(\dim F_d\ge d\). The model separates through degree \(d\): a relation between actual vectors with model \(P\) would give \(P(0)=0\) and the \(d\) paid tests \(\int_0^1 X^aP(X)\,dX=0\) for \(0\le a<d\). The weight-\(X\) Gram on \(P/X\) is nonsingular, so \(P=0\), and therefore \(\dim E_d=d+1+\dim F_d\).

Second, define the reverse row spaces
\[
 R_0\coloneqq K\mathbf h_1,\qquad
 R_{r+1}\coloneqq R_r+R_r A+R_rY+K\mathbf h_2\quad(r\ge0).
\]
They annihilate \(E_g\) when \(g+r+2\le p\), by the exact adjoint words. Their dimensions satisfy \(\dim R_r\ge r+\epsilon\) for \(0\le r\le d-1\). For this, a plateau would make the row space invariant under \(A,Y\) and contain \(\mathbf h_2=2\mathbf bYA-\mathbf bY^2\). A diagonal operator \(Y^\dagger\) that inverts the nonzero entries of \(Y\) and sends zero to zero is a polynomial in \(Y\). Modulo the invariant row space, this identity would give \(\mathbf bY=2\mathbf bY A Y^\dagger\). The matrix \(A Y^\dagger\) is strictly lower triangular and nilpotent, so \(\mathbf bY\) itself would belong to the row space. This contradicts its paid nonzero read on \(\mathbf1\); every row of the space kills \(\mathbf1\) within the stated budget.

If the last nonzero coordinate of \(\mathbf b\) is \(t\), truncation after \(t\) gives the same order by strictness. For any such truncated tableau with \(\mathbf h_1=0\), its final clock is 1 because the last coordinate of \(\mathbf b A\) is zero and that of \(\mathbf b\) is nonzero. The final basis vector is not in its \(E_d\): otherwise its model \(P=XQ\), \(\deg Q\le d-1\), would satisfy
\[
 \int_0^1 X^a P(X)\,dX=b_t\quad(0\le a\le d),
\]
and consecutive differences, by the nonsingular weight-\(X(1-X)\) Gram, give \(Q=0\), contrary to \(b_t\ne0\). Every \(R_r\) kills that basis vector: both seeds do, and \(A,Y\) kill it as well. Thus the dimension of the last \(d-1+\epsilon\) reverse ranks plus \(d+1+\dim F_d+1-\epsilon\) forward and auxiliary directions forces \(t\ge p+\dim F_d\ge p+d\). This is the established odd stage floor in precisely the form used here.

In an equality-stage tableau this proves \(t=s\), \(\dim F_d=d\) and that \(\dim H_d=2d+2-\epsilon\). At grade \(d+j\), the reverse space \(R_{d-j-1}\), also killing the added \(\mathbf e_s\) when present, has dimension at least \(d-j-1+\epsilon\). Therefore
\[
                  \dim H_{d+j}\le\dim H_d+j
                  \qquad(0\le j\le d-1).                         \tag{2}
\]
If \(W_j\) has not yet stabilized, the next increment is at least one. It follows from \(W_j\subseteq H_{d+j}\) and (2) that \(W_j=H_{d+j}\) with precisely one increment at each step \(1,\ldots,\min(\delta,d-1)\). After the first increment, no larger clock increment is possible at any later step: multiplication by \(C\) induces a surjection \(W_j/W_{j-1}\to W_{j+1}/W_j\).

## A last-path cutoff at a measured clock

For a vector in \(H_g\) supported at a single clock \(\theta\ne1\) and with nonzero \(\mathbf b\)-output, the scalar identity
\[
 \mathbf b A^{p-1-g}\cdot\mathbf u
    =\frac{(1-\theta)^{p-1-g}}{(p-1-g)!}\,\mathbf b\cdot\mathbf u
\]
holds when \(g\le p-1\). This is a paid word identity; for an added final coordinate, both sides are unaffected for positive length when evaluated on a numerical vector, using \(\mathbf bY^{p-1-g}\) for the right side before localizing. At zero length the statement is tautological. A nonzero tap of that length requires a strict path of that many physical stages after the vector begins. Thus its first nonzero physical index is at most \(s-(p-1-g)\). Only this bare cutoff is needed, not the stronger localized five-tap cutoff.

## Short closure would recover every needed early output

Put \(k\coloneqq s-p+d=2d\), and let \(\mathbf v\in E_d\) be zero through physical row \(k\). Suppose \(\delta\le d-2\). Set \(W\coloneqq W_\delta\). The preceding equality of low ranks gives
\[
  A^j\mathbf v\in H_{d+j}=W_j\subseteq W
  \qquad(0\le j\le\delta).
\]
It also starts strictly after row \(k+j\) by triangularity. Since \(W\) is \(C\)-invariant, each clock projection of \(A^j\mathbf v\) is an actual member of \(W\subseteq H_{d+\delta}\). Each projection on a clock other than 1 with nonzero \(\mathbf b\)-output starts by row
\[
          s-(d-\delta)=k+\delta+1
\]
by the bare cutoff. Such projections have disjoint physical supports. There are therefore at most \(\delta+1-j\) nonendpoint charged clocks for \(A^j\mathbf v\).

For \(\mu_r\coloneqq\mathbf bA^r\cdot\mathbf v\), the companion penultimate-tap theorem with \(L=d\) gives \(\mu_{d-1}=0\). At \(j=\delta\) there is at most one charged clock for \(A^\delta\mathbf v\). Its \((d-1-\delta)\)-th \(Y\)-moment is zero by the paid identity
\[
    \mathbf bY^r A^j\cdot\mathbf v=r!\,\mu_{r+j}
    \quad(1\le r\le d-j).
\]
Since \(d-1-\delta\ge1\), a single nonendpoint charge cannot make that moment vanish unless the charge is zero. All these positive moments are therefore zero, including \(\mu_{\delta+1},\ldots,\mu_d\).

Now descend in \(j\). If the taps \(\mu_{j+2},\ldots,\mu_d\) vanish, then \(A^j\mathbf v\) has \(d-j-1\) consecutive vanishing positive \(Y\)-moments, from powers 2 through \(d-j\). That number is at least \(\delta+1-j\), the largest possible number of nonendpoint charged clocks. A Vandermonde matrix on their distinct nonzero \(Y\)-clocks implies that the individual charges vanish. This yields \(\mu_{j+1}=0\) too. At \(j=0\), all taps \(\mu_1,\ldots,\mu_d\) vanish. The argument also covers \(\delta=0\).

This holds for every actual vector of \(E_d\) that vanishes through row \(k\). Consequently every row \(\mathbf b A^m\), \(1\le m\le d\), factors on \(E_d\) through the first \(k\) physical reads. The different taps may use different early rows. Truncating the tableau preserves all rooted stage data on these first \(k\) rows, so those rows are simultaneously exact on profiles of degree at most \(d\) for the \(d\) scalar weights \((1-X)^m/m!\).

Here is why those early rows cannot exist. Their joint reads and the literal first stage enforce separation of the polynomial profile on the prefix: a possible alias \(P=XQ\), \(\deg Q\le d-1\), is killed by every functional \(\int_0^1 (1-X)^m P\), \(1\le m\le d\); the weight-\(X(1-X)\) Gram gives \(Q=0\). Also the weight-\((1-X)\) Gram gives a polynomial \(S\) of degree at most \(d-1\) with
\[
 \int_0^1 (1-X)S(X)P(X)\,dX=\int_0^1 P(X)\,dX
 \quad(\deg P\le d-1).
\]
Expressing \((1-X)S\) in powers \((1-X)^m\) gives an actual combination of the prefix rows making an ordinary order-\(d\) output. Its pure dimension through degree \(d-1\) is at least \(d-1\), by the unrestricted size-six floor and strict pure growth. It grows at least once more at degree \(d\): a pure plateau would make the common pure space invariant under \(A,C\); the relation \(A\mathbf c-\mathbf c^{\odot2}/2\) in that space would then put \(\mathbf c\) itself there by inverting \(C\) on its nonzero coordinates and using nilpotence of \(C^\dagger A\). But the actually available shift-one output reads \(\mathbf c\) as \(1/6\ne0\). Thus the pure rank through degree \(d\) is at least \(d\); with separation there are at least \(2d+1\) independent columns on the prefix of size \(2d\). This contradiction proves \(\delta\ge d-1\).

All Gram determinants above use only the paid factorials through \(p!\), by the factorial Vandermonde proof in the published paid Beta argument. Equations (1) and the terminal clock-closure alternatives follow from (2) and the fact that the initial clock growth and every subsequent growth are exactly one until stabilization. No Lean acceptance or new unrestricted numerical table entry is being claimed.
