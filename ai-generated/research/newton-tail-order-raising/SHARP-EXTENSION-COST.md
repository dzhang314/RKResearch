# Sharp extension costs when output weights may change

Keep the entire old triangular matrix fixed, and put all additional stages after it. The old output weights may be changed. For \(p\ge3\), over the real algebraic numbers the worst-case minimum number of additional stages needed to go from order \(p-1\) to order at least \(p\) is
\[
 \left\lfloor\frac p2\right\rfloor \quad\text{for ERK},\qquad
 \left\lceil\frac p2\right\rceil \quad\text{for DIRK and SDIRK}.
\]
In the SDIRK upper bound the common diagonal is preserved. The lower bound in that class uses a choice of nonzero common diagonal, so it does not assert the same lower bound at every prescribed diagonal. These are worst cases over old tableaux of unrestricted size, not bounds on absolute minimum stages.

Use the normalized tree columns \(\mathbf N_t\), models \(X^{|t|-1}\), and polynomial integration maps \(I,J\) from the companion Newton-tail proof.

## 1. An old zero relation gives a physical tail lower bound

Suppose over a paid ring an old order-\((p-1)\) method has an actual relation
\[
  \sum_{|t|\le m} a_t\mathbf N_t^0=0,\qquad
  f(X)\coloneqq\sum_{|t|\le m}a_t X^{|t|-1},
  \qquad 1\le m\le p-1 .
\]
Set
\[
 d\coloneqq p-m,\qquad \Omega\coloneqq I(X^d f).
\]
The old order conditions give \(I(X^j f)=0\) for \(0\le j<d\), by adding \(j\) root leaves. Suppose \(\Omega\ne0\). In any enlarged order-\(p\) tableau with unchanged old rows, the block \(B\) of new-to-new coefficients cannot have a monic annihilating polynomial of degree at most \(d\).

To prove this, let
\[
 \mathbf F\coloneqq\sum_{|t|\le m}a_t\mathbf N_t
\]
on all stages of the enlarged tableau. Its old coordinates vanish, so applying any polynomial of the enlarged \(A\) to it acts by the same polynomial of \(B\) on its new coordinates. If a monic \(g\) of degree \(e\le d\) annihilated \(B\), then \(g(A)\mathbf F=0\). Applying \(A\) corresponds to applying \(J\) to the model, since \(\mathbf N_{[t]}=|t|A\mathbf N_t\). Multiplying by a clock power corresponds to joining the root with leaves. The order-\(p\) tests would therefore imply
\[
                   I(X^{d-e}g(J)f)=0 .
\]
Every term used in this readout has order at most \(m+e+(d-e)=p\). The integration adjoint sends \(X^i\) to \((1-X^{i+1})/(i+1)\). Thus moving the \(e\) highest integrations to the clock polynomial gives leading coefficient
\[
           \frac{(-1)^e}{(d-e+1)(d-e+2)\cdots d}
\]
at degree \(d\). The terms from lower powers of \(J\), and all lower-degree terms of the adjoint, have zero moment against \(f\). The displayed readout is this unit times \(\Omega\), a contradiction. This argument also applies at \(e=d\), where the readout has no extra clock power.

By Cayley–Hamilton there must be at least \(d+1\) new rows, regardless of their diagonal pattern or output weights. If all new diagonals equal \(\gamma\), then \(B-\gamma I\) is strictly lower triangular and must have nonzero \(d\)-th power. Thus at least \(d+1\) new stages lie on an actual strict path; fewer than \(d+1\) successive layers of mutually uncoupled rows are impossible even with unlimited width per layer. If each layer uses several different diagonals, the sum of the numbers of distinct diagonals within the layers must be at least \(d+1\). Indeed the product of the monic diagonal polynomials for the successive layers annihilates \(B\), by repeatedly moving support past the next layer.

There must also be \(d+1\) distinct clocks among the *new* coordinates with \(b_i F_i\ne0\). The readout of \(X^j\) on this signed coordinate measure is zero below \(d\) and equals \(\Omega\) at \(d\). If its support used \(k\le d\) clocks, multiply their monic node polynomial by \(X^{d-k}\). Its readout would be both zero on the support and equal to \(\Omega\) by its leading coefficient. This clock obstruction requires no sign assumption and no inverse clock differences.

In particular, the obstruction applies to a single added uncoupled layer of common diagonal even if all the old weights may be changed. Together with the previous variable-clock first-error quotient over a field, its vanishing for all old relations is precisely the feasibility criterion for such a layer, when its diagonal may be chosen to equal the first old diagonal. It is enough to check \(m=p-1\): multiplying a smaller relation by the right number of clock powers gives a relation at that last size with the same \(\Omega\). Width alone cannot repair a nonzero \(\Omega\) in a single layer.

## 2. Actual old tableaux realizing the obstruction

For a target \(p=2q+1\), start with \(q\)-node Gauss quadrature on \([0,1]\). For a target \(p=2q\), start with \(q\)-node left Radau quadrature including zero. In the latter case the node polynomial is \(X R_{q-1}\), with \(R_{q-1}\) orthogonal for the weight \(X\). The monic polynomials and their interior roots exist by polynomial orthogonality and the sign-change argument in the Newton-tail note. In each case the quadrature is exact through degree \(p-2\): divide an input polynomial by the monic node polynomial and use orthogonality to kill the quotient term. All coefficients and clocks can be real algebraic.

We detail why these clocks occur in true triangular order-\((p-1)\) methods. Write \(\xi_i\) for the nodes, \(\beta_i\) for their quadrature weights, and \(l_j\) for their cardinal polynomials. Use the collocation matrix
\[
        M_{ij}\coloneqq J_{\xi_i}(l_j).
\]
For stage values sampled from polynomials of degree at most \(q-1\), \(M\) is exact polynomial integration; therefore every normalized branch with child size at most \(q\) is the exact clock power. For a covector readout on an arbitrary node vector \(\mathbf z\), identify \(\mathbf z\) with its interpolation polynomial \(f\) of degree at most \(q-1\). Then
\[
 (\boldsymbol\beta\odot\boldsymbol\xi^{\odot j})\cdot M\mathbf z
 = I(X^j Jf)
 = I\!\left(\frac{1-X^{j+1}}{j+1}f\right)
\]
whenever \(j+q\le p-2\); both integrals may equivalently be computed by the quadrature. A root of size at most \(p-1\) has at most one child of size \(m>q\). Its smaller branches are the exact clock powers, with total size \(j\le p-2-m\), so the displayed adjoint identity applies. The two resulting moments on the large child, at powers \(0,j+1\), are paid by induction on largest root-child size. The decorated child has smaller largest root-child size and total size still at most \(p-1\). The result is \(m(1/m-1/(m+j+1))/(j+1)=1/(m+j+1)\). This proves order \(p-1\) for the collocation method directly on all rooted trees.

Now unroll its stages in blocks to obtain a triangular method. Choose a diagonal \(\gamma\). Take one initial stage with diagonal \(\gamma\) and no other coefficients. Each following block of \(q\) stages has diagonal \(\gamma\) and only coefficients \(M-\gamma I\) on the preceding block. In the first block the preceding stage is repeated as a donor in every column, so its incoming coefficient at row \(i\) is the corresponding row sum of \(M-\gamma I\). Every block has clocks \(\xi_i\). After block \(k\), the normalized tree profiles agree with the collocation stages through size \(k+1\): the preceding block is already correct through size \(k\), and the self contribution in the current block is correct by induction on the smaller child tree. Thus after \(p-2\) blocks put the quadrature weights on the last block to obtain exact order at least \(p-1\). The only physical clock labels are \(\gamma\) and the quadrature clocks. No simultaneous coupled stage solve remains.

For ERK choose \(\gamma=0\). For even \(p=2q\) the only clocks are the left Radau set, so the clock polynomial
\[
             f(X)=X R_{q-1}(X),\qquad m=q+1,
\]
is an actual old relation among the bush columns. Its next moment is \(I(X^q R_{q-1})=I(XR_{q-1}^2)>0\), by monicity and orthogonality. Here \(d=q-1\), forcing at least \(q\) added rows. For odd \(p=2q+1\) with \(q\ge2\), the extra zero clock gives the relation
\[
             f(X)=X G_q(X),\qquad m=q+2,
\]
where \(G_q\) is the monic Gauss polynomial. Its next moment \(I(X^q G_q)=I(G_q^2)>0\) again forces \(q\) rows. For \(p=3\), a two-stage order-two ERK already shows that one new row is sometimes necessary: no old weights can give a nonzero three-vertex tall coefficient on its two-row strict matrix.

For nonzero common-diagonal SDIRK choose \(\gamma\) equal to any nonzero quadrature node. This keeps the clock set at exactly the \(q\) quadrature labels. The even case gives the same lower bound \(q\). In the odd case the relation is \(f(X)=G_q(X)\) itself at \(m=q+1\); its next moment is still \(I(X^q G_q)>0\). This forces \(q+1\) new stages, even if their diagonal may vary. Hence the same worst-case lower bound holds for arbitrary DIRK, not only for extensions that remain SDIRK.

## 3. The matching upper counts

For DIRK and SDIRK use \(\lceil p/2\rceil\) Gauss receivers in the Newton-tail construction. For even-order ERK use the same \(p/2\) receivers.

For odd \(p=2q+1\) ERK use \(q+1\) left Radau clocks, which integrate through degree \(2q=p-1\) and have nonzero weights, as seen by integrating the squares of their cardinal polynomials. Put the zero clock first among them. In the strict tail its row in \(B\) is zero, and its row in \(U_0\) is zero because \(J_0=0\). The feed adjustment in the Newton proof uses \(q\) clock-moment rows. Choose their right inverse using only the other \(q\) distinct clocks. The zero receiver's feed stays zero, so it is literally another copy of the original first stage. Identify the two stages: move each coefficient reading the new zero receiver to the old first column, and move its output weight to the old first stage. Normalized tree entries are unchanged by this identification, by induction on each child tree. It does not change an old row and it preserves strict lower triangularity. This leaves only \(q\) new rows, proving the claimed floor for ERK.

The matching upper and lower statements allow reassigning output weights, including at the original first stage. They do not permit changing the old numerical stage equations.
