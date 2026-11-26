# Exact chronological tests on the two-coordinate curves

Use the orders, stage count and coordinate pairs from [The two equations and the weights](SIMPLE-LEGENDRE-COMPLETE-INTERSECTION-AND-WEIGHTS.md). The pair data in this note have no zero second coordinate, and are either obtained from a floor tableau or proposed through the complete-intersection hypotheses of that note. Define the numerical space \(V_j\) to be evaluation at the actual ordered pairs of all polynomials of weighted degree at most \(j\), with \(V_j=0\) for negative \(j\). Thus \(V_{p-2}\) is full. Fix a nonzero common diagonal \(\gamma\).

## A literal interpolation basis

At each physical index \(i\), let \(d_i\) be the least grade for which there is a vector in \(V_{d_i}\) zero on all indices less than \(i\) and nonzero at \(i\). It depends on the given chronological ordering, not on sorting by \(c_i\). Choose a polynomial \(f_i(x,z)\) of weight at most \(d_i\) whose vector \(\mathbf v_i\) has those earlier zeros and value \(1\) at \(i\). The \(\mathbf v_i\) with \(d_i\le j\) form a basis of \(V_j\): their different leading pivot indices give independence, and the possible pivot indices count the dimension by successively restricting to leading prefixes. Write
\[
          u_i(x)\coloneqq\int_0^x f_i(t,0)\,dt .
\]
For each \(i\) consider the following finite membership in the numerical restriction to the literal prefix \(\{1,\ldots,i\}\):
\[
 \boxed{\quad
 \left(-\frac{u_i(c_1)}{g_1},\ldots,-\frac{u_i(c_{i-1})}{g_{i-1}},
                         \frac{\gamma-u_i(c_i)}{g_i}\right)
              \in V_{d_i-1}\big|_{\{1,\ldots,i\}}.\quad}             \tag{3}
\]
These tests concern one genuinely normalized leading column at a time. They consist only of evaluation and a rank or consistency calculation on known pair data.

The following criterion is necessary and sufficient for the candidate data to come from a real strict common-diagonal order-\(p\) tableau with this physical ordering, with residual exactly \(\mathbf g\): the complete-intersection moment data of the first note, the endpoint normalization \(c_1=\gamma,\ g_1=\gamma^2/2\), and all the membership tests (3). The weights are fixed by (1) of that note. Neither this criterion nor the curve count assumes an interpolation problem is automatically solvable.

## Proof of necessity and sufficiency

The exact rooted profile requirement for a general polynomial \(f(x,z)\) of weight \(j\) is that its evaluated vector, after applying \(A\), differ from the primitive of \(f(x,0)\) evaluated at the clocks by a vector in \(G V_{j-1}\). This is necessary at stage saturation by \(F_{j+1}=G E_{j-1}\), ordinary extension, and the true pure multiplication giving the polynomial lift. For the basis vector \(\mathbf v_i\), lower triangularity and diagonal \(\gamma\) mean that \(A\mathbf v_i\) has earlier zeros and value \(\gamma\) at \(i\). This is exactly (3); the first stage separately gives \(c_1=\gamma,\ g_1=\gamma^2/2\).

Conversely assume the tests. Choose a lift \(\mathbf q_i\in V_{d_i-1}\) of the tested data, and define the single linear matrix \(A\) on the basis by
\[
                     A\mathbf v_i\coloneqq u_i(\mathbf c)+G\mathbf q_i .
\]
Since both the input and output column matrices are lower triangular, with respective diagonals \(1,\gamma\), this \(A\) is lower triangular with common diagonal \(\gamma\). It has \(A\mathbf1=\mathbf c\) from grade zero. At grade one the construction gives \(A\mathbf c-\mathbf c^{\odot2}/2\in G V_0\); its first component and the normalization force the coefficient to be \(1\), so this is the actual quadratic stage residual \(\mathbf g\).

For an arbitrary polynomial \(f\) of weight at most \(j\le p-2\), expand its evaluated vector in the basis columns \(d_i\le j\). The polynomial difference \(r:=f-\sum_i a_i f_i\) vanishes at every pair at grade \(j\), so its trace lies in \(\mathcal O_j\) by the exact trace quotient. Its primitive lies in \(\mathcal O_{j+1}\): pairing with any polynomial of degree at most \(p-2-j\) transfers the primitive to the reverse primitive of degree at most \(p-1-j\). The trace quotient for grade \(j+1\) says the evaluated primitive of \(r(x,0)\) is in \(G V_{j-1}\). More explicitly a relation with that trace differs from its scalar trace by \(z\) times a polynomial of weight at most \(j-1\). Thus the basis construction gives the required primitive congruence for every \(f\), even when a high-grade vector has ambiguous polynomial representatives.

Induct on the rooted-tree recurrence. The trivial tree is represented by \(1\). Rooted sum multiplies the two lift polynomials and their scalar traces. For an extension, the primitive congruence represents the new stage vector by the exact scalar primitive plus \(z\) times a lift of the prescribed smaller grade. Therefore every true tree through order \(p\) has a polynomial lift with its exact tree scalar trace. The weight identity (2) proves all order conditions. No tree enumeration, intermediate solver, or transpose-order assumption is needed for the equivalence.

## The diagonal is determined by the pairs and their ordering

The same test can be written with a separate unknown diagonal \(\delta_i\) at each index. When it is consistent, that \(\delta_i\) is unique. In fact the evaluation at \(i\) on \(V_{d_i-1}\) is already a linear combination of the earlier evaluations; otherwise the pivot \(i\) would occur at an earlier degree. If
\[
        q(c_i,g_i)=\sum_{k<i}\lambda_{ik}q(c_k,g_k)
                           \qquad(\deg_{\rm w}q\le d_i-1),
\]
then the only possible value is
\[
           \delta_i=u_i(c_i)
                     -g_i\sum_{k<i}\lambda_{ik}\frac{u_i(c_k)}{g_k}.
                                                                    \tag{4}
\]
The earlier coordinates in (3) still need to be consistent; numerical equality of (4) with \(\gamma\) does not discharge them by itself. The evaluation in (4) is independent of which representing \(\lambda\) is chosen when those earlier data are consistent. For example \(d_1=0\) gives \(\delta_1=c_1\); if the first two clocks are different their degree-one pivot gives the next conditional equality
\[
         \delta_2(c_2-c_1)=c_2^2/2-c_1c_2+g_2 .
\]
These are concrete mandatory relations between the clock and the quadratic residual, not a free diagonal ansatz.

An equivalent global uniqueness proof is useful: for two consistent lower triangular matrices, their difference \(D\) satisfies \(G^{-1}D V_j\subseteq V_{j-1}\), so \(G^{-1}D\) is nilpotent on full stage space. Being lower triangular, its diagonal vanishes. Once the diagonal tests pass, the solution freedoms are exactly independent choices of the \(\mathbf q_i\) above, modulo their evaluated prefix data. This gives an affine family with dimension \(\sum_i\dim\ker(V_{d_i-1}\to\mathbb K^i)\) for fixed pair data and ordering.

This criterion is sharp for the nowhere-zero branch. The companion zero-branch constraints apply before the first literal zero but do not presume division by zero or common diagonal at a silent row without a physical proof.
