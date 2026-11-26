# Multiple polynomial clock profiles force genuine pure leakage
\nThroughout the Runge–Kutta arguments in this note, the stage matrix is strictly lower triangular.

Use separated rooted data over a paid field, with actual \(E_j,F_j\) through tree degree \(j\). The actual clock operator is \(C=\operatorname{diag}(\mathbf c)\), and unary extension applies \(A\) numerically and the primitive \(J\) from zero on the exact model. A sufficient field hypothesis below is that the factorial through \(R+1\) is a unit when the last degree used is \(R\).

The first statement is a rank version of the chronological Gram exit. It does not assume one head, a flat interval, or that the pure directions not in a measured chart are supported on only a few clocks.

## A model-visible mask charges actual missing pure directions

Let \(U\subseteq F_a\) (\(a+1\le R\)) be invariant under \(C\) and a finite collection of specified numerical diagonal multipliers. On each physical joint block where all these diagonals, including \(C\), take fixed values, choose a chronological complement to its part of \(U\). Let \(W\subseteq F_R\) be any measured head span in this complement, and assume \(U+W\subseteq F_R\). Suppose there is a genuine column \(\mathbf z\in E_e\) with nonzero exact polynomial model \(P\), with the following two numerical properties:
1. \(\mathbf z\) is constant on each of these joint blocks.
2. At every coordinate where any vector of \(W\) is nonzero, the value of \(\mathbf z\) is zero.

Then the measured rank outside the chart satisfies
\[
                 \dim\bigl(F_R/(U+W)\bigr)
                         \ \ge\ (\lfloor R/2\rfloor-e)_+ .        \tag{1}
\]

Here is the proof. Projection onto the chosen complement is chronological: at every nonpivot row \(i\) it subtracts the unique matching combination of earlier physical pivot evaluations in the same joint block. Its row \(\boldsymbol\lambda_i\) kills \(U\), is supported through \(i\), and is supported at just one physical clock. At any first mismatch of a nonzero clock-polynomial mask of \(\mathbf z\), its row sum is nonzero, because the masked numerical values are constant on that joint block. The original \(\mathbf z\) has nonzero value on that block, so the row also kills \(W\).

Build successive actual exit rows in increasing physical order. If the former exits have distinct nonzero clocks \(x_1,\ldots,x_{t-1}\), set
\[
                       Q_t(X)\coloneqq X\prod_{j<t}(X-x_j).
\]
If \(e+t\le R\), the column \(Q_t(C)\mathbf z\) has nonzero formal model \(Q_tP\), so by separation it is not in \(U\). Take its first actual mismatch from \(U\) using the same projections. Because successive masks only remove additional clock fibres, the new physical index is strictly later and its nonzero clock \(x_t\) is distinct from all previous ones. Its row \(\boldsymbol\lambda_t\) kills \(U+W\), has \(\boldsymbol\lambda_t\cdot\mathbf1\ne0\), and there is \(\mathbf u\in U\) agreeing with \(Q_t(C)\mathbf z\) through the preceding row. All these are statements about numerical coordinates.

To prove independence of the first \(t\) exit rows on the quotient \(F_R/(U+W)\), suppose there is a nontrivial relation and let \(j\le t\) be the last index with nonzero coefficient. This combination \(\boldsymbol\lambda\) annihilates \(F_R\) and is supported through the \(j\)-th physical exit. For any polynomial \(V\) such that the following primitive is paid, strict chronology gives
\[
                 \boldsymbol\lambda A V(C) Q_j(C)\cdot\mathbf z=0.
\]
Indeed replace \(Q_j(C)\mathbf z\) on all earlier coordinates by its matching \(\mathbf u\in U\); then \(V(C)\mathbf u\in U\) and \(A V(C)\mathbf u\in F_{a+1}\subseteq F_R\), which the combination annihilates. But the exact model of the same actual primitive is \(J(V Q_j P)\). Its pure difference belongs to \(F_R\). The row \(\boldsymbol\lambda\) therefore equates a nontrivial linear combination of the scalar values \(J(VQ_jP)(x_\ell)\), with respective factors \(\boldsymbol\lambda_\ell\cdot\mathbf1\), to zero.

Those values can be chosen independently with \(\deg V\le e+j-1\). Put \(L(X)=Q_j(X)P(X)\), and in a splitting field prescribe a primitive \(G\) with \(G(0)=0\), arbitrary values at \(x_1,\ldots,x_j\), and derivative divisible by \(L\). To see the exact degree bound, at each root of \(L\) having multiplicity \(m\), prescribe the first \(m\) derivatives of \(G\) to vanish. The value at each root that is not an already prescribed node may arbitrarily be set zero. Those additional roots are all roots of \(P\), because every root of \(Q_j\) is among the anchored nodes. There are at most \(\deg P\le e\) of them. Confluent polynomial interpolation gives degree at most \(\deg L+j+\deg P\). Hence \(V=G'/L\) has degree at most \(j+\deg P-1\le j+e-1\). Solvability of this linear system over the splitting field implies solvability over the original field, since the requirements on \(V\) have coefficients there. The total rooted cost \(e+j+\deg V+1\) is at most \(2(e+j)\). All factorials and derivatives are paid. Taking value one at the last exit and zero at its predecessors contradicts the nonzero last coefficient of the relation. This proves (1) by taking \(t=\lfloor R/2\rfloor-e\) when positive.

## Applying the rank exit to several diagonal clock heads

Let \(\mathbf f\in F_b\) be a genuine pure vector, and let \(D_{\mathbf f}=\operatorname{diag}(\mathbf f)\). Suppose \(U\subset F_a\) is invariant under \(C,D_{\mathbf f}\), and there are \(r\) actual heads \(\mathbf w_1,\ldots,\mathbf w_r\) with positive integer heights \(k_1,\ldots,k_r\). These heights describe initial powers of each head already available at grade \(a\); they are not a dimension count guessed from a flag. Suppose the measured numerical relations include
\[
        D_{\mathbf f}\mathbf w_j
            \ \equiv\ \sum_{i=1}^r (P_{\mathbf f})_{ij}(C)\mathbf w_i
                   \pmod U,\qquad
        \deg(P_{\mathbf f})_{ij}\le b+k_i-k_j .                 \tag{2}
\]
A negative degree bound means that entry is zero. Let \(W\) be a measured span of pure clock-polynomial combinations of these heads in the common joint complement, contained in \(F_R\).

Here is a sufficient **actual rank check** for the degree bound in (2). Suppose \(C^t\mathbf w_j\in F_a\) for \(0\le t<k_j\), and for this \(\mathbf f\) all its products with these old head powers lie in
\[
          U+\sum_i\mathbf w_i P_{\le k_i+b-1}(C).
\]
Suppose also the next-cap polynomial columns through degree \(k_i+b\) on each corresponding head are independent modulo \(U\). Initially \(\deg (P_{\mathbf f})_{ij}\le k_i+b-1\) by the measured product chart. Compare \(X(P_{\mathbf f})_{ij}\) with the representation of \(D_{\mathbf f}C\mathbf w_j\); independence at the one higher cap removes its highest possible coefficient. Repeating with each old power of the input head always needs only that same one-higher cap, because each preceding comparison lowered the degree bound. At the \((k_j-1)\)-st power it gives exactly \(b+k_i-k_j\). If there are extra pure directions in \(F_{a+b}\), containment of the products in the displayed chart is a hypothesis to be tested, not inferred from a formal degree bound. For example, if the full clock closure \(T\) of \(F_a\) satisfies \(F_{a+b}\cap T\) equal to that chart, requiring just the \(r\) products \(D_{\mathbf f}\mathbf w_j\) to lie in \(T\) makes all other old powers land there too by commutation with \(C\); this costs at most \(r\dim(F_{a+b}/(F_{a+b}\cap T))\) linear conditions on a subspace of candidate \(\mathbf f\).

Project the heads to the common complement; (2) then holds exactly on the projected heads because the projection commutes with both \(C,D_{\mathbf f}\). At a physical row \(i\) occupied by a projected head, let \(\boldsymbol\omega_i\) be the nonzero row of its \(r\) head values. The actual equation is
\[
                       \boldsymbol\omega_i P_{\mathbf f}(c_i)
                                    = f_i\boldsymbol\omega_i .
\]
Thus \(f_i\) is a left eigenvalue of that clock matrix. Define
\[
 Q_{\mathbf f}(X,T)\coloneqq\det(TI-P_{\mathbf f}(X)),\qquad
 \mathbf z_{\mathbf f}\coloneqq Q_{\mathbf f}(C,D_{\mathbf f})\mathbf1 .
\]
The coefficient of \(T^v\) in this polynomial is a sum of principal minors of size \(r-v\). In each product term their shifted degree contributions \(k_i-k_j\) cancel around the permutation, so its degree in \(X\) is at most \((r-v)b\). Multiplying that coefficient vector by \(\mathbf f^{\odot v}\) costs at most \(rb\) total. Consequently \(\mathbf z_{\mathbf f}\in E_{rb}\), its exact model is \(Q_{\mathbf f}(X,0)=\det(-P_{\mathbf f}(X))\) because \(\mathbf f\) is pure, and it vanishes on every projected head support by the left eigenvector equation. Its physical values are constant on the required joint blocks. If the determinant is not identically zero, (1) gives
\[
         \dim F_R/(U+W)\ge (\lfloor R/2\rfloor-rb)_+ .            \tag{3}
\]
This conclusion measures actual pure rank outside the chart. In particular a nonconstant diagonal clock profile cannot be used to infer a scalar eigenvalue model on each head; the polynomial matrix and its determinant require the physical checks above.

## When a whole family shares a genuine null direction

One can obtain a second conditional conclusion from (3) for a linear subspace \(\mathcal L\subseteq F_b\). Suppose a single core \(U\) is invariant under all its \(D_{\mathbf f}\), the measured profile matrix \(P_{\mathbf f}\) in (2) depends linearly on \(\mathbf f\), and the polynomial matrices commute. A sufficient physical check of the last condition is independence modulo \(U\) of the head polynomials through degrees \(k_i+2b-1\): the commutator entries have degree at most \(2b+k_i-k_j\le k_i+2b-1\), and the genuine diagonals commute on the actual heads. Thus their evaluated commutator columns vanish modulo \(U\), and the checked independence makes the polynomial commutator zero.

If \(\dim F_R/(U+W)<\lfloor R/2\rfloor-rb\), (3) forces \(\det P_{\mathbf f}=0\) for every \(\mathbf f\in\mathcal L\). Assume the coefficient field has more than \(r\) elements (automatic when the nontrivial paid budget here exceeds \(r\)). Since the determinant is polynomial of degree \(r\) in the coordinates of \(\mathbf f\), it is the zero polynomial on that linear family. Over an algebraic closure of \(K(X)\), the commuting matrices can be simultaneously triangularized. The determinant is the product of their joint diagonal characters, so one character is identically zero. For clarity, choose a linear combination separating the finitely many distinct characters; its generalized zero eigenspace is nonzero and stable under the whole family. Each member is nilpotent there. Commuting nilpotents have a common nonzero kernel, found by successively restricting to each invariant kernel. Thus all the matrices have a common nonzero kernel over the extension, and hence over \(K(X)\) by rank of their stacked linear equations.

Clearing denominators gives a nonzero polynomial kernel column \((p_i(X))\). A numerical common-null head
\[
                         \mathbf w_*=\sum_i p_i(C)\mathbf w_i
\]
is then earned only if the physical head columns are independent at the actual degrees of these \(p_i\), and the used head powers are in the claimed rooted cap. These are finite measurable conditions. For instance a polynomial kernel column can be obtained by cofactors of a full-rank minor of the stacked equations with one extra column. If the row heights in that minor are \(k_{i_1},\ldots,k_{i_t}\) and the selected column set is \(J\) of size \(t+1\), the cofactor for \(j\in J\) has degree at most
\[
                         t b+\sum_{\ell=1}^t k_{i_\ell}
                                    -\sum_{i\in J\setminus\{j\}} k_i.
\]
This gives an explicit sufficient numerical cap to check, rather than claiming that formal polynomial independence persists under evaluation at the actual clocks. After a common invariant projection commuting with all the diagonals, the nonzero actual head \(\mathbf w_*\) has zero coordinatewise product with every \(\mathbf f\in\mathcal L\). Thus the measured alternatives are genuine pure rank beyond the chart, or a genuine common-null direction under the independently checked polynomial cap. Stages on the latter direction then have no residual from \(\mathcal L\), with any unmeasured pure directions charged by the physical provider inequality of the companion note. This is not by itself an unconditional stage bound.
