# The odd-order clock-1 exception is attained by actual strict SDIRK tableaux

At odd order \(p=2d+1\), the extra endpoint row cannot be removed in general, even using all the original rooted order conditions. For each \(d\ge1\) there is a strict SDIRK tableau over the real algebraic numbers of exact order \(2d+1\) in which a visible clock-1 vector of degree \(d\) begins exactly \(d\) rows before the last nonzero output. Its earlier prefix realizes every paid positive Beta shift, but no earlier output on that prefix realizes the ordinary rooted order conditions through size \(d+1\).

There is also an exact structural alternative for any strict SDIRK tableau: when the positive shifts are already available at this cutoff but the ordinary output is not, there is precisely one late endpoint model direction and a full independent sequence of late unary directions. The construction below shows that this alternative is nonempty. The [nonendpoint tail theorem](COMMON-DIAGONAL-RESONANCE.md) is one way to obtain the positive-shift hypothesis in other tableaux. Neither result here requires that theorem.

## 1. An exact order-\(2d+1\) starting tableau

Let \(x_1,\ldots,x_d\) be the interior nodes of the right Radau formula on \([0,1]\), and let \(x_{d+1}=1\). For completeness, the interior nodes are the roots of the monic degree-\(d\) polynomial orthogonal to lower degrees for weight \(1-X\). This polynomial exists over the rationals by positive definiteness of the scalar Gram matrix, and its roots are distinct and interior: otherwise multiplying by the monic product of only its interior sign-changing roots would give a polynomial test of degree less than \(d\) and a nonzero integral of one sign. All its nodes are real algebraic. The interpolatory weights \(b_1,\ldots,b_d,\omega\) on these \(d+1\) nodes integrate every polynomial of degree at most \(2d\): divide by the full nodal polynomial and use weighted orthogonality on the quotient. The endpoint weight \(\omega\) is positive because the exact quadrature integrates the square of the endpoint cardinal polynomial (degree \(2d\)).

Write \(L_j\) for the cardinal polynomials of the \(d\) interior nodes alone, so \(\deg L_j\le d-1\), and define
\[
 \widehat A_{ij}\coloneqq\int_0^{x_i}L_j(X)\,dX,\qquad
 q_j\coloneqq\int_0^1L_j(X)\,dX,\qquad
 \lambda_j\coloneqq L_j(1).
\]
The starting tableau uses the \(d\) interior stages of \(\widehat A\), followed by one stage at clock 1 with input row \(\mathbf q\) and zero self-entry. Its output is the Radau row \((b_1,\ldots,b_d,\omega)\). Thus it is block triangular, but the interior block can be fully implicit. Denote the whole array by \(A^\circ\) and its clock diagonal by \(C^\circ\).

Its primitive is exact at every stage for polynomials through degree \(d-1\). Its weighted adjoint is also exact: for any stage vector \(\mathbf v\) and polynomial \(S\) with \(\deg S\le d\),
\[
 \mathbf b^\circ\cdot S(C^\circ)A^\circ\mathbf v
   =\mathbf b^\circ\cdot (\mathcal U S)(C^\circ)\mathbf v,
 \qquad
 (\mathcal U S)(x)\coloneqq\int_x^1 S(X)\,dX.
\tag{1}
\]
Indeed let \(P\) be the interpolation polynomial through the interior entries of \(\mathbf v\). Then \(A^\circ\mathbf v\) evaluates the lower primitive \(JP\) at all nodes. Quadrature integrates \(S JP\) and \((\mathcal U S)P\) exactly, since both degrees are at most \(2d\); these integrals are equal. The endpoint contributes nothing on the right because \((\mathcal U S)(1)=0\), so the stage entry of \(\mathbf v\) there need not match \(P(1)\).

Here is a direct rooted proof of full order, rather than reliance on analytic convergence or a collocation theorem. Let
\[
 P_t(X)\coloneqq \frac{|t|}{t!}X^{|t|-1}
\]
be the exact polynomial of \(\boldsymbol\Phi_t\). The stage derivative vector equals \(P_t(\mathbf c)\) through tree size \(d+1\), by primitive exactness and rooted recursion. More generally, for any \(R\) with \(\deg R+|t|-1\le2d\),
\[
 \mathbf b^\circ\cdot R(C^\circ)\boldsymbol\Phi_t(A^\circ)
     =\int_0^1R(X)P_t(X)\,dX.
\tag{2}
\]
To prove this by induction, consider the children of the root of \(t\). If every child has size at most \(d\), all its primitives are exact and (2) is the scalar quadrature. Otherwise there is only one child \(u\) of size at least \(d+1\), since two such children would already exceed the budget. Let \(H\) be the product of the exact primitives of the other children. The numerical read in (2) is then \(\mathbf b^\circ\cdot(RH)(C^\circ)A^\circ\boldsymbol\Phi_u(A^\circ)\). Its outer polynomial has degree at most \(2d-|u|\le d-1\). Equation (1) transfers the primitive to the outer polynomial; the induction hypothesis applies because \(\deg(\mathcal U(RH))+|u|-1\le2d\). Moving it back inside the formal integral gives (2). In particular the starting tableau has the complete rooted order \(2d+1\).

## 2. A strict common-diagonal terminal replacement that costs exactly \(d+1\) rows

Choose a common nonzero diagonal \(\gamma\) equal to one of the interior nodes. Replace the one explicit endpoint stage by \(d+1\) stage rows all at clock 1. On these rows, indexed \(0,\ldots,d\), let \(N\) be the unit strictly lower adjacent shift and define
\[
 R\coloneqq\gamma I+N,\qquad
 A_{\mathrm{tail,int}}\coloneqq \mathbf1\mathbf q^{\mathsf T}
                               -(R\mathbf1)\boldsymbol\lambda^{\mathsf T}.
\]
The last displayed matrix gives the actual taps into the interior block. Its row sums are \(1-(R\mathbf1)_i\) because \(\mathbf q\cdot\mathbf1=\boldsymbol\lambda\cdot\mathbf1=1\). The total row sum of each tail stage is therefore 1 and its actual diagonal is \(\gamma\).

Keep the interior output weights and define the tail weights by
\[
 w_i\coloneqq\omega(1+\gamma)(-\gamma)^i\quad(0\le i<d),
 \qquad w_d\coloneqq\omega(-\gamma)^d .
\]
The identity \(N^j\mathbf1\) equals the tail indicator beginning at row \(j\), so telescoping gives
\[
 \mathbf w\cdot N^j\mathbf1=\omega(-\gamma)^j\quad(0\le j\le d),
 \qquad
 \mathbf w\cdot R^j\mathbf1=0\quad(1\le j\le d).
\tag{3}
\]
In particular the total tail weight is \(\omega\) and its last weight is nonzero.

Let \(u_t^\circ\) be the starting tableau's endpoint derivative entry and \(\widetilde{\mathbf u}_t\) the new tail derivative vector for tree \(t\). The interior entries \(\mathbf v_t\) have not changed. The exact difference satisfies
\[
 \widetilde{\mathbf u}_t-u_t^\circ\mathbf1
 \ \in\ \operatorname{span}\{R^j\mathbf1:1\le j\le |t|-d-1\}
 \qquad (|t|\le2d+1),
\tag{4}
\]
where an empty span is zero. To see this, the tail primitive of a child vector is
\[
 \mathbf1(\mathbf q\cdot\mathbf v_t)
          +R\bigl(\widetilde{\mathbf u}_t-
                      \mathbf1(\boldsymbol\lambda\cdot\mathbf v_t)\bigr).
\]
For each child of size at most \(d\), its exact stage profile has degree at most \(d-1\), so interpolation gives its true endpoint value, and the term involving \(R\) vanishes. This proves the zero cases of (4) inductively. At a root with one child \(u\) of size at least \(d+1\), all other primitive factors are identical scalar multiples of \(\mathbf1\) on the tail. Thus the new difference is a scalar multiple of
\[
 R\bigl(\widetilde{\mathbf u}_u-u_u^\circ\mathbf1
        +(u_u^\circ-\boldsymbol\lambda\cdot\mathbf v_u)\mathbf1\bigr).
\]
The inductive span for \(u\) advances by one and stays within (4), since \(|u|<|t|\). There cannot be two such children in the paid budget. By (3), the tail output kills all these differences; the retained constant endpoint output is exactly the old weight \(\omega\). Consequently every rooted order equation through \(2d+1\) remains true.

This replacement mechanism does not in itself need a collocation interior: it works for any terminal explicit stage with no backwards effect on predecessors, if an actual predecessor read \(\boldsymbol\lambda\) reproduces its derivative entries for trees through size \(d\). The single-large-child argument then gives (4) verbatim.

## 3. Make the interior literally SDIRK, without introducing another clock

The fully implicit interior block can be realized on all Butcher vectors up to any finite tree size by a finite strict common-diagonal tableau. This is an exact algebraic matching, not an approximation error claim.

Start with one diagonal-only stage at clock \(\gamma\). A first block at the \(d\) interior clocks uses diagonal \(\gamma\) and one tap \(x_i-\gamma\) to that stage from row \(i\). At each further block, row \(i\) uses its own diagonal \(\gamma\) and the preceding block with coefficients \(\widehat A_{ij}-\gamma\,\mathbf1_{i=j}\). These are all earlier rows. Every block has the same actual clock vector, and the first block already agrees on all trees of size at most two. By rooted induction, block number \(r\), counted from zero, agrees with the interior collocation on all trees of size at most \(r+2\). In fact the current and preceding block agree on every child when \(r\ge|t|-2\); their two literal integration contributions then sum to \(\widehat A\) on that child.

Use block \(2d-1\) as the interior bank for the tail taps and for the interior output weights. All earlier weights are zero. The donor bank reproduces exactly the needed interior stage vectors, so the actual tail reproduces (4) by rooted recursion on its own unchanged rows. This gives a literal strict SDIRK tableau, with common diagonal \(\gamma\) and with clocks only among \(x_1,\ldots,x_d,1\). All entries are real algebraic. The width \(2d^2+d+2\) is a nonoptimized witness and is not a table improvement.

The order is exactly \(2d+1\). The polynomial
\[
 (1-X)\prod_{j=1}^d(X-x_j)^2
\]
has degree \(2d+1\), zero numerical quadrature, and strictly positive integral. Hence order \(2d+2\) is impossible for this tableau by its bushy equations.

Let \(t\) be its last nonzero output, which is the last tail row. The only clock-1 stages are the final \(d+1\), and the polynomial
\[
 P_E(X)\coloneqq\prod_{j=1}^d\frac{X-x_j}{1-x_j}
\]
gives their actual indicator \(\boldsymbol\eta=P_E(\mathbf c)\in E_d\). Thus \(\boldsymbol\eta\) is first nonzero at \(t-d\), and \(\mathbf b\cdot\boldsymbol\eta=\omega\ne0\). This is the promised exact attainment of the endpoint loss; it is not just an abstract scalar tail countermodel.

At the earlier prefix through \(t-d-1\), every positive paid Beta shift factors on \(E_d\): its exact output is \(\mathbf b\cdot q_m(C)\boldsymbol v\) for \(q_m(X)=(1-X)^m/m!\), which ignores the entire tail if \(m\ge1\). The ordinary output cannot factor through that prefix because its value on the literal late indicator is \(\omega\).

## 4. Exact late-alias alternative for any odd-order tableau

Now return to any actual order-\(2d+1\) tableau with a nonzero common diagonal on its last \(d+1\) relevant physical rows. Truncate after the last nonzero output \(t\); this preserves the order conditions. Set \(k\coloneqq t-d-1\) and
\[
 K\coloneqq\{\boldsymbol v\in E_d:\ v_i=0\text{ for }i\le k\}.
\]
Use the separated exact model \(\sigma:E_d\to\mathbb K[X]_{\le d}\) at this odd midpoint: if a formal model gives a zero numerical vector, the paid ordinary moments through degree \(d\) separate that polynomial. Suppose all the positive rows \(\mathbf b A^m\), \(1\le m\le d\), vanish on \(K\); this is exactly their factorization through the earlier reads. The assertion is wholly numerical. It may hold without clock invariance, as a consequence of other actual rank information.

For every \(\boldsymbol v\in K\) the moments give
\[
 \int_0^1(1-X)^m\sigma(\boldsymbol v)(X)\,dX=0
       \qquad(1\le m\le d).
\]
Thus \(\sigma(K)\) lies in the line of the degree-\(d\) endpoint reproducer \(R_d^{(1)}\), characterized by
\[
 \int_0^1 R_d^{(1)}(X)P(X)\,dX=P(1)\qquad(\deg P\le d).
\]
Indeed the positive weights are \(1-X\) times the full polynomial space through degree \(d-1\). Their orthogonal line in degree \(d\) is exactly that of the reproducer.

Either the ordinary output vanishes on \(K\) and reconstructs on the early prefix, or choose \(\boldsymbol\eta\in K\) with nonzero output. In the latter case put \(B\coloneqq A-\gamma I\). On the actual terminal suffix \(B\) is strictly triangular. The vanishing positive shifts give
\[
 \mathbf b\cdot B^d\boldsymbol\eta
      =(-\gamma)^d(\mathbf b\cdot\boldsymbol\eta)\ne0 .
\]
This forces the complete adjacent path from \(t-d\) to \(t\), so \(\boldsymbol\eta\) starts at \(t-d\). On this suffix the rows \(\mathbf b B^j\), \(0\le j\le d\), have distinct successive last nonzero coordinates \(t-j\) and span all its coordinate reads. A vector of \(K\) that vanishes also at \(t-d\) has zero \(\mathbf b B^d\) read by chronology, hence zero ordinary read. Its positive reads already vanish, so all \(\mathbf b B^j\) reads vanish. The spanning property makes it zero. Therefore
\[
 K=\mathbb K\,\boldsymbol\eta,\qquad
 E_d\cap\{\boldsymbol v:v_i=0\text{ for }i\le t-d\}=0.
\tag{5}
\]
Its one model line is the genuine endpoint reproducer, and no pure direction is lost by early restriction. Furthermore \(B^j\boldsymbol\eta\), \(1\le j\le d\), have successive leading physical positions after \(t-d\), so they form an independent sequence modulo \(E_d\) by (5). They are actual vectors of \(E_{d+j}\). In particular the failure of the early ordinary read forces at least \(j\) genuine later rooted directions by grade \(d+j\), not merely an apparent loss of a scalar moment.

If the actual late kernel \(K\) is \(C\)-invariant, the uniform nonendpoint tail theorem of 801a9698… (pending independent audit) provides the positive-factorization hypothesis when \(d\ge6\): every nonendpoint local component in \(K\) is too late, and the endpoint components are killed by positive weights. In the nontrivial alternative (5), the line is then literally supported at clock 1, so \(c_{t-d}=1\). Without that invariant hypothesis, (5) needs only the positive factors; it does not assert literal support, only the effective endpoint model. The counterfamily satisfies the factors unconditionally and therefore witnesses this very one-dimensional alternative.

The ordinary output through size \(d\) always can be repaired by positive shifts alone under the factorization hypothesis. Write \(\Pi_d\) for the monic degree-\(d\) ordinary orthogonal polynomial on \([0,1]\) and define
\[
 q(X)\coloneqq1-\frac{\Pi_d(X)}{\Pi_d(1)}.
\]
The denominator is nonzero by the paid shifted Hilbert pairing: a zero at 1 would put the quotient by \(X-1\) in the kernel for weight \(1-X\). Then \(q(1)=0\), so \(q\) is a combination of the positive Beta weights. It reproduces the ordinary moments of all degrees at most \(d-1\) by orthogonality. It cannot, and no other degree-at-most-\(d\) density vanishing at 1 can, reproduce all degree-\(d\) ordinary moments: the ordinary paid Hilbert pairing would force the density to equal 1. The missing direction is exactly the one represented in (5).

The structural argument holds over all paid fields. The explicit counterfamily lies over the real algebraic numbers and uses signed tail weights, as allowed in ordinary RK existence. No stronger unrestricted numerical lower bound, Lean certificate, or claim for lower widths is inferred.
