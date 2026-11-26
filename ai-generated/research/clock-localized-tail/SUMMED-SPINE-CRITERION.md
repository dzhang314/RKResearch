# One exact test for simultaneous paired corrections

This note uses the concrete shifted contrast architecture of the paired-layer compression, but does not require each virtual layer to be recovered separately. The statements apply both to ERK (\(\gamma=0\)) and to nonzero prescribed common diagonal \(\gamma\). They concern all ordinary rooted equations, not just linear stability. They are not unrestricted stage lower bounds.

## Actual recurrence

Work over a characteristic-zero field. Fix a target order \(p=m+r\), with \(m\ge2\) and \(1\le r\le m\). Keep the old prefix decoder \(D\) through derivative grade \(m-1\) and the actual base owner rows from the paired-layer construction. Use its notation \(M=E J_\gamma R\) for the dense shifted reference, \(C=\operatorname{diag}(\mathbf x)\) for owner clocks, and \(\widehat{\mathbf b}\) for the owner quadrature. Write \(\mathbf V_{-1}(t)\) for the prefix-decoded owner vector and \(\mathbf V_0(t)\) for the actual base vector. Define
\[
 \boldsymbol\Delta_0(t)\coloneqq\mathbf V_0(t)-\mathbf V_{-1}(t),\qquad
 \mathbf Z(t)\coloneqq\boldsymbol\Phi_t(M)-\mathbf V_0(t).
\]
The reference is correct on weighted shifted order through \(p\). The base matches it through \(m\) and the prefix decoder through \(m-1\). Thus \(\mathbf Z\) is zero through size \(m\) and \(\boldsymbol\Delta_0\) through size \(m-1\).

Choose \(a\) physical plus stages in chronological order. Each copies the entire strict feed of an older minus row at the same clock and adds a source read from \(\boldsymbol\Delta_0\) and a linear combination of earlier contrasts. All older minus rows precede these new plus rows. Their shifted primitive must agree with the exact profile for children of size at most \(r-1\); in particular the base owner rows qualify. The minus row need not be an owner. Write \(\Xi\) for the diagonal of plus clocks, \(S\) for the source-tap matrix, \(T\) for the strictly lower-triangular matrix of contrasts feeding earlier plus-minus differences into later ones, and \(\mathbf w\) for the plus weights. Subtract the matching weight from the old minus row. Source and contrast feeds have zero row sums because their leaf columns are zero. Thus these are literal strict rows with the stated clocks, and the common diagonal is preserved. The actual correction to the shifted output is \(\mathbf w\cdot\boldsymbol\delta(t)\), where \(\boldsymbol\delta(t)\) is the vector of plus-minus differences.

In a paid tree, there is at most one child of size at least \(m\), since \(p\le2m\). If there is none, both \(\boldsymbol\delta(t)\) and \(\mathbf Z(t)\) vanish. Otherwise let \(u\) be that child and \(P\) the product of the other shifted exact primitive profiles at the root. These other child sizes sum to at most \(r-1\); they agree on the two compared rows. The exact recurrences are
\[
 \boldsymbol\delta(t)=P(\Xi)\bigl(S\boldsymbol\Delta_0(u)+T\boldsymbol\delta(u)\bigr),\qquad
 \mathbf Z(t)=P(C)M\bigl(\boldsymbol\Delta_0(u)+\mathbf Z(u)\bigr).       \tag{1}
\]
There are no dropped product terms. The target for the new scalar output is \(\widehat{\mathbf b}\cdot\mathbf Z(t)\). Matching it for all shifted paid trees is equivalent to ordinary order, by contracting the identity choices in every \(A=B+\gamma I\) expansion, and also using the inverse expansion.

## Exact simultaneous equations

Follow the unique size-at-least-\(m\) child repeatedly from a paid tree \(t\). Let its successive descendants be \(u_1,\ldots,u_d\), and let \(P_1,\ldots,P_d\) be the corresponding products of the other primitive children, in root-to-tip order. Write
\[
 \begin{split}
 \mathbf v_j(t)&\coloneqq P_j(\Xi)T^{\mathsf T}P_{j-1}(\Xi)\cdots T^{\mathsf T}P_1(\Xi)\mathbf w,\\
 \mathcal T(t)&\coloneqq\sum_{j=1}^d\mathbf v_j(t)\,\boldsymbol\Delta_0(u_j)^{\mathsf T},\\
 z(t)&\coloneqq\sum_{j=1}^d\widehat{\mathbf b}^{\mathsf T}P_1(C)M\cdots P_j(C)M\boldsymbol\Delta_0(u_j).
 \end{split}                                                            \tag{2}
\]
For \(j=1\) the first line is \(P_1(\Xi)\mathbf w\). The number of decorations plus transitions is bounded: \(j+\sum_{i=1}^j\deg P_i+|u_j|\le |t|\). The sole exact equation for \(t\) is
\[
                       \langle S,\mathcal T(t)\rangle=z(t),               \tag{3}
\]
where the bracket is the entrywise matrix pairing. Indeed (2) expands (1) one active-child step at a time. In particular, once \(T,\Xi,\mathbf w\) and the physical minus choices are fixed, there is an admissible \(S\) if and only if every linear relation among the tensors \(\mathcal T(t)\) annihilates the corresponding target scalars \(z(t)\). If the source read is limited to particular old measurements of \(\boldsymbol\Delta_0\), replace that column everywhere in the physical tensors by their actual measured vector; the target is unchanged. Restrictions to a linear space of allowed entries of \(S\) similarly replace the physical tensors by their restrictions as linear functionals. This is a finite linear test; both necessity and sufficiency use the actual tree combinations.

In contrast, requiring every depth contribution in (2), or every independently varied marked word, to equal its target is a sufficient larger system. A formal way to see the difference is to place the summands of (2) at distinct coordinates of a direct sum indexed by depth and by monomials in the decorations. The actual paid span is generated by the **sum for each complete tree**, not by each of its coordinate pieces. The pieces need not belong to that span. The next examples show that this distinction concerns genuine rooted data, not merely abstract tensor ranks.

### A parallel tail as a degenerate case

If \(T=0\), there is a still simpler exact criterion. Put \(\boldsymbol\rho(u)\coloneqq\boldsymbol\Delta_0(u)+\mathbf Z(u)\). For any source \(u\) of size at most \(p-1\), simultaneous matching is equivalent to
\[
 \mathbf w^{\mathsf T}f(\Xi)S\boldsymbol\Delta_0(u)
       =\widehat{\mathbf b}^{\mathsf T}f(C)M\boldsymbol\rho(u)
                       \qquad(\deg f\le p-1-|u|).                       \tag{4}
\]
Sufficiency follows from the first step of (1). For necessity, take a root whose children are \(u\) and \(j\) additional leaves. This pays the tests \((X-\gamma)^j\) at every allowed exponent, and these span the indicated polynomials. Sources below size \(m\) give zero. Thus (4) pairs the **compensated** residual \(\boldsymbol\rho\) against the observed \(\boldsymbol\Delta_0\); it does not simply throw away the higher virtual increments. The same argument applies to other paired ERK tails whenever their exact single-active-child recursion is additive in a fixed old measurement and earlier contrast, with the corresponding sources inserted in (2). It does not by itself merge any rows of the existing fixed ERK upper tableaux.

## Two orders beyond the donor grade: exact geometry and failure of separated necessity

Let \(r=2\). Define the actual target rows on owner vectors by
\[
 L_0\coloneqq\widehat{\mathbf b}^{\mathsf T}M,\qquad
 L_x\coloneqq\widehat{\mathbf b}^{\mathsf T}CM,\qquad
 L_2\coloneqq\widehat{\mathbf b}^{\mathsf T}M^2.
\]
On every size-\(m\) source, the paid weighted adjoint identity gives
\[
                 L_2\boldsymbol\Delta_0(u)
                =((1-\gamma)L_0-L_x)\boldsymbol\Delta_0(u).             \tag{5}
\]
Indeed \(J_\gamma^*1=1-X-\gamma\); the source after one primitive is represented by a polynomial of degree at most \(m\), so the adjoint is inside the paid degree \(m+1=p-1\).

Suppose there are two distinct eligible minus clocks \(x_1,x_2\), use unit plus weights, and write \(\tau\) for the single possible feedback tap (from row 1 to row 2). Let \(U\) be the span of \(\boldsymbol\Delta_0(u)\) for all \(|u|=m\), and let \(V\) be its sum with the span of \(\boldsymbol\Delta_0(v)\) for nonunary \(|v|=m+1\). The first source tap is forced on \(U\) to be
\[
                  R_1\coloneqq\frac{x_2 L_0-L_x}{x_2-x_1}\bigg|_U .       \tag{6}
\]
The unary defect is the only remaining freedom to trade between the two grades. On the formal span of size-\(m\) trees, let
\[
 F(u)\coloneqq \boldsymbol\Delta_0([u])+V,\qquad
 d_\tau(u)\coloneqq (L_2-\tau R_1)\boldsymbol\Delta_0(u).
\]
The two-row architecture is exact if and only if \(\ker F\subseteq\ker d_\tau\). To prove this, let \(E_0\) be the sum of the two source taps minus \(L_0\). Unaries at size \(m+1\), and a root at size \(m+2\) with one extra leaf, give \(E_0|_U=0\) and (6). Outer unary roots above the nonunary size-\(m+1\) cases give \(E_0|_V=0\). Finally the doubly unary cases give \(E_0\boldsymbol\Delta_0([u])=d_\tau(u)\), so exactly the asserted quotient interpolation. Conversely choose any extension of \(R_1\) to the first source row and set the second to \(L_0+E_0\) minus the first; these satisfy all paid cases. No additional marked-spine type is possible at this budget.

There is a simple universal geometry: take \(x_2=1-\gamma\), \(\tau=x_2-x_1\), and \(E_0=0\). Equation (5) makes \(d_\tau=0\), and two physical stages replace the former two-plus-one count for all genuine grade-\((m-1)\) donors. An ERK uses the old endpoint 1; a strict method can use that shifted endpoint as a base clock, or use its first clock when \(\gamma=1/2\). No one-mode or extra grade of donor is assumed. Conversely if \(F=0\) and \(L_0,L_x\) are independent on \(U\), this two-row geometry is forced: comparing coefficients in (5) and (6) gives \(\tau=x_2-x_1\) and \(x_2=1-\gamma\). The unrestricted paid system can escape this barrier precisely through the actual quotient \(F\), not by dropping a needed adjoint identity.

### Two exact small canaries of real cross-grade cancellation

Take \(m=2,p=4\). The donor has two physical rows at diagonal \(\gamma\), with one strict lower coefficient 1; its decoder is the second coordinate as a constant polynomial (this pays grade one). Put \(Z=X-\gamma\). With three distinct owners, the size-two source is the evaluated \(Z-1\), the size-three bush source is the evaluated \(Z^2-1\), and the size-three unary source from the size-two tree is the evaluated \(Z\). Thus the last column is independent modulo the first two polynomial directions. For the size-two source, the three scalar reads are as follows:

| diagonal | \(L_0\) | \(L_x\) | \(L_2\) | exact owner sites |
|---:|---:|---:|---:|:---|
| \(0\) | \(-1/3\) | \(-5/24\) | \(-1/8\) | \(0,5/8,2\) |
| \(1\) | \(2/3\) | \(1/8\) | \(-1/8\) | \(0,3/16,18/23\) |

These reads follow by integrating \(J_\gamma(Z-1)=X^2/2-(2\gamma+1)X+\gamma(\gamma+1)\), then multiplying by \(X\) and using (5). At each displayed grid the monic nodal polynomial has integral zero, and its product with \(X\) has integral \(-19/480\), respectively \(47/7360\). The corresponding scalar rules therefore pay precision three exactly. A **single** plus stage at the clock \(\xi=L_x/L_0\) in its grid suffices. Give its source tap \(L_0+E_0\), where \(E_0\) kills the first two columns and takes value \(-1/8\) on the size-three unary source; this exists by the independence above. The one-row variant of the same grade checks proves literal order four and the unpaid bush proves exactness. The depth-two target is nonzero, so this one-row result is impossible if the two virtual corrections must be matched separately. These are checks of the gap between the two equations, not competitive order-four counts.
