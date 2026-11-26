# Several dense SDIRK layers can be replaced by paired scalar reads

This is a construction of literal tableaux. It does not need equality of the penultimate owner vectors. Each new row is compared with the same older row at its clock, and only weighted polynomial moments of the differences are recovered. The negative reference is reused across all successive layers. No extra stage is needed for it, and no row is identified merely because two clocks agree.

## Construction theorem

Work over a characteristic-zero field \(K\). Fix a nonzero diagonal \(\gamma\), a target \(p\), and integers
\[
 2\le m\le p,\qquad 2m\ge p,\qquad
 m-1\le q\le p,\qquad 2q\ge p,\qquad r\coloneqq p-m.
\]
Suppose there are \(q\) distinct sites \(\mathbf x=(x_1,\ldots,x_q)\) with weights \(\widehat{\mathbf b}\) integrating every polynomial through degree \(p-1\) on \([0,1]\). Suppose also that a strict SDIRK prefix with \(s_F\) stages at diagonal \(\gamma\) has a linear polynomial decoder \(D\) through derivative grade \(m-1\): it maps the Butcher weight vector of every tree of size at most \(m-1\) to its exact-flow polynomial \(|t|X^{|t|-1}/t!\), and its codomain is the polynomials of degree at most \(m-2\). Then a literal strict SDIRK tableau at the same diagonal has order at least \(p\) and uses at most
\[
                   s_F+q+\frac{r(r+1)}2                         \tag{1}
\]
stages. It uses the prefix unchanged, one base row at each of the \(q\) sites, and \(r,r-1,\ldots,1\) further rows. Its aggregate output masses by clock are exactly the given scalar rule. If that rule misses the degree-\(p\) moment, the tableau has exact order \(p\) for every such \(\gamma\).

Write \(\ell P\coloneqq\int_0^1P(X)\,dX\). The lower and upper shifted primitives, both operations on polynomial coefficients, are
\[
 (J_\gamma P)(X)\coloneqq\int_0^X P(U)\,dU-\gamma P(X),\qquad
 (J_\gamma^*P)(X)\coloneqq\int_X^1 P(U)\,dU-\gamma P(X).
\]
The identity \(\ell(fJ_\gamma g)=\ell((J_\gamma^* f)g)\) follows by integrating the derivative of the product of lower primitives. For a tableau with common diagonal, its shifted strict part is \(B\coloneqq A-\gamma I\). Define the exact shifted tree profiles by
\[
 G_\bullet\coloneqq 1,\qquad
 G_{[t_1]\#\cdots\#[t_a]}\coloneqq \prod_{j=1}^a J_\gamma G_{t_j}.
\]
The degree is at most \(|t|-1\). Expanding each edge with \(A=B+\gamma I\) contracts the identity edges and gives smaller rooted trees with appropriate factors of \(\gamma\). The same expansion holds for the exact shifted primitive and the ordinary lower primitive. Thus the prefix decoder maps \(\boldsymbol{\Phi}_t(B_F)\) to \(G_t\) through size \(m-1\), and agreement of the final shifted scalar on every paid tree suffices for the ordinary RKOC. This uses both signs of the expansion, not equality of individual unshifted stage coordinates.

### The dense reference needs only a scalar quadrature rule

Let \(E\) evaluate a polynomial at the \(q\) owner sites, and let \(R\) interpolate an owner vector by a polynomial of degree less than \(q\). The clock diagonal is \(C\coloneqq\operatorname{diag}(\mathbf x)\). Define the dense *shifted* reference operator by
\[
                         M\coloneqq E J_\gamma R.
\]
It is not used as a literal diagonal block. On any vector \(\mathbf v\) with \(\deg(R\mathbf v)\le n-1\), the adjoint equality
\[
 \widehat{\mathbf b}\cdot\bigl(f(\mathbf x)\odot M\mathbf v\bigr)
 =\widehat{\mathbf b}\cdot\bigl((J_\gamma^* f)(\mathbf x)\odot\mathbf v\bigr)
 \qquad (\deg f+n\le p-1)                                     \tag{2}
\]
holds: the integrands on both sides have degree at most \(p-1\). It need not hold on arbitrary owner vectors outside this degree condition.

For each tree \(t\), the polynomial \(R\boldsymbol{\Phi}_t(M)\) has degree at most \(|t|-1\), since interpolation is a remainder by the monic node polynomial. Through size \(q\), the vector itself is \(EG_t\), by induction on the children. The following more general weighted equality is valid through the whole paid range:
\[
 \widehat{\mathbf b}\cdot\bigl(f(\mathbf x)\odot\boldsymbol{\Phi}_t(M)\bigr)
                  =\ell(fG_t)\qquad (\deg f+|t|\le p).          \tag{3}
\]
If every child has size at most \(q\), all of its shifted primitives at the receiving sites are exact and (3) is scalar quadrature. Otherwise there is just one larger child \(u\), because \(p\le2q\). The product \(P\) of the other exact primitive factors has degree at most \(|t|-1-|u|\). Equation (2) with \(fP\) moves the remaining primitive to the weight; induction applies to \(u\) and \(J_\gamma^*(fP)\). Thus neither a collocation-order citation nor a preservation test for each full owner vector is needed to obtain the dense reference scalar.

### Virtual differences and the single active child

For all trees, define \(\mathbf V_{-1}(t)\coloneqq E D\boldsymbol{\Phi}_t(B_F)\). For \(i\ge0\), define the virtual owner layer by
\[
 \mathbf V_i(\bullet)\coloneqq\mathbf1,\qquad
 \mathbf V_i([t_1]\#\cdots\#[t_a])\coloneqq
               \mathop{\bigodot}_{j=1}^a M\mathbf V_{i-1}(t_j),
 \qquad \boldsymbol\Delta_i(t)\coloneqq\mathbf V_i(t)-\mathbf V_{i-1}(t).
\]
Each \(R\mathbf V_i(t)\) has degree at most \(|t|-1\), starting from the decoder cap. The prefix decoder and the small-tree part of (3) give agreement of \(\mathbf V_{-1}(t)\) with \(\boldsymbol\Phi_t(M)\) through size \(m-1\). Consequently \(\mathbf V_i(t)\) agrees with that dense column through size \(m+i\). In particular \(\mathbf V_r\) is correct through \(p\), and \(\boldsymbol\Delta_i(t)=0\) through size \(m+i-1\).

Fix \(i\ge1\) and a paid tree. A child can have nonzero \(\boldsymbol\Delta_{i-1}\) only if its size is at least \(m+i-1\). At most one child reaches this size, since \(p\le2m\). If none does, \(\boldsymbol\Delta_i(t)=0\). Otherwise let \(u\) be the unique such child. All other children have total size at most \(r-i\le m-1\), so their primitive factors in both compared layers are the exact shifted polynomials. Let \(P\) be their product. The full virtual difference is
\[
                  \boldsymbol\Delta_i(t)
                   =P(\mathbf x)\odot M\boldsymbol\Delta_{i-1}(u).
                                                                    \tag{4}
\]
This is an exact product identity on the paid band, not a first-order approximation. It is precisely what allows the physically realized rows to match pairings instead of reproducing \(\boldsymbol\Delta_i\) coordinates.

### Literal rows: one new stage rather than a pair

For a scalar \(x\), write \(E_xP\coloneqq P(x)\). First give \(\mathbf V_0\) actual rows at all \(q\) owner sites. A row at \(x\) has strict feed \((E_xJ_\gamma)D\) from the prefix and diagonal \(\gamma\). Its strict row sum is \(x-\gamma\), since \(D\mathbf1=1\). Its shifted rooted weights are precisely \(\mathbf V_0\) because \(R E D=D\).

For each \(1\le i\le r\), choose any \(r-i+1\) distinct owner sites \(S_i\), and let \(L_{i,a}\) be their cardinal polynomials. Write \(\boldsymbol\delta_0(t)\coloneqq\boldsymbol\Delta_0(t)\); it is a literal linear combination of the already numerical prefix and base owner data. For \(i\ge1\), add one **plus** row at each \(a\in S_i\). Its entire strict feed is the same as the older base row at \(a\), with the additional earlier-row read \(K_i(a)\boldsymbol\delta_{i-1}\). Here \(\boldsymbol\delta_i\) denotes the stage weights of the new plus rows minus those of the corresponding **unchanged** base rows. Define the tap matrices by
\[
 (K_1)_{a,j}\coloneqq\widehat b_j(J_\gamma^*L_{1,a})(x_j),\qquad
 (K_i)_{a,d}\coloneqq(J_\gamma^*L_{i,a})(d)\quad(i>1,\ d\in S_{i-1}).
                                                                    \tag{5}
\]
All corrections are read only from earlier data. Their row sums are zero: \(\boldsymbol\delta_{i-1}(\bullet)=0\). Thus the actual clock of every new row is \(a\), and adding \(\gamma\) on each diagonal makes a literal lower-triangular strict SDIRK tableau. There is no same-layer dependency, and the reuse of the negative reference is an actual reuse of the old coordinate and its incoming row.

The physical difference \(\boldsymbol\delta_i(t)\) is zero through size \(m+i-1\), by induction from the earlier-row formula. For the unique child \(u\) in (4), the small-child factors of the base row and the plus row agree and equal \(P(a)\): the small children fit the prefix decoder and every contrast term on them is zero. Therefore
\[
                  \delta_{i,a}(t)=P(a)K_i(a)\boldsymbol\delta_{i-1}(u).
                                                                    \tag{6}
\]
No exact stage interpretation is assigned to the plus row on the large child.

### Exact paired recovery and ordinary order

For every paid \(t\) and polynomial \(f\) with \(\deg f+|t|\le p\),
\[
 \sum_{a\in S_i}f(a)\delta_{i,a}(t)
       =\widehat{\mathbf b}\cdot\bigl(f(\mathbf x)\odot\boldsymbol\Delta_i(t)\bigr).
                                                                    \tag{7}
\]
When there is no large child both sides are zero. Otherwise put \(g\coloneqq fP\). The degree bound in (4) gives \(\deg g\le p-1-|u|\le r-i\). Hence \(g=\sum_{a\in S_i}g(a)L_{i,a}\). The left side of (7) is therefore the read against \(J_\gamma^*g\) on the preceding physical contrast, by (5) and (6). For \(i=1\) this is directly the weighted owner read on \(\boldsymbol\Delta_0(u)\). For \(i>1\) it is the same read on \(\boldsymbol\Delta_{i-1}(u)\) by the previous instance of (7), since \(\deg(J_\gamma^*g)+|u|\le p\). Equation (2), applied with \(n=|u|\), changes it to the right side of (7) using (4).

The actual output begins with \(\widehat{\mathbf b}\) on the old base rows. Give each plus row weight \(+1\) and subtract \(1\) from its unchanged base row at the same clock. No other output is added. Then the shifted output on each paid tree is
\[
 \widehat{\mathbf b}\cdot\mathbf V_0(t)+\sum_{i=1}^r\sum_{a\in S_i}\delta_{i,a}(t)
    =\widehat{\mathbf b}\cdot\left(\mathbf V_0(t)+\sum_{i=1}^r\boldsymbol\Delta_i(t)\right)
    =\widehat{\mathbf b}\cdot\mathbf V_r(t)=\ell(G_t).
\]
This proves all ordinary order conditions by the edge expansion. Output corrections cancel exactly by physical clock, so a scalar failure at degree \(p\) is still the next bush failure. Counting the unchanged prefix, the \(q\) base rows and the plus rows proves (1).

## Exact finite criterion for using fewer sites or different measurements

The test below applies to the paired telescope, not to general SDIRK. Keep the base and each literal same-clock reference but do not fix the cardinal formula (5). Once the lower correction levels have been assigned, let \(\boldsymbol\delta_{i-1}(u)\) denote their actual contrast read for a child \(u\); it may include any proposed earlier linear observations of that contrast. One new set of taps \(K_i\) preserves **all** the layer-\(i\) moments (7) if and only if
\[
 \sum_{a\in S_i}g(a)K_i(a)\boldsymbol\delta_{i-1}(u)
 = \widehat{\mathbf b}\cdot
       \bigl(g(\mathbf x)\odot M\boldsymbol\Delta_{i-1}(u)\bigr)
 \quad\text{for every } |u|\le p-1,\quad\deg g\le p-1-|u|.       \tag{8}
\]
The actual observations must be zero on the leaf and in the inactive band, as above, for the new rows to have the same clocks and the same small factors. Necessity follows by applying (7) to the unary tree \([u]\). For sufficiency substitute \(g=fP\) in (8); (4) and (6) cover every other tree. Thus this is a simultaneous finite linear system over the chosen field, after earlier rows are fixed.

For a fixed cap \(n\), take the actual readout matrix \(Y\) on children through \(n\), the evaluation matrix \(X\) on a basis of test polynomials through \(p-1-n\), and the target pairing matrix \(Z\) on those same children and tests. The corresponding rectangle is precisely \(X^{\mathsf T} K_iY=Z\). In particular \(\ker Y\subseteq\ker Z\) and \(\operatorname{im} Z\subseteq\operatorname{im}X^{\mathsf T}\) are necessary and sufficient for this one rectangle over a field; all caps share the **same** taps. The size \(r-i+1\) is forced if one asks this architecture to reproduce every test through degree \(r-i\) on arbitrary owner input at this cut, in the adjoint formulation of (2), with at least \(r-i+1\) distinct nonzero-weight owners and injective evaluation of \(J_\gamma^*\) on that test space at the nonzero-weight owners. The rank is then \(r-i+1\). This applies to the even/odd rules and dense-donor choices below whenever \(r-i+1<q\), because \(J_\gamma^*\) raises degree by one. In the remaining full-width boundary, no claim of injectivity follows from degree alone. A saving below these source-independent widths must use the **actual** right span, another observation, or cancellation between the different virtual differences. No full penultimate owner-rank condition has been assumed.
