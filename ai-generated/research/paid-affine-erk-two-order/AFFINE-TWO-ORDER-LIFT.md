# An iterable paid two-order lift for explicit Runge–Kutta methods

Let the old order be \(q\ge6\), the target order \(p\coloneqq q+2\), and the degree parameter \(m\coloneqq q-2=p-4\). Work over \(\mathbb U_p\coloneqq\mathbb Z[1/p!]\). This is a relative construction. It adds a number of rows linear in \(q\) once the initial forward chart is prepared. It does not assert any new absolute optimum.

## The prepared old method

The old method is strictly explicit and satisfies the rooted-tree order conditions through order \(q\). It has an original zero-clock row and an actual clock-one endpoint row whose incoming coefficients are the old output weights \(\mathbf b\). The endpoint is not needed in the support of \(\mathbf b\). Auxiliary stages and the endpoint may be added with zero output weights. Write \(\mathbf c\) for the old clocks. Use \(E_xf\coloneqq f(x)\) and \(I_xf\coloneqq\int_0^x f(z)\,dz\).

A prepared chart \(\Pi_m\) is a linear map from old stage data to polynomials of degree at most \(m-1\). For each rooted tree \(t\) through order \(p\), or formally over the rationals at higher orders, set
\[
 g_t(x)\coloneqq \frac{|t|}{t!}x^{|t|-1},
 \qquad
 \rho_t\coloneqq g_t-\Pi_m\boldsymbol{\Phi}_t(A).
\]
The chart is exact through tree order \(m\). Its evaluations at zero and one are the reads from the two actual endpoint rows. Its first two integral reads, on arbitrary data \(\mathbf w\), are
\[
 I_1(\Pi_m\mathbf w)=\mathbf b\cdot\mathbf w,\qquad
 I_1(x\Pi_m\mathbf w)=(\mathbf b\odot\mathbf c)\cdot\mathbf w .
\]
Thus \(I_1\Pi_m\) is exactly the incoming row of the old endpoint, not merely a row producing the same low-order weights.

The two output-derived reads are what removes the narrow reverse compatibility. For \(|t|=m+2\) the polynomial \(\rho_t\) vanishes at both endpoints and has integral zero. For \(|t|=m+1\) it has, in addition, first moment zero. In that second case \(I_x\rho_t\) vanishes at both endpoints and has integral zero, because \(I_1(I_x\rho_t)=I_1((1-x)\rho_t)\). These statements use only old rooted-tree equations of order at most \(m+2\). In particular, multiplying the derivative profile by \(x\) corresponds to a rooted sum with \([\bullet]\).

## One reverse suffix works in both parities

Let \(n\coloneqq p\) if \(p\) is odd and \(n\coloneqq p-1\) if \(p\) is even. Use the \(n\) clocks \(x_j\coloneqq j/(n-1)\), \(0\le j<n\). Let \(\lambda_j\) be the integral of the corresponding Lagrange cardinal polynomial. All site differences and interpolation denominators are paid. Quadrature is exact through degree \(p-1\): the ordinary interpolation proof gives degree \(n-1\), and the monic nodal polynomial is odd about one-half, giving one further degree.

Use four donors in reverse order at the first clock one and then at three distinct nonendpoints \(a,b,c\), with \(c=(a+b)/2\). For example the fractions with numerators \(1,3,2\) and denominator \(n-1\) work at every order under consideration. All donor masses can be chosen to equal one. To keep the raw quadrature rule, give the remaining mass at each donor clock to labels outside the donor columns. Each nonendpoint has a pure label of mass one available in addition to any corrected donor label. The residual mass is placed on another pure label at the same clock, possibly zero. This bookkeeping uses only one pure physical row at any clock.

Write \(y_i\coloneqq1-x_i\), \(\kappa\coloneqq-(1-a)^2/2\), and let \(\mathbf u\) have value \(\kappa\) on the three nonendpoint donor labels and zero at the first endpoint. Initially put \(\kappa\) also on every pure nonendpoint label. The exactness adjustment below changes only these pure labels. Build a strict lower triangular \(L\) in reverse label order, using only the four donor columns. Require
\[
 L\mathbf1=\mathbf y,\qquad
 L\mathbf y=\mathbf y^{\odot2}/2+\mathbf u,\qquad
 \mathbf g\coloneqq L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\qquad
 \mathbf v\coloneqq L\mathbf u.
\]
The first row is zero. The row at \(a\) uses only the first column, with coefficient \(1-a\), and gives the prescribed \(u_a=\kappa\). The row at \(b\) uses the first two columns; the unit difference of their \(y\)-values pays its two equations. Let \(G,V\) be the affine polynomials in \(y\) interpolating the resulting \(g,v\) at \(a,b\).

The row at \(c\) can meet \(g_c=G(y_c)\) and \(v_c=V(y_c)\) at once. To check this, write \(A_0\coloneqq1-a\), \(B_0\coloneqq1-b\), \(C_0\coloneqq1-c\), and define \(\alpha,\gamma\) by agreeing \(\alpha y+\gamma y^2\) with \(u\) at the first three donors. Since the two nonzero values are \(\kappa\), one has \(\alpha=-\gamma(A_0+B_0)\). Any of the first three nonendpoint donor rows therefore obeys
\[
 v_i-\gamma g_i=\alpha(y_i^2/2+\kappa)+\gamma y_i^3/3 .
\]
The right-hand cubic has second divided difference \(\alpha/2+\gamma(A_0+B_0+C_0)/3=0\) on these three interior points. Its values there agree with the affine polynomial \(V-\gamma G\). The row at \(c\) can prescribe \(L\mathbf1,L\mathbf y,L\mathbf y^{\odot2}\) using the first three donor columns and a paid Vandermonde. Prescribing \(g_c=G(y_c)\) then gives \(v_c=V(y_c)\).

For all remaining labels, the row can independently prescribe \(L\mathbf1,L\mathbf y,L\mathbf y^{\odot2},L\mathbf u\) using the four donor columns. The donor matrix for \(\mathbf1,\mathbf y,\mathbf y^{\odot2},\mathbf u\) is a paid unit: its cubic divided difference of \(u\) is \(\kappa/(A_0B_0C_0)\), and its other factor is the paid Vandermonde. Use \(g=G(y)\), \(v=V(y)\) at every nonendpoint label, even those whose \(u\) is changed later. At the pure label at one set \(u=g=v=0\), so its \(L\) row is zero. At zero the four values can be chosen with \(L\mathbf1=1\); the other components do not affect any of the vanishing tests at that endpoint.

If \(\beta_i\) is the mass of virtual label \(i\), set the suffix block in primal order by
\[
 (A_S)_{ji}\coloneqq
 \begin{cases}
   \beta_iL_{ij}/\beta_j,&j\text{ is a donor},\\
   0,&j\text{ is not a donor}.
 \end{cases}
\]
Use \((I-A_SE)\Pi_m\) for the block from old stages to suffix stages, where \(E\) and \(I\) collect the evaluations and primitives at the suffix clocks. The output is \(\boldsymbol{\beta}\) on the suffix. This is strictly explicit. Every pure label at \(x\) has exactly the row \(I_x\Pi_m\); it has no incoming taps from suffix stages. Thus all its virtual copies merge, redirecting outgoing taps and summing weights. At zero and one the pure rows already belong to the old prefix. The other pure rows contribute \(n-2\) stages, and the four donors contribute four, for a total of \(n+2\) new physical rows.

## Ordinary order

Let \(\langle\mathbf u,\mathbf w\rangle_\beta\coloneqq\sum_i\beta_i u_iw_i\), and let \(X\) denote multiplication by the clock on suffix vectors. The suffix block satisfies
\[
 \langle\mathbf f,A_S\mathbf h\rangle_\beta
 =\langle L\mathbf f,\mathbf h\rangle_\beta .
\]
If \(\boldsymbol\epsilon_t\) is the suffix derivative profile minus \(E g_t\), the extension recurrence is
\[
 \boldsymbol\epsilon_{[t]}=(A_SE-I)\rho_t+A_S\boldsymbol\epsilon_t .
\]
Rooted sum multiplies both profiles coordinatewise. The first possible error has tree order \(m+2\), so through \(p=m+4\) no product contains two errors. Each remaining weighted error is therefore a scalar multiple of a word in \(A_S,X\), applied to \((A_SE-I)\rho_t\). For \(|t|=m+1,m+2,m+3\), the word has length at most two, one, zero, respectively.

Define \(Jf(x)\coloneqq\int_x^1 f(z)\,dz\) and \(U(f)\coloneqq\sum_i\beta_i u_if(x_i)\). Through total degree \(p-1\), the quadrature identity \(\langle E f,I\rho\rangle_\beta=\langle E(Jf),E\rho\rangle_\beta\) follows by integrating over the triangle. The length-zero error cancels because \(L\mathbf1=E(J1)\). At length one the only differences from the triangle identity are the pairings with \(\pm\mathbf u\), because \(L\mathbf x=E(Jx)-\mathbf u\) and \(L\mathbf y=E(Jy)+\mathbf u\). For length two, after the exact polynomial terms are removed, the four rows give
\[
\begin{array}{c|l}
\text{word}&\text{remaining error}\\ \hline
X^2&\langle-2\mathbf u+\mathbf g,E\rho_t\rangle_\beta\\
A_SX&\langle\mathbf u-\mathbf g,E\rho_t\rangle_\beta\\
XA_S&\langle\mathbf u-\mathbf g/2-\mathbf v,E\rho_t\rangle_\beta+U(I_x\rho_t)\\
A_S^2&\langle\mathbf g/2+\mathbf v,E\rho_t\rangle_\beta-U(I_x\rho_t).
\end{array}
\]
These expressions vanish. The constant interior value of \(u\) kills the endpoint-zero, mean-zero tests, including the primitive in the table. The affine \(G,V\) kill the endpoint-zero tests with vanishing zeroth and first moments. All higher degree uses of the quadrature identity in this verification are bounded by \(p-1\). The exactness adjustment changes \(U\) by a functional vanishing on the entire endpoint-zero test space of degree at most \(m+1\), so the same verification applies after adjustment.

## Exact order without paying the next prime

There are at least \(m+1\) nonendpoint geometric clocks even in the shorter parity. Choose any \(m+1\) of them, comprising a set \(D\). Adjust \(u\) only on the unit-mass pure label at each \(x\in D\), adding
\[
 \frac{\theta}{x(1-x)\prod_{z\in D\setminus\{x\}}(x-z)} .
\]
The divided-difference identity shows that the change in \(U\) vanishes on \(x(1-x)\mathcal P_{\le m-1}\). The donor values of \(u\) stay fixed, so the four-column solve can continue to prescribe the same affine \(G,V\) at the altered labels. The adjustment causes no new physical row.

Let \(r\coloneqq[\bullet]^{\#(p-2)}\), \(t\coloneqq[r]\#[\bullet]\), and \(B\coloneqq[\bullet]^{\#p}\). The residual \(\rho_r\) has zero endpoint values and leading term \(x^{p-2}\). Its quotient by \(x(1-x)\) has leading coefficient \(-1\), so the change in \(U(\rho_r)\) is \(-\theta\). Before adjustment,
\[
 U(\rho_r)=\kappa I_1\rho_r
           =\kappa\bigl(1/(p-1)-\mathbf b\cdot\mathbf c^{\odot(p-2)}\bigr).
\]
Take \(\theta\) to be this last expression minus one. This gives \(U(\rho_r)=1\) by paid arithmetic, regardless of whether the old order-\((q+1)\) bushy condition happened to hold.

Let \(D_w\coloneqq w!\,\boldsymbol\beta\cdot\boldsymbol\Phi_w-1\) be the cleared defect at tree \(w\). The bushy tree \(r\) has no suffix stage derivative error. In \(t\), its one extension and one added leaf give the reverse operator \(L\mathbf x=E(Jx)-\mathbf u\). The coefficient of \(x^p\) in \((Jx)\rho_r-xI_x\rho_r\) is \(-1/2-1/(p-1)\), and the integral is zero. The exact derivative of \(t\) contributes \(1/(p-1)\) times the bushy degree-\(p\) quadrature error. Multiplying the resulting identity by \(p+1\) gives, entirely in the paid ring,
\[
 \frac{D_t}{p-1}+\frac{D_B}{2}=-(p+1).
\]
For \(\mathcal Q[f]\coloneqq\sum_i\beta_i f(x_i)\) we also have \(D_B=(p+1)\mathcal Q[x^p]-1\). Consequently the two defects generate the unit ideal, even when \(p+1\) is not a unit. This proves exact order \(p\) over every nonzero \(\mathbb U_p\)-algebra.

The construction leaves the old coefficients as they were and uses no scaled copy of an old tableau. The old output rule and its single clock-weighted read are enough. This avoids new scaling primes; it does not purify an old seed whose coefficients were already outside the paid ring.

## Preparing the next lift

For the next step one needs a chart of grade \(m+2\) with the new output pins. All the pure \(I_x\Pi_m\) rows at the quadrature clocks survive the merge. Their derivative reads are exact through tree order \(m+1\). They therefore yield a chart \(\Pi_{m+1}\) at no row cost by ordinary paid interpolation.

At tree order \(m+2\), a non-unary root still has its exact derivative profile at the pure rows, since each child now has order at most \(m\). A unary root \([t]\) instead has derivative profile \(g_{[t]}-I_x\rho_t\) there. The primitive nuisance \(P\coloneqq I_x\rho_t\) has degree at most \(m+1\), double zeros at both endpoints, and mean zero. Thus the pure reads, interpolated on \(m+2\) clocks, recover one polynomial \(D\), the exact profile minus this nuisance. For all lower grades the nuisance is zero. Appending at most \(m-2\) new stages of the form \(I_z\Pi_{m+1}\) gives exact grade-\((m+2)\) derivative reads. Subtracting \(D(z)\) from these reads gives the nuisance at the new clocks. With its four endpoint value and derivative zeros, paid interpolation reconstructs it and hence gives the grade-\((m+2)\) chart.

One can save one of those new value rows for each of several interior pins. At the beginning of the old lift, move \(k\) of its already budgeted pure quadrature rows \(I_z\Pi_m\) into the old prefix. Let \(C\) collect their clocks together with zero and one. For each new pin \(z\), let \(R_z\) have a double root at \(z\), triple roots at the other elements of \(C\), and normalization \(R_z''(z)=1\). One may take a scalar multiple of the product of these factors; the scalar only inverts two and unit site differences. Replace \(\Pi_m\) by
\[
 \Pi_m+\sum_{z\in C\setminus\{0,1\}}
   R_z''\bigl(E_{\mathrm{new},z}-E_z\Pi_m\bigr),
\]
where \(E_{\mathrm{new},z}\) reads the moved stage. This requires \(3(k+1)\le m-1\). All \(I_x\Pi_m\) at the pins remain literally fixed, since \(R_z'\) vanishes at every pin. All old moment reads remain fixed, since \(I_1(xR_z'')=0\) by integration by parts. The new pins read exact through grade \(m+1\), so at each of them \(\rho_{m+1}=0\). Their pure suffix copies are merged, so moving them added no physical stage.

The nuisance \(P\) consequently has \(P'(z)=0\) at those \(k\) pins. Collect its values at the \(k\) pins and at \(m-2-2k\) other sites, using only \(m-2-k\) new stages. These values, the pinned derivative zeros and the endpoint double zeros give ordinary Hermite interpolation on \(m+2\) conditions. Its pivots are paid because the node gaps are units; equivalently, the ideals \((x-z)\) or \((x-z)^2\) at distinct nodes are pairwise comaximal with unit gaps.

Append the new actual endpoint by using the new output coefficients as an incoming row, if it is not present already. It can be used for the unit-clock evaluation in the recovered chart, because the nuisance vanishes there. To impose the two new integral reads without altering the endpoint values, use rank-two corrections from \(x(1-x)\) and \(x^2(1-x)\); their two moment matrix has determinant \(1/720\). Their residuals against the new output reads are zero on all trees through the new chart grade. This produces the prepared lift invariant again.

Thus a prepared order-\(q\) method yields an exact order-\((q+2)\) method in \(n+2\) extra rows and a prepared one in at most \(n+q-1-k\) extra rows, with \(0\le k\le\lfloor(q-6)/3\rfloor\). Consecutive lifts of either parity can use the same formula, including all targets through twenty.

## Preparing a bare seed

There is a paid construction of the first chart independent of favorable fixtures. Let \(g_0\coloneqq\min(m,\lfloor(q+3)/2\rfloor)\). At grade \(g_0\), use the two endpoint evaluations and the \(g_0-2\) old output reads \((\mathbf b\odot\mathbf c^{\odot j})\cdot\mathbf w\), with \(0\le j\le g_0-3\). On polynomials vanishing at the endpoints their test matrix is the moment matrix for the weight \(x(1-x)\). It has unit determinant. Indeed, derivatives of \(x^{j+1}(1-x)^{j+1}\) of order \(j\), divided by \(x(1-x)\) and normalized to be monic, give a triangular orthogonal basis by integration by parts. Their leading coefficients and pairings against \(x^j\) involve only factorials through \(2j+3\le2g_0-3\le q\), so all are units.

Each subsequent grade \(g\le m\) can be obtained by appending \(g-2\) stages from the previous primitive and adjoining the two endpoint reads, using a paid equal-grid Vandermonde. Finally impose the two moment pins with the rank-two correction above. A bare \(s\)-row seed therefore needs at most \(1+\sum_{g=g_0+1}^m(g-2)\) prepared rows beyond its original stages, counting the endpoint. This initial cost is incurred once; the repeated two-order lifts use the linear bound.

## Why the same polynomial choices do not lower the chart by another grade

For the tempting variant \(m=q-3\), the old order has three moment reads on the first source residual, so one might try to choose the new higher reverse profiles quadratic on all nonendpoints while keeping \(u\) constant and \(g,v\) affine. The first four donors above cannot do this just by adding a fifth distinct donor.

Write \(S_1\coloneqq A_0+B_0+C_0\), \(S_2\coloneqq A_0B_0+A_0C_0+B_0C_0\), and \(S_3\coloneqq A_0B_0C_0\). On the first four donor columns the cubic \(y^3\) agrees with \(S_1y^2-S_2y+S_3u/\kappa\). Thus on any nonendpoint row using these columns, the profile \(L\mathbf y^{\odot3}-\mathbf y^{\odot4}/4\) is forced to the polynomial
\[
 H_{\rm forced}(y)\coloneqq
 S_1(y^3/3+G(y))-S_2(y^2/2+\kappa)
 +(S_3/\kappa)V(y)-y^4/4.
\]
If \(H\) is the quadratic agreeing with this polynomial at \(A_0,B_0,C_0\), comparison of the leading two coefficients gives
\[
 H_{\rm forced}(y)-H(y)
 =-\tfrac14(y-A_0)(y-B_0)(y-C_0)(y-S_1/3).
\]
The affine compatibility forced \(S_1/3=C_0\). With paid distinct gaps, no fifth distinct clock can satisfy this equality while using only the first four donor columns. A duplicate at \(C_0\) preserves it but adds no independent cubic column. This is an obstruction to these particular constant, affine and quadratic profile choices, not to all possible lower-grade lifts.
