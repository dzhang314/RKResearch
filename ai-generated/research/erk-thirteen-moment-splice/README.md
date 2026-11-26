# An exact 42-stage paid ERK method of order thirteen

**Current witness: 41 stages.** The new [41-stage method](ORDER-13-IN-41-STAGES.md) uses the same suffix and one fewer preparation stage. Its [literal tableau](tableau-13-41.json) and [integer-arithmetic verifier](check-41.py) check all 20,299 rooted order conditions and a unit combination of order-fourteen defects. Run `python reconstruct-41.py` to reconstruct the literal tableau from the order-nine seed. The 42-stage construction below is retained as an archive and specifies the common suffix.

The construction uses coefficients in \(\mathbb U_{13}\coloneqq\mathbb Z[1/13!]\). Its order conditions through order thirteen hold over every nonzero \(\mathbb U_{13}\)-algebra. At order fourteen a linear combination of two order defects is a unit, so order thirteen is exact over every such algebra. No machine search or replay is used in this construction.

## The forward rows

Use the 28-row prefix constructed in [the forward chart](FORWARD-CHART.md) from the [16-row order-nine seed](../erk-nine-moment-splice/README.md). The prefix consists of the seed, its order-nine endpoint, the new midpoint obtained from the order-six chart, four new rows obtained from the order-seven chart, and six new rows obtained from the order-eight chart. Its map \(\Pi\) sends vectors on the 28 prefix stages to polynomials of degree at most eight. For a rooted tree \(r\) of order at most fourteen, define
\[
 g_r(x)\coloneqq \frac{|r|}{r!}x^{|r|-1},
 \qquad
 \rho_r\coloneqq g_r-\Pi\boldsymbol{\Phi}_r(A_F),
\]
where \(A_F\) is the prefix tableau. Then \(\rho_r=0\) for \(|r|\le9\). The zero-clock evaluation of \(\Pi\) is the reading at the original zero row and its unit-clock evaluation is the reading at the pinned endpoint. Therefore \(\rho_r(0)=0\) for every tree and \(\rho_r(1)=0\) for \(|r|\le10\). The primal row \(I_1\Pi\), with \(I_x f\coloneqq\int_0^x f(z)\,dz\), is the already-present endpoint row, because the integral is one of the stipulated order-nine chart readings.

## The quadrature

In the coordinate \(u=12x-6\), use the thirteen sites
\[
 -6,-5,-4,-3,-2,-1,0,2,3,4,5,6,8.
\]
All site differences are units: before division by twelve they are nonzero integers of absolute value at most fourteen, and \(14=2\cdot7\). The raw quadrature weights \(\lambda_x\) are integrals of the Lagrange cardinal polynomials for these sites on \([0,1]\). This defines all weights by paid rational arithmetic and gives exact quadrature through degree twelve.

In particular the weight at \(a\coloneqq5/6\) is the unit
\[
 \lambda_a=\frac{6534}{79625}
           =\frac{2\cdot3^3\cdot11^2}{5^3\cdot7^2\cdot13}.
\]
To verify this, define the eleven-site nodal polynomial and the mean in the centered variable by
\[
 P(u)\coloneqq u\prod_{k=2}^6(u^2-k^2),
 \qquad I[f]\coloneqq\frac1{12}\int_{-6}^6 f(u)\,du.
\]
The old site \(u=4\) has derivative \(P'(4)=2^9 3^3 5\cdot7\). Its Lagrange numerator integral and the degree-twelve nodal moment are
\[
 H\coloneqq I\left[\frac{P(u)}{u-4}\right]
       =-\frac{2^9 3^5}{5\cdot11},
 \qquad
 M\coloneqq I[uP(u)]
       =-\frac{2^{11}3^5\cdot23\cdot367}{5\cdot7\cdot11\cdot13}.
\]
These fractions follow using \(I[u^{2j}]=36^j/(2j+1)\) and the following two polynomials in \(t=u^2\). The even part of \(P(u)/(u-4)\) is \(t^5-74t^4+1729t^3-13896t^2+32400t\), and \(uP(u)=t^6-90t^5+2913t^4-41560t^3+254736t^2-518400t\). The two new sites are \(-1,8\); their nodal factor at \(u=4\) is \(T\coloneqq(4+1)(4-8)=-20\). Since \(I[P]=0\), the old weight \(-9/1925\) is multiplied by \(1+M/(HT)\). In the numerator,
\[
 4\cdot23\cdot367-20\cdot91=31944=2^3\cdot3\cdot11^3.
\]
It follows that \(1+M/(HT)=-7986/455\), giving the indicated \(\lambda_a\).

## Reverse rows and the physical tableau

The four donors, in reverse stage order, have clocks \(1,a,b,c\), where
\[
 b\coloneqq\tfrac12,\qquad c\coloneqq\tfrac23,\qquad y_x\coloneqq1-x.
\]
Each geometric nonendpoint clock \(x\) has a selected label of mass \(\mu_x\) and may have a remainder label of mass \(\lambda_x-\mu_x\). The nonendpoint set \(\mathcal I\) has eleven clocks. Define
\[
 D_x\coloneqq x\prod_{z\in\mathcal I\setminus\{x\}}(x-z),\qquad
 \mu_a\coloneqq\lambda_a,\qquad u_a\coloneqq-\frac{y_a^2}{2},\qquad
 \eta\coloneqq u_a\mu_a D_a .
\]
All \(D_x\) and \(\eta\) are units. Set the two selected donor masses by
\[
 u_b\coloneqq1,\qquad u_c\coloneqq\tfrac13,\qquad
 \mu_b\coloneqq\frac{\eta}{u_bD_b},\qquad
 \mu_c\coloneqq\frac{\eta}{u_cD_c}.
\]
At each of the eight remaining selected nonendpoint labels let \(\mu_x\coloneqq1\) and \(u_x\coloneqq\eta/(\mu_x D_x)\). The first donor at \(x=1\) has mass \(1\) and \(u=0\). The raw mass at \(x=0\) is a single label. Use \(u=0\) at the origin and at every remainder label, including the remainder at \(x=1\). For any polynomial \(f\) define
\[
 U(f)\coloneqq\sum_i\beta_i u_i f(x_i),
\]
where \(i\) ranges over all labels, \(x_i\) is their clock, and \(\beta_i\) their assigned mass. The Lagrange leading-coefficient identity on the eleven clocks gives \(U(f)=0\) for \(f\in x\mathbb U_{13}[x]_{\le9}\), and \(U(x^{11})=\eta\).

Define a strict lower triangular matrix \(L\) in reverse label order, supported only in the four donor columns. The first row is zero. The row at \(a\) has just \(y_a\) in the first column. The rows at \(b,c\) use only the first two columns and satisfy
\[
 (L\mathbf1)_i=y_i,\qquad
 (L\mathbf y)_i=y_i^2/2+u_i.
\]
Their two coefficients are uniquely determined since \(y_a=1/6\) is a unit. On these first four rows define
\[
 g_i\coloneqq (L\mathbf y^{\odot2})_i-y_i^3/3,\qquad
 v_i\coloneqq (L\mathbf u)_i.
\]
The four donor rows of \((\mathbf1,\mathbf y,\mathbf y^{\odot2},\mathbf u)\) form an invertible matrix. The ordinary Vandermonde factor is a unit, and the divided difference of \(u\) at \(0,y_a,y_b,y_c\) is
\[
 \frac{-1/72}{1/108}+\frac{1}{1/36}+\frac{1/3}{-1/108}
 =-\frac32.
\]

At the origin and all remainder labels set \(g_i=v_i=0\). At the eight late selected labels solve for \(g_i,v_i\) so that
\[
 \sum_i\beta_i g_i f(x_i)=\sum_i\beta_i v_i f(x_i)=0
 \qquad(f\in x(1-x)\mathbb U_{13}[x]_{\le7}).
\]
Each system is an eight-site Vandermonde times unit diagonal factors, since all these labels have mass \(1\) and neither endpoint occurs among them. On each late row, including the origin and remainders, let its four donor coefficients be the solution to the four equations
\[
 \bigl((L\mathbf1)_i,(L\mathbf y)_i,(L\mathbf y^{\odot2})_i,(L\mathbf u)_i\bigr)
 =\bigl(y_i,\ y_i^2/2+u_i,\ y_i^3/3+g_i,\ v_i\bigr).
\]
In particular the remainder at \(1\) has zero row in \(L\).

The primal suffix order is the reverse of the label order. For suffix labels \(i,j\), set
\[
 (A_S)_{ji}\coloneqq
 \begin{cases}
   \beta_i L_{ij}/\beta_j,&j\text{ is a donor},\\
   0,&j\text{ is not a donor}.
 \end{cases}
\]
Only the donor masses, all units, are inverted. Let \(E\) and \(I\) be the vectors of evaluation and primitive functionals at the suffix clocks. The block from the prefix to the suffix is \((I-A_S E)\Pi\). The prefix has zero couplings to the suffix, and the output masses are \(\beta\) on the virtual suffix and zero on the prefix.

Each label other than the four donors has incoming row \(I_x\Pi\), with no taps from suffix stages. Thus a remainder can be merged with the selected label at the same clock whenever the latter is not a donor. The merge sums output weights and redirects outgoing taps. The origin merges into the existing zero prefix row, and the remainder at one merges into the existing prefix endpoint. Only the two remainders at \(b,c\) need their own rows. With one physical selected row at each nonzero clock, this gives \(28+12+2=42\) rows. Keeping a zero remainder if necessary does not change the method. The entire construction is strictly explicit.

## Verification through order thirteen

For a suffix vector use the bilinear pairing \(\langle \mathbf f,\mathbf g\rangle_\beta\coloneqq\sum_i\beta_i f_i g_i\). The construction of \(A_S\) gives \(\langle \mathbf f,A_S\mathbf g\rangle_\beta=\langle L\mathbf f,\mathbf g\rangle_\beta\), including at virtual labels with nonunit mass. Define
\[
 \boldsymbol\epsilon_r\coloneqq\boldsymbol{\Phi}_r(A)|_S-E g_r,\qquad
 K\coloneqq A_S E-I,\qquad X\coloneqq\operatorname{diag}((x_i)_i).
\]
The extension recurrence is
\[
 \boldsymbol\epsilon_{[r]}=K\rho_r+A_S\boldsymbol\epsilon_r.
\]
Rooted sum multiplies stage derivatives coordinatewise and multiplies the exact polynomials. The first possible nonzero error occurs at tree order eleven, so rooted sums of total order at most thirteen never have a product of two errors. Every contribution after this expansion is, up to a scalar, \(WK\rho_r\), where \(|r|\ge10\), \(W\) is a word in \(X,A_S\), and its length is at most \(12-|r|\).

Put \(Jf(x)\coloneqq\int_x^1 f(z)\,dz\). Polynomial integration over the triangle \(0\le z\le x\le1\) and quadrature through degree twelve give
\[
 \langle E f,I\rho\rangle_\beta=\langle E(Jf),E\rho\rangle_\beta
 \qquad\bigl(\deg f+\deg\rho+1\le12\bigr).
\]
For the empty word the weighted contribution is zero because \(L\mathbf1=\mathbf y=E(J1)\). For length one the extra terms from \(L\mathbf x\) and \(L\mathbf y\) are \(-\mathbf u,\mathbf u\), which vanish against \(\rho_r\): for \(|r|\le11\), it has degree at most ten and vanishes at zero.

For length two one has \(|r|=10\), so \(\rho_r\in x(1-x)\mathbb U_{13}[x]_{\le7}\) and \(I_x\rho_r\in x\mathbb U_{13}[x]_{\le9}\). With the exact polynomial terms removed by the triangle identity, the four weighted residuals are
\[
\begin{array}{c|l}
 W & \text{weighted residual}\\ \hline
 X^2 & \langle -2\mathbf u+\mathbf g,E\rho_r\rangle_\beta\\
 A_S X & \langle \mathbf u-\mathbf g,E\rho_r\rangle_\beta\\
 X A_S & \langle \mathbf u-\mathbf g/2-\mathbf v,E\rho_r\rangle_\beta
                  + U(I_x\rho_r)\\
 A_S^2 & \langle \mathbf g/2+\mathbf v,E\rho_r\rangle_\beta-U(I_x\rho_r).
\end{array}
\]
All are zero by the three moment systems. For example \(L\mathbf x=E(Jx)-\mathbf u\) and \(L\mathbf y^{\odot2}=E(Jy^2)+\mathbf g\), which give the third row after applying \(L\) again. Hence the output agrees with the exact integral of \(g_t\) for every tree through order thirteen, namely \(1/t!\).

## A unit combination of order-fourteen defects

Let \(r\coloneqq[\bullet]^{\#11}\), \(t\coloneqq[r]\#[\bullet]\), and \(B\coloneqq[\bullet]^{\#13}\). Write \(\Delta_w\coloneqq\boldsymbol\beta\cdot\boldsymbol{\Phi}_w(A)-1/w!\). The two required trees are \(t,B\), both of order fourteen. The normalized quadrature functional \(\mathcal Q[f]\coloneqq\sum_i\beta_i f(x_i)\) gives
\[
 \Delta_B=\mathcal Q[x^{13}]-1/14.
\]
For the bushy tree \(r\), the suffix derivative weights equal \(E(x^{11})\) because the stage clocks are exact. Thus \(\boldsymbol\epsilon_r=0\), and \(\rho_r=x^{11}-\Pi\boldsymbol{\Phi}_r(A_F)\) has leading term \(x^{11}\) and no constant term. The extension and the one added leaf give
\[
 \Delta_t
 =\frac{\Delta_B}{12}
  +\mathcal Q[(Jx)\rho_r-xI_x\rho_r]-U(\rho_r).
\]
The polynomial in the middle has integral zero and degree at most thirteen, with coefficient \(-1/2-1/12\) at \(x^{13}\). Since the quadrature is exact through degree twelve, that middle term is \((-1/2-1/12)\Delta_B\). Also \(U(\rho_r)=U(x^{11})=\eta\). Therefore
\[
 \Delta_t+\tfrac12\Delta_B=-\eta.
\]
The right-hand side is a unit, so these two order conditions cannot both hold over any nonzero \(\mathbb U_{13}\)-algebra. If order defects are instead cleared by tree factorials, the same unit-ideal conclusion holds because the factorials of both trees are units in \(\mathbb U_{13}\).
