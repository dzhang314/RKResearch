# The strictly interior four-change weak-five quartic is impossible

**Result.** Let $K$ be an ordered field, let $M$ be the actual paid scalar packet `WeakFive16.Moments q Z c`, and suppose $\deg q=4$ and the four nonorigin marks $(u,a,h,z)=(c_1,c_2,c_3,c_4)$ all lie in $(0,1)$. Then $q$ cannot have four sign-changing roots in $(0,1)$ over an order-preserving real closure of $K$. This closes the previously remaining four-change scalar sector. It is a mathematical proof with a finite rational checker, not a Lean replay or an unconditional stage bound. It does not reuse either earlier Gaussian certificate or any held fixed physical fibre.

Use polynomial formal integrals $I_{l,r}$. Put $w=X(1-X)$ and $N=(X-u)(X-a)(X-h)(X-z)$. The paid inputs are precisely
$$
\begin{gathered}
I_{0,1}(wqN H)=0\quad(\deg H\le5),\\
I_{0,u}(Xq)=I_{0,u}(X^2q)=I_{0,a}(X(X-u)q)=0,\\
I_{z,1}((1-X)q)=I_{z,1}((1-X)^2q)=I_{h,1}((1-X)(z-X)q)=0,
\end{gathered}
$$
plus the four marks being distinct and $q$ being nonzero at each. These are fields of $M$, using `middleFactor` and `nodalTail`. After monic scaling and ordered real-closure extension, the four sign-changing unit roots of $q$ are simple and use its entire degree. Thus $T=qN$ is monic of degree eight with eight **distinct** roots strictly inside $(0,1)$. All moment equations, strict orders, and the existing positive rational degree-19 integration mesh survive this extension. No Archimedean assumption, moving-root continuity, or external numerical bound is used.

## 1. Eight nodes, degree thirteen, and the three weight signs

Let $\mu(P)=I_{0,1}(wP)$ and let $P_n$ be its monic orthogonal polynomial in degree $n$. The needed Gram matrices through degree seven are positive definite: a nonzero polynomial square has a strictly positive weighted sample in the 19-node rule, and the total integrand degree is at most 16. Write $h_n=\mu(P_n^2)>0$. The global law pays $T\perp\operatorname{Poly}_{\le5}$. Since $XP_7$ is monic of degree eight and also orthogonal to degrees through five, the difference is in $\operatorname{span}\{P_6,P_7\}$. Therefore uniquely
$$
 T=(X-d)P_7-\kappa P_6 .
$$
Let $\beta_1<\cdots<\beta_8$ be the actual roots of $T$. Division by $T$ and interpolation give a signed eight-node rule $\widehat\mu(P)=\sum_i\omega_iP(\beta_i)$ exact through degree **13**, since the quotient degree is at most five. Neither exactness at degree 14 nor positivity of all weights is assumed.

In the $P_0,\ldots,P_7$ basis the Gram matrix of $\widehat\mu(PQ)$ is diagonal with entries $h_0,\ldots,h_6,\kappa h_6$. All but the last entry are covered by degree-13 exactness. For the last, $XP_6=P_7+$ a polynomial of degree at most six gives $\widehat\mu(XP_7P_6)=\widehat\mu(P_7^2)$ by the paid off-diagonal terms. The nodal identity $(X-d)P_7=\kappa P_6$ gives $\widehat\mu(XP_7P_6)=\kappa h_6$. Evaluation at eight distinct nodes is invertible. Thus:

* $\kappa>0$: all eight weights are positive, by positive definiteness.
* $\kappa=0$: exactly one weight is zero and the others are positive, by the nonnegative form of rank seven. Here $T=(X-d)P_7$ and $d$ differs from every $P_7$-root.
* $\kappa<0$: exactly one weight is negative and the others are positive. The form is nonsingular, has a negative line, and is positive on a seven-dimensional subspace, so it cannot have a two-dimensional negative subspace.

The first error of the four-**mark** signed law is different: for $\nu(P)=\mu(qP)$ it is $\Gamma=\mu(TX^6)=h_7-\kappa h_6=(21/340-\kappa)h_6$. The norm ratio is checked from the fixed reference moments below. No step requires $\Gamma\le0$ or any signed-bracket degree refund.

## 2. A compact domain that includes the negative-weight sector

Write $y=2X-1$. The monic orthogonal polynomials in this coordinate are $p_6=A_6/429$ and $p_7=A_7/715$ for
$$
 A_6=429y^6-495y^4+135y^2-5,\qquad
 A_7=715y^7-1001y^5+385y^3-35y .
$$
Then $P_n(X)=2^{-n}p_n(2X-1)$. The checker verifies orthogonality using exact moments $4/[(j+1)(j+3)]$ for even $j$ and zero for odd $j$ for weight $1-y^2$, as well as the identity
$$
 (1-y^2)A_7'(y)+7y A_7(y)=7A_6(y).
$$
The reference roots $\gamma_1<\cdots<\gamma_7$ of $P_7$ are simple and interior. The first three lie strictly in $(1/20,1/16),(4/25,13/80),(19/60,8/25)$ by exact opposite endpoint signs; the fourth is $1/2$ and reflection gives the rest. The identity above gives
$$
 R(X)=\frac{P_6(X)}{P_7(X)}
     =\sum_{i=1}^7\frac{v_i}{X-\gamma_i},\qquad
 v_i=\frac{20}{21}\gamma_i(1-\gamma_i)>0 .
$$
Indeed these are the actual simple-pole residues $P_6(\gamma_i)/P_7'(\gamma_i)$, and subtracting the pole terms leaves a polynomial vanishing by degree at infinity. The checker also verifies $P_6(0)=1/429$, $P_7(0)=-1/1430$, $R'(0)=-80/3$; parity gives the other endpoint values.

Since the eight actual roots are strictly interior, $T(0),T(1)>0$. Evaluating at the endpoints gives the strict inequalities
$$
 (10/3)\kappa<d<1-(10/3)\kappa,\qquad \kappa<3/20.                 \tag{1}
$$
For $\kappa<0$ put $a_0=-\kappa>0$. No actual root is a reference pole, since $P_6(\gamma_i)\ne0$. On each of the six internal pole gaps, $f(X)=X-d+a_0R(X)$ starts positive and ends negative at points sufficiently close to its endpoints. On the two extreme gaps the end signs are respectively both negative and both positive, by the simple residues and the leading $X-d$ term. Consequently each internal gap has an odd positive root count, and each extreme gap an even count. All roots are simple; with eight roots, precisely one extra pair occurs, either a triple internal gap or a doubled extreme gap. In either case some actual root $\xi\in(0,1)$ crosses from negative to positive, with $f'(\xi)>0$. Thus
$$
 1>a_0 \sum_{i=1}^7\frac{v_i}{(\xi-\gamma_i)^2}.                \tag{2}
$$
The same rising root is the one negative-weight site, since the degree-seven cardinal coefficient gives $\omega_\beta P_7(\beta)=\kappa h_6/T'(\beta)$ and $T'(\beta)=P_7(\beta)f'(\beta)$. It is the middle root in a triple internal gap or the outward member of a doubled extreme gap. The identification is not an additional premise.

The sum in (2) is at least $80/3$ for every non-pole in $[0,1]$. On $[0,\gamma_1)$ each denominator in absolute value is at most its value at 0, where the sum is $-R'(0)=80/3$; reflect for the far right. In an internal gap of length $g$ the two adjacent terms alone give at least $8\min(v_i,v_{i+1})/g^2$, by $1/t^2+1/(g-t)^2\ge8/g^2$. Use the displayed rational lower bounds $\ell=1/20,4/25,19/60$ for the three left gaps' left roots and monotonicity of $\gamma(1-\gamma)$ up to $1/2$. The gap lengths have upper bounds $9/80,4/25,11/60$, respectively. The checker verifies $8(20/21)\ell(1-\ell)/g^2>80/3$ for each bounding pair. Reflect the remaining three gaps. Therefore
$$
                          -3/80<\kappa<3/20.                   \tag{3}
$$
The uses of side signs in (1)--(3) are algebraic: a simple pole has the sign of its residue divided by the distance on each sufficiently close side, infinity signs follow from the leading terms, and the derivative at a simple root has the sign of the crossing.

Reflect if necessary by $(q,u,a,h,z)\mapsto(q(1-X),1-z,1-h,1-a,1-u)$. This swaps the paid end/inner words and preserves the globals with the test reflected. It changes $d$ to $1-d$ and preserves $\kappa$, so assume $d\le1/2$. Set $D=2d-1$, $\lambda=4\kappa$. Now $-3/20<\lambda<3/5$ and $-1+(5/3)\lambda<D\le0$. Thus the actual parameters occur in the **closed unit square** under
$$
 \lambda=(15s-3)/20,\qquad D=-\tfrac54(1-s)t,\qquad 0\le s,t\le1 .
$$
Actual data satisfy $0<s<1$, $0\le t<1$; the table includes edges. The three signs of $\kappa$ correspond to $s>1/5,s=1/5,s<1/5$. At the compact boundary $s=1$ the parameter $t$ is redundant; no claim of simple roots is made there. The scaled centered polynomial with the actual centered roots is
$$
 2145\, T_y(y)=3(y-D)A_7(y)-5\lambda A_6(y),\qquad
 T_y(y)=2^8T((1+y)/2).
$$

## 3. Exact root cages on the whole chart, including collisions

The file `cells.tsv` lists 127 dyadic rectangles. A row begins with $(b_s,i_s,b_t,i_t)$ and specifies $[i_s/2^{b_s},(i_s+1)/2^{b_s}]\times[i_t/2^{b_t},(i_t+1)/2^{b_t}]$. The checker puts both partitions at common dyadic scales and, on every open $s$-slice between successive table endpoints, verifies that the spanning $t$-intervals exactly tile the unit interval. Taking the closures proves the finite union covers the entire closed square, including edges, over every ordered field.

At any listed rational threshold $x=m/B$, $B=32768$, compute the Taylor coefficients $c_j$ of the displayed scaled $T_y$ at $y=2x-1$. Each is affine in $(D,\lambda)$ and hence separately affine in $(s,t)$, so its range is bounded by the four exact corner values. The checker uses integers, clearing the positive scale $B^8\cdot20\cdot2^{b_s+b_t}$.

**A type-0 row: Descartes root-count cages.** The eight pairs following the type code give lower/upper endpoints in denominator $B$ for each ordered root. Descartes' upper bound on positive roots applied to $T_y(y+Y)$ bounds the number of roots strictly greater than $x$ by the sign variations of $(c_j)_j$, omitting zero coefficients. Applied to $T_y(y-Y)$ it bounds roots strictly below $x$ with coefficients $((-1)^j c_j)_j$. This is the usual algebraic sign rule over a real closed field, proved by sign variations under removal of positive linear factors. The checker considers the signs allowed by each interval, then computes the maximum possible variation by a two-state recurrence according to last sign. A zero actual coefficient may be deleted: filling ambiguous zero positions by any allowed nonzero signs cannot reduce variation, and identically zero positions are skipped. Taking independent sign choices only overcounts. For the $i$-th root (one-based), at most $i-1$ roots strictly below its lower cage edge forces $\beta_i$ at least that edge. At most $8-i$ roots strictly above the upper cage edge gives the other bound. The trivial endpoints $0,1$ use the actual unit-root condition. This argument allows the root to **equal** the cage edge. Cages may overlap near a collision or even contain the same limiting node; no parameter-dependent separation estimate, simple-root assumption on other points of the box, or division by a spacing appears. It verifies 123 conditional eight-site cages on entire parameter boxes.

**A type-2 row: real-rootedness fails.** The two entries after the type code give derivative index $k$ and threshold numerator $m$. If a polynomial $P$ of degree $n\ge2$ has all real roots, then
$$
 (n-1)(P')^2-nPP''\ge0
$$
at every real point. Off its roots, divide by $P^2$ and obtain $n\sum r_i^2-(\sum r_i)^2\ge0$ with $r_i=1/(X-\text{root}_i)$; at a root it is immediate. All derivatives of a fully real split polynomial with simple roots are fully real split by the derivative signs at successive roots and IVT. For $P=T_y^{(k)}/k!$, $0\le k\le6$, the values $P,P',P''$ are proportional to $c_k,(k+1)c_{k+1},(k+1)(k+2)c_{k+2}$. Using the exact Taylor intervals, the checker verifies a strictly **negative upper bound** for the Laguerre expression at the listed rational point, ruling out the entire box for actual $T_y$. Its sign is unchanged by common positive scaling. There are four such boxes. Neither this cut nor the conditional cages assume any quadrature weight sign.

## 4. Every possible order contradicts an actual paid port

Write $r_1<r_2<r_3<r_4$ for the actual $q$-roots and $p(x)=\#\{r_i<x\}$. The two endpoint pairs force $p(u)\ge2$ and $p(z)\le2$. Otherwise a constant or affine sign fit of $q$ on the relevant open window contradicts its two exact moments with positive weight $X$ or $1-X$. The true difference windows are
$$
 I_{u,a}(X(X-u)q)=0,\qquad I_{h,z}((1-X)(z-X)q)=0.
$$
If $a<u$, both $(0,a)$ and $(a,u)$ must have a root, so $1\le p(a)<p(u)$; if $a>u$, the difference forces $p(u)<p(a)$. If $h>z$, both $(z,h)$ and $(h,1)$ must have a root, so $p(z)<p(h)\le3$; if $h<z$, the difference forces $p(h)<p(z)$. Every fixed-sign contradiction uses the original positive affine integration mesh and an integrand of degree at most six. The checker enumerates all interleavings of the four ordered root labels with the four permuted marked labels, retaining exactly 141 words by these necessary inequalities, 11 disjoint and 130 overlapping outer-window orders. No signed-step refund is used to discard any word.

Let
$$
 \mathcal J_e(d;R)=I_{0,1}\left(Y^e\prod_{r\in R}(dY-r)\right).
$$
Use $R=\{r_1,r_2,r_3,r_4\}$ and $\bar R=\{1-r:r\in R\}$. The following identities with strictly positive prefactors are the actual paid words under $X=dY$ or $X=1-dY$:

| Paid integral | Normalized test | Prefactor |
|---|---|---|
| $I_{0,u}(Xq)$ | $\mathcal J_1(u;R)$ | $u^2$ |
| $I_{z,1}((1-X)q)$ | $\mathcal J_1(1-z;\bar R)$ | $(1-z)^2$ |
| $I_{0,u}(X^2q)$ | $\mathcal J_2(u;R)$ | $u^3$ |
| $I_{z,1}((1-X)^2q)$ | $\mathcal J_2(1-z;\bar R)$ | $(1-z)^3$ |
| $I_{0,a}(X(X-u)q)$ | $\mathcal J_1(a;R\cup\{u\})$ | $a^2$ |
| $I_{h,1}((1-X)(z-X)q)$ | $\mathcal J_1(1-h;\bar R\cup\{1-z\})$ | $(1-h)^2$ |

In particular the right inner test uses the actual $z-X$, turning into $(1-h)Y-(1-z)$. The four signs from the right substitution in the monic quartic cancel. No site distance is inverted. If a cage includes $d=0$ the normalized test is still polynomial there, while the actual prefactor stays positive.

For fixed $d$, the normalized test is multiaffine in the four or five factor variables, so every Cartesian vertex of their cages suffices. At any factor vertex the test is a polynomial in the common $d$, of degree at most the number of factors. The checker tests its Bernstein coefficients on the entire $d$-interval, preserving the common $d$ in all factors. More explicitly, write $d=A/B$, $r=R_i/B$, and let $q_i$ be the integer coefficients of $\prod_i(Y-R_i)$. After removing $B^{-n}$ with $n$ the number of factors, the normalized polynomial is $\sum_i q_i A^i/(i+e+1)$. On $A\in[L,H]$ write $A=L+(H-L)v$. The $j$-th Bernstein coefficient of $A^i$ in degree $n$ is
$$
 \sum_{k\le\min(i,j)}\binom{i}{k}L^{i-k}(H-L)^k
                           \binom{j}{k}/\binom{n}{k}.
$$
The nonnegative Bernstein basis sums to 1. Strict same sign at every coefficient of every factor vertex proves strict sign in the full cage by convex combinations first in $d$, then in the factor variables. The checker computes the coefficients with exact cleared moment and binomial denominators. For each of the 141 orders in each of the 123 cages it finds a strict normalized sign of some listed paid port, with smallest certified absolute normalized margin at least $24/10^9$. That port cannot be zero. The four infeasible boxes already have no eight-root packet. Complete compact coverage now contradicts every actual packet, for all three signs of $\kappa$.

## Reproduce and connect

Put `check_four_changes.py` and `cells.tsv` together and run `python3 check_four_changes.py` without `-O`. Only standard-library exact integer/rational tests and the finite table are needed. Numerical scouting only proposed cells and edges; all sign bounds, complete coverage, reference identities, and root/mark enumeration are independently rechecked without floats. No previous Gaussian certificate, held input, physical fixed-fibre arithmetic, resultant or norm-elimination calculation is used. The fixed inner-product ratio $h_7/h_6$ of reference polynomials is not a norm elimination.

The input is the same $M$ returned by `width24_weak_five_quartic_remaining`: no positivity of original tableau weights, no extra moment, and no supplied clock ordering beyond strict interiority and the root-count branch. It complements the previously excluded two-change positive and negative tails and the three-change sector. Joining the independent exterior, two-change, and three-change mathematical results gives a source-level closure of the weak-five quartic only. The separate weak-four chart and a native checked assembly are not covered.
