# Exact width of uniform explicit leapfrog paths, even with arbitrary reads

Let $p\geq1$, let $R\ne0$ be a commutative ring, and assume $p!$ is a unit in $R$. An explicit leapfrog path of mesh $\delta\in R$ has stages
$$
Y_0=y,\qquad Y_1=y+H\delta f(Y_0),\qquad
Y_{j+2}=Y_j+2H\delta f(Y_{j+1}).
$$
A path with evaluations through $Y_J$ uses these $J+1$ derivative values, whether or not a terminal state is read. All paths start from the same $Y_0$. Allow arbitrary signed $R$-weights on **all** their derivative evaluations and allow exactly identical evaluations to share a stage. In particular, any normalized affine combination of partial endpoint states is allowed, and different paths and output reads need not have the same endpoint time or the same parity.

**Claim.** Every order-$p$ explicit RK tableau of this form has at least $1+\lfloor p^2/4\rfloor$ physical stages. The bound is attained over $\mathbb Z[1/p!]$ by the same-parity full endpoints, with cleared next tall-tree defect $-1$. For order nine the bound is 21 stages, with coefficient primes only $2,3,5,7$. This is an architecture theorem, not an unrestricted ERK lower bound.

## 1. Literal stage reads and the paid masks

Use $\boldsymbol{\Phi}_{\bullet}(A)=\mathbf1$,
$\boldsymbol{\Phi}_{[t_1,\ldots,t_m]}(A)=\bigodot_\nu A\boldsymbol{\Phi}_{t_\nu}(A)$, and write $c=A\mathbf1$. The superscript on a stage column denotes a coordinatewise power. Along one path put $c_j=j\delta$, $z_j=\delta^2$, $o_j=1$ for $j$ odd and $o_j=0$ for $j$ even; $e_j=1-o_j$. The shared origin has $c=0$ and even parity. The row definition gives
$$
2Ac=c^2-zo,\qquad 3Ac^2=c^3-cz.
\tag{1}
$$
For example, for every stage column $u$ the recurrence is
$(Au)_0=0$, $(Au)_1=\delta u_0$, and
$(Au)_{j+2}-(Au)_j=2\delta u_{j+1}$.
For the two identities in (1), substitute $u=c$ and $u=c^2$; each discrepancy is constant on either parity and the values at $0,1$ give the claimed formulas.

Put $D\coloneqq c^2-2Ac$. For $k\geq1$, the literal path identities are
$$
D^k=z^k o,\qquad A(D^k)=c z^k e.
\tag{2}
$$
Every even row reads only odd predecessors with coefficients summing to its clock; every odd row reads only even predecessors, including the origin where $D=0$. Thus (2) holds without any mesh division.

A syntactic expression formed from $\mathbf1$, $A$, linear combinations and coordinatewise products, homogeneous with $d$ occurrences of $A$ per term, expands into rooted stage columns of order $d+1$. Applying $A$ is unary grafting; coordinatewise multiplication is root join $t\mathbin{\#}u$, which adds the values of $|t|-1$ and $|u|-1$. The corresponding exact clock polynomial is obtained by replacing $A$ with integration from $0$ to the clock, starting with $1$. Indeed $\boldsymbol{\Phi}_t(A)$ has exact polynomial $x^{|t|-1}|t|/t!$, so for $d+1\leq p$ the scalar weighted order condition reads the integral of this polynomial from $0$ to $1$. This uses the syntax of the expression, not a claim that the exact polynomial descends to all equalities on actual stage columns.

The exact polynomial of $D$ is zero. Therefore through order $p$ all of the following identities are paid:
$$
\begin{aligned}
 b\cdot c^\ell&=\frac1{\ell+1} &&(0\leq\ell\leq p-1),\\
 b\cdot(c^\ell z^k o)&=0 &&(k\geq1,\;\ell\geq0,\;\ell+2k\leq p-1),\\
 b\cdot(c^\ell z^k e)&=0 &&(k\geq1,\;\ell\geq1,\;\ell+2k\leq p-1).
\end{aligned}
\tag{3}
$$
For the third line use $c^{\ell-1}\odot A(D^k)$. Notably the pure $z^k$ mask is available only on the odd part. The weights in (3) require no positivity.

## 2. Sharp chronological census

It is enough to prove the lower bound over a maximal residue field $K$ of $R$. The literal denominator-cleared order equations and the leapfrog recurrences specialize. Zero-mesh paths then evaluate only the origin and can be absorbed into its output weight. Every remaining $z=\delta^2$ is nonzero. For each distinct nonzero $z$, let $J(z)$ be the largest evaluated index on any path of that squared mesh. Define
$$
\mathcal Z_d\coloneqq\{z:J(z)\geq d\},\qquad N_d\coloneqq|\mathcal Z_d|,\qquad
Q_d(Z)\coloneqq\prod_{z\in\mathcal Z_d}(Z-z).
$$
In particular $Q_d(0)\ne0$. An odd and an even polynomial mask below have the same unmarked term at $Z=0$. A monomial $c^\ell Z^k$ in either part spends $\ell+2k$; all other terms will be among (3). At any shared physical evaluation the masked sum can be read by choosing its path representative. For the marked terms that sum is well-defined by the literal identities (2), and for the unmarked term it only uses its clock.

If $p=2r$, fix $0\leq k<r$, put $d=2k+1$, and use the pair
$$
P_E(x,Z)=xQ_d(Z)\prod_{j=1}^{k}(x^2-(2j)^2Z),\qquad
P_O(x,Z)=xQ_d(Z)\prod_{j=1}^{k}(x^2-(2j-1)^2Z).
\tag{4}
$$
Both masks vanish on their respective parity at every evaluated path site: either the mesh belongs to $\mathcal Z_d$ or the index is at most $2k$. Suppose $N_d\leq r-k-1$. Every term spends at most $1+2k+2N_d\leq p-1$, and all marked even terms have positive clock power. Applying (3) to the combined mask $eP_E+oP_O$ would give $0=Q_d(0)/(2k+2)$, a contradiction. Hence
$$
N_{2k+1}\geq r-k\qquad(0\leq k<r).
\tag{5}
$$

If $p=2r+1$, fix $0\leq k<r$, put $d=2k+2$, and use
$$
P_E(x,Z)=x^2Q_d(Z)\prod_{j=1}^{k}(x^2-(2j)^2Z),\qquad
P_O(x,Z)=Q_d(Z)\prod_{j=1}^{k+1}(x^2-(2j-1)^2Z).
\tag{6}
$$
Below index $d$, there are $k$ positive even indices but $k+1$ odd indices. The odd mask can therefore trade its $x^2$ factor for one more squared-clock factor, because pure odd marked powers are paid. If $N_d\leq r-k-1$, the spend is at most $2+2k+2N_d\leq p-1$, and (3) would give $0=Q_d(0)/(2k+3)$. Hence
$$
N_{2k+2}\geq r-k\qquad(0\leq k<r).
\tag{7}
$$

For each $z$, choose one path attaining $J(z)$. Its first $\min(J(z),p-1)$ nonorigin evaluations are distinct: the clocks $j\delta$ there are nonzero and different since $1,\ldots,p$ are units. No two such evaluations from different squared meshes can share a physical stage. In fact the cubic stage read in (1) recovers the squared mesh as
$$
z=\frac{c^3-3Ac^2}{c},
$$
using only a nonzero clock and the literal reads $c$, $Ac^2$ of that evaluation. This counting argument still permits any stage sharing consistent with equality of these rooted stage-state reads. Thus
$$
s\geq 1+\sum_{d=1}^{p-1}N_d.
$$
Monotonicity of $N_d$ and (5) give $s\geq1+r^2$ when $p=2r$; (7) gives $s\geq1+r(r+1)$ when $p=2r+1$. The case $p=1$ only requires one stage.

## 3. Exact attainment and coefficient support

For completeness, the same-parity construction can be checked on literal rooted trees. For a tree $t=[t_1,\ldots,t_m]$ of order $n$, define degree-$n$ polynomials $F_t^E,F_t^O$ with
$$
F_t^\varepsilon(X+2)-F_t^\varepsilon(X)
   =2\prod_\nu F_{t_\nu}^{\bar\varepsilon}(X+1).
$$
The even initial condition is $F_t^E(0)=0$; the odd one is
$F_t^O(1)=\prod_\nu F_{t_\nu}^E(0)$.
Each is unique: solve the polynomial difference equation from the top degree down using the paid integers and then set the constant from the indicated value. The parity of each polynomial as a polynomial in $X$ is the parity of $n$. For the even polynomial, reflect about $0$ and use uniqueness. For the odd polynomial in a nonleaf case, its right side vanishes at $X=-1$, so its values at $1,-1$ are both zero and reflection again gives uniqueness. For a leaf both polynomials are $X$. Both have leading coefficient $1/t!$, by the same top-degree recurrence. The literal recurrence gives $(A\boldsymbol{\Phi}_t)_j=\delta^{|t|}F_t^\varepsilon(j)$, including for the endpoint row used as a read rather than an extra evaluated stage.

This also proves that (3) is sufficient for arbitrary output weights on the paths. Multiply the child-state polynomials to obtain a stage column of order $|t|$. Its common leading term is $(|t|/t!)c^{|t|-1}$; all other terms on each parity have the form $c^\ell z^k$ with $k\geq1$ and $\ell+2k=|t|-1$. On even stages the child-state polynomials have zero constants, so no marked even term has $\ell=0$. The equations (3) therefore give the exact weighted output $1/t!$ for every tree through $p$.

Take every $n\in\{1,\ldots,p\}$ of the parity of $p$, and the endpoint $Y_n$ of the mesh $1/n$. For each $t$ through order $p$, its output is a polynomial in $z_n=1/n^2$ with constant $1/t!$. For odd $p$, parity gives degree at most $\lfloor |t|/2\rfloor\leq (p-1)/2$; for even $p$, $F_t^E(0)=0$ improves this to $\lfloor (|t|-1)/2\rfloor\leq (p-2)/2$. The endpoint parity is fixed across all levels, so each such polynomial is common across the branches and has degree below their number. Lagrange weights $\lambda_n=\prod_{m\ne n}z_m/(z_m-z_n)$ give the evaluation at $z=0$. Their denominators are paid: $m,n$ are paid and distinct same-parity levels have $m^2-n^2=4((m-n)/2)((m+n)/2)$, with both nonzero integer halves of magnitude at most $p$. This establishes all rooted conditions over $\mathbb Z[1/p!]$, hence universally over $R$.

There are $1+\sum_n(n-1)=1+\lfloor p^2/4\rfloor$ evaluations. In this witness, branches share only the origin, so a causal chain has at most $p$ vertices and $A^p\mathbf1=0$. The next tall tree has cleared defect $(p+1)!\,b\cdot A^p\mathbf1-1=-1$, with no need to invert $p+1$. At $p=9$ the levels are $1,3,5,7,9$: the nonorigin counts are $0,2,4,6,8$, and $\mathbb Z[1/9!]=\mathbb Z[1/210]$.
