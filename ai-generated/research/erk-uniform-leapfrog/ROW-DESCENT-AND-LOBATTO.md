# ERK9 denominator descent: one-row criterion and a source-chart obstruction

No sub-21-stage tableau is certified by this note. Two scoped results identify when a high-order rational chart can be transferred and when its clock architecture cannot be retained.

## 1. Sharp local affine-row transfer

Write $U\coloneqq\mathbb Z[1/p!]$ and let an explicit prefix be defined over $U$. Suppose one rational stage row has the form $r_0+\theta v$, where $r_0,v$ are causal rows on that prefix over $U$, $\theta\in\mathbb Q$, and
$$
v\cdot\boldsymbol{\Phi}_u(A)=0\qquad(|u|<q).
$$
A stage evaluated at row $r_0+xv$ has tree sample
$$
P_t(x)\coloneqq\prod_{u\text{ a root child of }t}
  \bigl(r_0\cdot\boldsymbol{\Phi}_u(A)+x\,v\cdot\boldsymbol{\Phi}_u(A)\bigr).
$$
The product includes child multiplicity. Consequently $\deg P_t\leq\lfloor (|t|-1)/q\rfloor$. Suppose a consumer with original coefficient $g\in\mathbb Q$ needs the scaled old samples $gP_t(\theta)$ through order $a\leq p$; put $D=\lfloor(a-1)/q\rfloor$. Later internal rows can use $a=p-1$ for preserving order $p$, while a direct output component uses $a=p$.

If $g\theta^m\in U$ for $0\leq m\leq D$, replace the old stage by rows $r_0+jv$ for $j=0,\ldots,D$, whose incoming data depend only on the frozen prefix. Set the consumer coefficients to $gL_j(\theta)$, where $L_j$ are the Lagrange basis at $0,\ldots,D$. These are in $U$, since $L_j\in U[X]$. They give exactly the desired scaled samples. With multiple consumers one can retain the common list up to the maximum needed $D$, using the shorter interpolation rule padded by zero for lower-budget consumers. The new rows can be placed consecutively at the original stage location; induction on tree order in the later tableau then gives the old full outputs through $p$. This is a local replacement theorem, not a necessary condition for coordinated edits involving other rows or redistribution among other consumer columns.

Conversely suppose $|u|=q$ and $\beta\coloneqq v\cdot\boldsymbol{\Phi}_u(A)$ is a unit in $U$. For the root with $m$ copies of $u$, the sample is $(\alpha+\beta x)^m$ with $\alpha\coloneqq r_0\cdot\boldsymbol{\Phi}_u(A)$ and order $mq+1$. Matching these samples by paid donor rows forces $g(\alpha+\beta\theta)^m\in U$ for $m\leq D$; binomial inversion in $\alpha+\beta\theta$ forces $g\theta^m\in U$. For an unpaid prime $\ell$, a pole of order $e$ in $\theta$ must thus be cancelled to order at least $De$ by $g$. For that single-prime obstruction it is enough that $\beta$ be an $\ell$-adic unit. Also $D+1$ donors on this affine line are necessary if $g\ne0$, $\theta\notin U$, and $\beta\ne0$: the $m$-copy samples determine moments through $D$ over $\mathbb Q$; any $D$ or fewer distinct paid donor parameters would be annihilated by their monic node polynomial, which does not vanish at $\theta$.

In particular, a size-four first action can be affine through output order eight but is quadratic at order nine, because $[u,u]$ has nine vertices. A single unpaid-prime cancellation in $g$ does not suffice when $\theta$ has a simple pole and that size-four action is an $\ell$-adic unit. Adding more clones on the same affine line does not repair the pole.

**Unit order-ten exactifier for a qualifying size-three row.** Let $p=9$, $q=3$, and $\beta\in U^\times$ as above. The first three donor rows $r_0+jv$, $j=0,1,2$, suffice for the paid transport if its valuation test is met. Include also $j=3$ (or reuse it if available). Vary the output weights on these four rows by $\eta(-1,3,-3,1)$, leaving all other weights and the tableau fixed. Every output through nine is unchanged because every affected sample has degree at most two. For the order-ten tree $\tau=[u,u,u]$, the change of raw output is $3!\eta\beta^3$. Choose $\eta=-(b\cdot\boldsymbol{\Phi}_\tau(A))/(3!\beta^3)\in U$; the new raw output at $\tau$ is zero, with cleared defect $-1$. Thus a rational order-at-least-nine source of at most 17 stages with one qualifying bad row and the remaining coefficients paid would yield an exact all-ring order-nine tableau with at most 20 stages. No particular source is claimed to meet these hypotheses.

## 2. A six-clock mirror Lobatto source cannot be descended by a one-clock extension

Misha Stepanov's [*On Runge–Kutta methods of order 10*, §5](https://arxiv.org/html/2504.17329v2#S5) gives an exact 15-stage ERK family with six quadrature clocks: the endpoints and four inner Lobatto nodes in reflected pairs. This serves here only as the precise source architecture. Dropping the order-ten requirement does not make its six-clock shape rational.

Indeed any rational order-nine RK quadrature supported in
$\xi\in\{\pm1,\pm u,\pm v\}$ for $\xi=2c-1$ must integrate all polynomials of degree at most eight. Neither mirrored weights nor any positivity are assumed. Set $s=\xi^2$ and write $\mathcal L(s^j)=1/(2j+1)$. With $S=u^2+v^2$, $P=u^2v^2$, the polynomial $G(s)=(s-1)(s-u^2)(s-v^2)$ vanishes on the support. Thus $\mathcal L(G)=\mathcal L(sG)=0$, which give
$$
S-5P=3/7,\qquad 3S-7P=5/3.
$$
Therefore $S=2/3$ and $P=1/21$, not a rational square, contrary to $P=(uv)^2$.

One additional arbitrary clock does not suffice within this skeleton. If the new $\xi=w$ is not zero and not already in the six-clock set, the odd polynomial
$\xi(\xi^2-1)(\xi^2-u^2)(\xi^2-v^2)$ has degree seven and vanishing exact integral. It isolates the new clock and forces its grouped weight to vanish. If $w=0$, the necessary identity is instead $\mathcal L(sG(s))=0$, namely
$$
9(u^2+v^2)-21u^2v^2=5.
\tag{*}
$$
This has no solution in $\mathbb Q_3$. If both valuations of $u,v$ are nonnegative then the left side is divisible by $3$. Otherwise let $a=\nu_3(u)<0$ and assume $a\le b=\nu_3(v)$. If $b\le0$, the product term has strictly smallest valuation $1+2a+2b<0$. If $b\ge1$, including the possibility $v=0$, the $9u^2$ term has strictly smallest valuation $2+2a$; valuation zero would force $a=-1$, in which case the left side is $1\pmod3$ whereas the right is $2\pmod3$. This also handles all degeneracies with zero or repeated original nodes.

Thus even allowing arbitrary grouped weights, a rational method that preserves the old mirrored endpoint-pair skeleton must introduce at least two other distinct weighted clocks (or change the skeleton). Same-clock row splitting alone cannot repair this, independently of the transfer criterion. The conclusion does not bound general order-nine widths, does not rule out changing old clock partners, and gives no purported descent of Fehlberg's distinct architecture. Fehlberg's [NASA TR R-287, §§XVII–XVIII, (145) and Table XII](https://ntrs.nasa.gov/api/citations/19680027281/downloads/19680027281.pdf) gives a different exact parameter construction with printed decimal example, not a pinned specialization over $U$ for the local criterion above.
