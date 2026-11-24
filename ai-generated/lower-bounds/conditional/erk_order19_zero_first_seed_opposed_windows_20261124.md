# Opposed polynomial windows at order 19

This note proves a scalar incompatibility for a quintic observed at four physical clocks. It then identifies the scalar data furnished by the zero-first-seed geometry of a strictly explicit, 29-stage Runge–Kutta tableau of order at least 19. The proof works over every ordered field. It does not require positive Runge–Kutta weights, a numerical ordering of the clocks in stage order, or a Jacobi polynomial calculation.

## Formal moments and alternating signs

Let $K$ be an ordered field. For $G(X)=\sum_j g_jX^j$, write

$$
\mathcal P G(X)=\sum_j\frac{g_j}{j+1}X^{j+1},\qquad
I_{l,r}(G)=(\mathcal P G)(r)-(\mathcal P G)(l).
$$

These are polynomial operations. Differentiation and the constant term give the affine substitution identity

$$
I_{l,r}(G)=(r-l)I_{0,1}\bigl(G(l+(r-l)X)\bigr).
$$

An *alternation* of a polynomial on an open interval is a change between opposite nonzero signs at successive members of an increasing list of sample points in the interval. Zero evaluations are discarded. If $G\ne0$, any such list has at most $\deg G$ alternations. Indeed, from a list with $m$ alternations one can select $m+1$ increasing points $x_0<\cdots<x_m$ with alternating nonzero values. If $m>\deg G$, Lagrange interpolation gives

$$
0=[X^m]G=\sum_{i=0}^m\frac{G(x_i)}{\prod_{j\ne i}(x_i-x_j)}.
$$

The denominator in the $i$th summand has sign $(-1)^{m-i}$. The summands are nonzero and all have the same sign, a contradiction. Alternations witnessed in disjoint open intervals in increasing order can be added: concatenate the lists and keep their internal sign changes.

**Positive rational grid.** For each degree bound $M$, there is a finite quadrature rule with strictly positive rational weights and more than $M$ distinct rational nodes in $(0,1)$, exact for $I_{0,1}$ through degree $M$. Here is a construction. Choose the $M+1$ rational anchors

$$
r_i=\frac{2i+1}{2(M+1)},\qquad 0\le i\le M,
$$

and their cardinal Lagrange polynomials $L_i$. Take the uniform $N$-cell midpoint rule $Q_N$, where $N$ is an odd multiple of $M+1$. Every anchor is one of its midpoints. Add the correction $I_{0,1}(L_i)-Q_N(L_i)$ to the weight at $r_i$. Exactness through degree $M$ follows by interpolating the tested polynomial at the anchors.

For a fixed rational polynomial $L$, the midpoint error has absolute value at most $C_L/N^2$, with $C_L=\sum_j |[X^j]L|2^j$. To see this, expand $L$ around each midpoint. The constant term gives the midpoint rule, the linear term integrates to zero, and a term of degree $k\ge2$ has moment of absolute value at most $N^{-k-1}\le N^{-3}$. The sum of the absolute values of all coefficients of the translated polynomial is bounded by $C_L$, because each midpoint lies in $[0,1]$. Sum over the $N$ cells. Taking $N$ greater than all the $C_{L_i}$ makes every corrected weight larger than zero. All operations in this construction take place over $\mathbb Q$. Casting its monomial identities into $K$ and using affine substitution gives an exact positive grid on every interval $l<r$ in $K$.

The repository also gives [a fixed rational rule exact through degree 19](positive_rational_rule_degree19_20261124.json).

The following two consequences use the same grid for all tests on a fixed interval. Its degree bound may be chosen to cover their integrands and its node count to exceed the degree of the polynomial being sampled.

1. **One weight.** Suppose $U>0$ on $(l,r)$, $G\ne0$, and $I_{l,r}(UGT)=0$ for every polynomial $T$ of degree less than $m$. Then $G$ has at least $m$ alternations in $(l,r)$. Otherwise choose one separator between successive nonzero sample values at each sign change. The product of the corresponding linear factors, with its sign chosen suitably, has degree less than $m$ and makes $GT$ positive at every nonzero sample of $G$. At least one sample is nonzero, by the degree and node count. The exact positive weighted sum is then positive, contradicting the moment equation. A weight of constant negative sign is handled by negation.
2. **Two weights.** Suppose $U,V>0$ on $(l,r)$, $U/V$ is strictly monotone there, $G\ne0$, and $I_{l,r}(UG)=I_{l,r}(VG)=0$. Then $G$ has at least two alternations there. No alternation contradicts the moment with weight $V$. If there is exactly one, choose $t$ between the last nonzero sample of the first sign and the first of the opposite sign. Put $\lambda=U(t)/V(t)$. The polynomial $G(U-\lambda V)$ has the same strict sign at every nonzero sample of $G$, because the ratio is strictly monotone. Its exact positive sum is nonzero, whereas linearity gives moment zero.

Neither argument infers the existence of a root between two samples. The use of alternating signs, rather than roots, is what allows an arbitrary ordered coefficient field.

## The opposed-window theorem

Let $P\in K[X]$ have degree five, and let $a,b,c,d$ be distinct elements of $K\setminus\{0,1\}$ with $P(a)P(b)P(c)P(d)\ne0$. Define

$$
\begin{aligned}
N&=(X-a)(X-b)(X-c)(X-d),& D&=PN,\\
L_1&=X,& R_1&=1-X,\\
L_2&=X(X-a),& R_2&=(1-X)(X-d),\\
L_3&=X(X-a)(X-b),& R_3&=(1-X)(X-d)(X-c).
\end{aligned}
$$

**Theorem.** For either $e=0$ or $e=1$, the following equations are incompatible:

$$
\begin{array}{lll}
I_{0,a}(L_1PX^k)=0 & (0\le k\le2), & I_{d,1}(R_1PX^k)=0\quad(0\le k\le2),\\
I_{0,b}(L_2PX^k)=0 & (0\le k\le1), & I_{c,1}(R_2PX^k)=0\quad(0\le k\le1),\\
I_{0,c}(L_3P)=0, && I_{b,1}(R_3P)=0,\\[2pt]
I_{0,1}((1-X)X^eDX^k)=0 & (0\le k<9-e).&
\end{array}
$$

All integrands in these equations have degree at most 18. The statements with $X^k$ allow arbitrary polynomial tests of the same degree by linearity.

### Exterior clocks

The last line, with the positive weight $(1-X)X^e$ on $(0,1)$, supplies at least $9-e$ alternations of $D$ in $(0,1)$. Every clock $t\in\{a,b,c,d\}$ outside $(0,1)$ supplies one further alternation arbitrarily close to $t$. In fact $D=(X-t)B$ with $B(t)\ne0$. To check the local sign algebraically, write $B(X)-B(t)=(X-t)T(X)$. On $|x-t|\le1$, the absolute value of $T(x)$ is bounded by $\sum_j |[X^j]T|(|t|+1)^j$. At points sufficiently close to $t$, this bound shows that $B(x)$ has the sign of $B(t)$. Thus $D$ has opposite signs on the two sides of $t$. The neighborhoods can be taken disjoint and outside $[0,1]$, since none of the clocks equals an endpoint. As $\deg D=9$, there are no exterior clocks for $e=0$ and at most one for $e=1$.

The primitive of $L_3P$ has equal values at $0,a,b,c$. At $a$ this uses the $L_1$ test $(X-a)(X-b)$; at $b$ it uses the $L_2$ test $X-b$. Likewise the primitive of $R_3P$ has equal values at $b,c,d,1$, using the $R_1$ test $(X-d)(X-c)$ and the $R_2$ test $X-c$.

If the one exterior clock $t$ is negative and belongs to $\{a,b,c\}$, the $L_3$ moment on $(t,0)$ vanishes and its weight has constant strict sign there. Thus $P$ has an alternation in that interval. The polynomial $N$ has constant strict sign there, so $D$ has that alternation too. The alternation of $D$ across $t$ can be witnessed closer to $t$ than the two samples in $(t,0)$. These are two independent exterior alternations, in addition to the eight in $(0,1)$, which is impossible. The same argument with $R_3$ on $(1,t)$ excludes an exterior clock $t>1$ in $\{b,c,d\}$. Consequently, in both layouts,

$$
a>0,\qquad d<1,\qquad 0<b<1,\qquad 0<c<1.
$$

The only possible exterior clocks left are $a>1$ or $d<0$. The middle interval used below does not reach either one.

### The middle interval

The $L_1$ tests give three alternations of $P$ in $(0,a)$, and the $R_1$ tests give three in $(d,1)$. Each affine moment of $L_2P$ vanishes on both consecutive intervals in the sorted set $\{0,a,b\}$: its primitive also vanishes at $a$ by the $L_1$ tests. The weight has constant strict sign on each of the two open intervals. Thus each supplies two alternations. The $R_2$ tests likewise give two alternations on each consecutive open interval in $\{d,c,1\}$. The equal primitive values for $L_3P$ and $R_3P$ give one alternation on each consecutive open interval in their respective four-element endpoint sets. In each case the roots of the mask are among the endpoints and never lie in a consecutive open interval.

If $a<b$, the three alternations in $(0,a)$ and the two in $(a,b)$ account for five below $b$. The rightmost $R_3$ interval, $(\max(b,c,d),1)$, contributes one more. This contradicts degree five, so $b<a$. If $c<d$, the three in $(d,1)$ and the two in $(c,d)$ give five above $c$, and the leftmost $L_3$ interval contributes a sixth. Hence $d<c$.

Now $b\le d$ would give two alternations in $(0,b)$ and four in the disjoint intervals $(d,c)$ and $(c,1)$. Similarly, $c\ge a$ would give four in $(0,b)$ and $(b,a)$ and two in $(c,1)$. We conclude that both $b$ and $c$ lie strictly between $d$ and $a$.

Both $L_3P$ and $R_3P$ have zero moment on the open interval between $b$ and $c$. Choose their weight signs to give positive weights $U$ and $V$ on that interval. If $b<x<c$, their ratio is

$$
\frac{U(x)}{V(x)}
=\frac{x}{1-x}\frac{x-b}{x-d}\frac{a-x}{c-x}.
$$

Every factor is positive and strictly increasing: the last two are $1-(b-d)/(x-d)$ and $1+(a-c)/(c-x)$, respectively. If instead $c<x<b$, the ratio is

$$
\frac{U(x)}{V(x)}
=\frac{x}{x-c}\frac{b-x}{1-x}\frac{a-x}{x-d}.
$$

Here all three factors are positive and strictly decreasing, as can be seen from $1+c/(x-c)$, $1-(1-b)/(1-x)$, and $(a-d)/(x-d)-1$. These comparisons use only ordered field arithmetic. The two-weight result therefore gives two alternations in the middle interval. When $b<c$, add the two in $(0,b)$ and the two in $(c,1)$. When $c<b$, add the two in $(d,c)$ and the two in $(b,a)$. Either way $P$ has at least six alternations, contrary to degree five. This proves the theorem.

## Physical input at width 29

Let $A$ be strictly lower triangular on the original indices $0,\ldots,28$, let $w$ be the output weights, and assume the reviewed all-tree condition `HasOrder 19 A w`. Set $c_i=\sum_j A_{ij}$ and $y_i=1-c_i$. The first and quadratic reflected adjoint seeds are the actual vectors

$$
D_1=A^\mathsf T w-yw,\qquad D_2=2A^\mathsf T(yw)-y^2w,
$$

where products of stage vectors are coordinatewise. Assume $D_1=0$. The zero-seed geometry supplies a quintic $Q$, a polynomial $E$ of degree at most four, the reflected quintic $P(X)=Q(1-X)$, and the actual contrast and forward correction

$$
W_i=y_iw_iQ(y_i)-(D_2)_iE(y_i),\qquad \theta_i.
$$

The following lists the geometric inputs used here. They are the assertions of `Width29ZeroHead`, `Width29ForwardPorts`, and `Width29OriginSplit`, together with the reverse identity used by `Width29ZeroHead.port_of_later_mask`.

* At every row with $W_i\ne0$, one has $(D_2)_i=0$, $y_iw_iQ(y_i)\ne0$, and hence $P(c_i)\ne0$ and $c_i\ne1$. The terminal row $28$ has $W_{28}=0$. The correction $\theta$ is supported on the active contrast rows together with the original origin and terminal; $c_0=0$.
* Either there are exactly four active contrast rows, with distinct clocks and $W_0=0$, or there are exactly five, with distinct clocks and $W_0\ne0$. In the latter layout the other four rows cannot have clock zero. In the four-row layout the checked endpoint moment lemma `x_nodal_paid_moments_exclude_one`, applied to `Width29ZeroHead.four_site_orthogonal`, excludes reflected clock $1$ on the contrast, and hence forward clock zero on those four rows.
* For every row with $W_i\ne0$ and every $T$ of degree at most three,
  $$
  \sum_j A_{ij}\theta_j T(c_j)=I_{0,c_i}(TP).
  $$
  At the same row, for every $S$ of degree at most two, the reverse formula is
  $$
  \sum_j A_{ji}W_j S(y_j)=w_i I_{0,y_i}(SXQ).
  $$
  The latter uses the actual terminal-zero grade-nine annihilator cover. It makes no claim about a higher forward grade or a reversed tableau satisfying independent order conditions.
* For every $T$ of degree at most twelve,
  $$
  I_{0,1}(T(1-X)P)=\sum_i W_iT(c_i).
  $$

Order the four active contrast rows other than the original origin by their stage indices, and call their clocks $a,b,c,d$ in that chronological order. Set $e=0$ in the four-row layout and $e=1$ in the five-row layout. The clocks now satisfy all the point and nonvanishing assumptions of the scalar theorem.

For the three forward observations, at clocks $a,b,c$ use the multipliers $X R$, $X(X-a)R$, and $X(X-a)(X-b)$, respectively, where $\deg R\le2$ in the first and $\deg R\le1$ in the second. The factor $X$ kills the possible origin correction. The other factors kill the required earlier contrast rows, and the terminal is never earlier. Strict lower triangularity then makes the three forward sums zero. These are exactly the left three-plus-two-plus-one equations.

For the reverse observations at clocks $d,c,b$, first choose the forward-coordinate multipliers $R$, $(X-d)R$, and $(X-d)(X-c)$, respectively. Their reflected versions $S(Y)=T(1-Y)$ have degree at most two and kill, respectively, no later contrast rows, the last one, or the last two. If the origin is active it is earlier, not later. Strict transpose causality gives a zero sum. Cancel the nonzero $w_i$ in the reverse formula and reflect the primitive using

$$
I_{0,1-x}\bigl(B(1-X)\bigr)=I_{x,1}(B),
$$

which follows by differentiating $(\mathcal P B)(1)-(\mathcal P B)(1-X)$ and checking its zero constant term. Taking $B=T(1-X)P$ gives exactly the right three-plus-two-plus-one equations, with the same quintic $P$ as on the forward side.

Finally, take $T=X^kX^eN$ in the global formula, for $0\le k<9-e$. The degree of this multiplier is at most twelve. The nodal factors kill the four non-origin contrast rows, and the factor $X$ in the $e=1$ layout kills the active origin. Thus the global moments are exactly the last line of the scalar theorem.

The opposed-window theorem excludes these physical data. This proves the zero-first-seed width-29 exclusion from the stated geometry; it does not address the case $D_1\ne0$. The geometric inputs were separately checked on the earlier reviewed Lean interface. This note is the mathematical proof of their scalar consequence, not a claim that the combined endpoint has been kernel-checked on the current interface.
