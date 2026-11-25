# The weighted transpose is an involution on the attained full-weight chart

Use the notation, hypotheses, and exact flags of the [causal profile reduction](README.md). Thus $B=zA$ is lower triangular with nonzero diagonal, $(p,n)=(7,8)$ or $(8,10)$, every $b_i\ne0$, and the full rooted-tree order is $p$ or greater. Write $D_b=\operatorname{diag}(b)$ and $J$ for index reversal. Then
$$
 (B,b)\ \longmapsto\ (J D_b^{-1} B^{\mathsf T} D_b J,\ Jb)
$$
is an **order-preserving involution on this chart**. Under the natural label identification it preserves every paid elementary and defect space. It need not fix the individual tableau. This theorem is not a claim about the raw transpose of an arbitrary Runge–Kutta method; the exact dual flags and nonzero individual weights are used essentially in this proof.

**Proof.** Work before the permutation $J$, set $B^\dagger=D_b^{-1} B^{\mathsf T}D_b$, and use the nondegenerate pairing $\langle u,v\rangle=u^{\mathsf T}D_bv$. For $0\le k\le p-1$ one has $F_k=E_{p-1-k}^{\perp}$; this also holds at $k=0,1$ since $F_0=F_1=0$ and the two complementary elementary spaces are full. D1 gives $B^\dagger\mathbf1=\bar x=z\mathbf1-x$. The operator $B^\dagger$ advances every $F_k$ to $F_{k+1}$: pair against $E_{p-2-k}$ and apply the ordinary $B$ advance on the other side. Multiplication by $\bar x$ advances $F$ as well, since it is the difference of scalar multiplication by $z$ and the original clock advance. All affordable products of defects retain their original closure.

For $1\le m\le p-1$ we claim
$$
 h_m=m B^\dagger x^{m-1}-(z^m\mathbf1-x^m)\ \in F_m.
$$
It suffices to test against $E_r$ for $r=p-1-m$. Its $F_r$ component pairs to zero: $BF_r\subset F_{r+1}$, and the terms paired with it have affordable clock costs. For its pure powers $x^j$, $0\le j\le\min(r,p-1-r)$, the paid identity $(j+1)Bx^j-x^{j+1}\in F_{j+1}$ gives
$$
 m\langle x^{m-1},Bx^j\rangle
 =\frac{m z^{j+m}}{(j+1)(j+m+1)}
 =\langle z^m\mathbf1-x^m,x^j\rangle .
$$
For $j=0$ this primitive is exactly $B\mathbf1=x$. The two casts in the denominator are units. This proves the claim by duality. Expanding $(z-x)^{m-1}$ and using $\tfrac{m}{j+1}\binom{m-1}{j}=\binom{m}{j+1}$ shows
$$
 mB^\dagger\bar x^{m-1}-\bar x^m
 =\sum_{j=0}^{m-1}(-1)^j\binom{m}{j+1}z^{m-1-j}h_{j+1}\in F_m .
$$
The reflected quadrature is $\beta\bar x^r=z^r/(r+1)$ for $0\le r<p$, by the binomial identity $\sum_{j=0}^r(-1)^j\binom rj/(j+1)=1/(r+1)$. Each $F_k$ has zero output. Thus the very same normalized tree recursion as in the [weighted profile theorem](../weighted-profile-reduction.md) places the difference between every reflected normalized elementary column of grade $k$ and $\bar x^k$ in $F_k$. This proves the complete order, not just the orders of chains.

The new actual defect space of grade $k$ is contained in $F_k$ by subtracting equal-grade normalized columns. The new elementary space is contained in $E_k$ since $\bar x^j$ is a polynomial in $x$ of degree $j$ and $F_j\subset E_j$. After reversal the new tableau is again lower triangular, nonsingular, and at the same stage floor. The exact ranks are therefore the same, so the two inclusions are equalities. Finally the second weighted transpose restores $B$, since its weight diagonal is transported by $J$. This proves the involution.

**An order-seven symmetry obstruction.** Suppose the order-seven attained tableau on eight stages is fixed by the involution (this is a separate assumption). Then $Jb=b$, $Jx=z\mathbf1-x$ and $Js=\lambda s$ for $\lambda^2=1$, since the one-dimensional $F_2=K s$ is invariant under reversal. In fact on $F_3$ there is one symmetric and one antisymmetric direction. Reversal has two orthogonal four-dimensional eigenspaces since the characteristic is not two and the weight diagonal is symmetric. Now $F_3=E_3^\perp$ while
$$
 E_3=F_3\oplus\operatorname{span}\{\mathbf1,x,x^2,x^3\}.
$$
The pure space has two dimensions of each sign (center at $z/2$); dimension in either reversal eigenspace gives $4=2+2\dim F_3^\pm$.

If there are exactly four physical clock groups, the four-pair alternative in the [weighted profile theorem](../weighted-profile-reduction.md) is impossible on this symmetric chart. Put $P(X)=\prod_g(X-\xi_g)$ for the four clocks, and $m_g=\sum_{i:x_i=\xi_g}b_i s_i^2$. Reflection makes $m_{z-\xi}=m_\xi$. On the other hand $P(z-X)=P(X)$ makes $P'(z-\xi)=-P'(\xi)$, whereas the paid order-seven moments give $m_\xi=\eta/P'(\xi)$. Hence every $m_g=0$. For the common-diagonal strict chart the endpoint groups must consequently be triples and the other two groups singletons, not four pairs. Here $b_0\ne0$ already follows from the full-weight hypothesis. For arbitrary prescribed nonzero diagonals the conclusion $m_g=0$ remains valid; no endpoint multiplicities without the original endpoint guards are asserted.

In the strict common-diagonal case one can also locate the second and penultimate stages. Normalize the diagonal to one and set $u=x_1-1\ne0$, $\kappa=1+2u-u^2=s_1$. From the equal-initial-diagonal formula $Bs=-t$, the two independent columns $s$ and $\tau=(B-I)s$ span $F_3$; they start with $(1,\kappa)$ and $(0,u)$. Since $Cs\in F_3$, its first two values force $Cs=s+\kappa\tau$. If $\kappa=0$, the nonzero entries of $s$ would all be on $x=1$. This includes the last stage since $Js=\lambda s$. The last-clock formula then gives $z=2$, placing $x_0=1$ at the midpoint, which is not a four-clock node by the original quadrature lemma. Hence $s_1\ne0$. Both singleton clocks have seed zero from the four paid first-seed moments, while $x_1\ne x_0$. Consequently $x_1=x_{n-1}$ and, by reflection, $x_{n-2}=x_0$.

Independently of the equal-diagonal assumption, these four clocks must be the four Gaussian clocks. The monic $P$ is orthogonal to $1,X,X^2$ by order-seven quadrature. It is a linear combination of the scaled shifted Legendre columns $L_4,L_3$ given in the weighted profile theorem. The first is even and the second odd about $z/2$, so symmetry gives $P=L_4/70$. Equivalently $u=2\xi/z-1$ satisfies $35u^4-30u^2+3=0$. Consequently $((35u^2-15)/2)^2=30$; over a field in which 30 is not a square, including $\mathbb Q$, the symmetric four-clock chart is empty. The arguments for the barycentric and polynomial conclusions actually require only reflected clock/weight data with reflected seed squares, not an a priori fixed tableau. None asserts absence of nonsymmetric methods or a new unrestricted stage floor.

The [exact arithmetic checker](check-reflection.py) verifies the primitive binomial identities and the Legendre, radical, and barycentric formulas independently. It is a fixture check, not a proof of attainment or a Lean verification.
