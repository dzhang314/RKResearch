# A decorated-path obstruction to common-diagonal RK saturation

**Theorem.** Over a field of characteristic zero, a triangular Runge–Kutta tableau with a common physical diagonal and order at least $p\ge 5$ has at least $p$ stages. More precisely, a common-diagonal tableau with $s\ge 4$ stages cannot pay every rooted condition through $s+1$. No stability, sign, or support assumption beyond triangularity is used.

## Scalar cap

Define \(\mathbf c\coloneqq A\mathbf 1\) and \(B\coloneqq A-\gamma I\), where \(\gamma\) is the common diagonal. The Butcher weight vectors satisfy \(\boldsymbol{\Phi}_{\bullet}(A)=\mathbf 1\), \(\boldsymbol{\Phi}_{[t]}(A)=A\boldsymbol{\Phi}_t(A)\), and \(\boldsymbol{\Phi}_{t\#u}(A)=\boldsymbol{\Phi}_t(A)\odot\boldsymbol{\Phi}_u(A)\). Let $\mathcal I$ denote formal polynomial integration from $0$ to $x$, and define
$$
J\coloneqq\mathcal I-\gamma\,\operatorname{id},\qquad
\ell(f)\coloneqq\int_0^1 f(x)\,dx,\qquad
\lambda_n\coloneqq\ell(J^n1)
=\sum_{j=0}^n\binom nj\frac{(-\gamma)^{n-j}}{(j+1)!}.
$$
For $n+1\le p$ the literal tall conditions give $\mathbf b\cdot B^n\mathbf 1=\lambda_n$, by expanding $B^n$ in powers of $A$. The generating function $\Lambda(z)=\sum_{n\ge0}\lambda_nz^n$ satisfies
$$
z\Lambda(z)=\exp\!\left(\frac{z}{1+\gamma z}\right)-1,\qquad
(1+\gamma z)^2(z\Lambda)'=1+z\Lambda.
$$
The first identity follows by summing the binomial expression above; coefficients of the second give $\lambda_0=1$ and
$$
(n+2)\lambda_{n+1}
=(1-2(n+1)\gamma)\lambda_n-n\gamma^2\lambda_{n-1}
\qquad (n\ge1).
\qquad (1)
$$
Since $B$ is strictly lower triangular, $B^s=0$. If $\gamma=0$, paying the tall tree of size $s+1$ would give $0=\lambda_s=1/(s+1)!$. If $\gamma\ne0$, paying through $s+2$ would give two consecutive zeros $\lambda_s=\lambda_{s+1}=0$, and (1) would descend to $\lambda_0=0$. Thus the scalar cap for nonzero $\gamma$ is $p\le s+1$.

Assume from now on $s\ge4$, $\gamma\ne0$, and full rooted payment through $s+1$. Then $\lambda_s=0$ and $L\coloneqq\lambda_{s-1}\ne0$ by (1). A length-$s-1$ strict path must visit all $s$ stages in order, so
$$
L=\mathbf b\cdot B^{s-1}\mathbf 1=b_s\prod_{j=2}^s B_{j,j-1}.
\qquad (2)
$$
In particular, this is an actual nonzero physical path.

## One clock on the full path

Let $C=\operatorname{diag}(\mathbf c)$ and let $M$ multiply polynomials by $x$. For **each** physical stage $1\le i\le s$, use the word
$$
\mathbf b\cdot B^{s-i} C B^{i-1}\mathbf 1.
\qquad (3)
$$
In the backwards path from output stage $s$, the first $s-i$ hops reach stage $i$, and the last $i-1$ go from $i$ to stage $1$. Hence (2) shows that (3) is exactly $Lc_i$.

The word is also literally paid. After expanding its two powers of $B$, a term is $\mathbf b\cdot A^u(\mathbf c\odot A^v\mathbf 1)$, where $u\le s-i$, $v\le i-1$, and $\odot$ is componentwise multiplication. For $v=0$ the inner stage vector is the two-vertex tree. For $v\ge1$ it is the tree whose root has a leaf child and a tall child with $v$ vertices. Adding $u$ unary ancestors gives size $u+v+2\le s+1$. In either case the reciprocal tree factorial is $(v+1)/(u+v+2)!$, exactly $\ell(\mathcal I^u M\mathcal I^v1)$. Summing the two binomial expansions gives $\ell(J^{s-i}MJ^{i-1}1)$ as the target of (3).

The commutator has sign
$$
MJ-JM=M\mathcal I-\mathcal I M=\mathcal I^2:
$$
on a monomial $x^k$ the difference is $x^{k+2}(1/(k+1)-1/(k+2))$. Since $\mathcal I^2$ commutes with $J$, moving $M$ to the right in (3)'s target yields
$$
J^{s-i}MJ^{i-1}=J^{s-1}M+(i-1)J^{s-2}\mathcal I^2 ;
$$
for $i=1$ the second term is absent. Use $M1=x=\mathcal I1$ and $\mathcal I=J+\gamma\,\operatorname{id}$ to obtain
$$
Lc_i
=\lambda_s+\gamma L
 +(i-1)(\lambda_s+2\gamma L+\gamma^2\lambda_{s-2}).
$$
Thus the actual clocks are in arithmetic progression:
$$
c_i=\gamma+(i-1)a,\qquad
a=2\gamma+\frac{\gamma^2\lambda_{s-2}}L
  =\frac{1-2\gamma}{s-1}.
\qquad (4)
$$
The last equality is (1) at $n=s-1$. In particular $a=c_2-\gamma=B_{21}\ne0$ by (2).

## The paid three-point polynomial

Put $h=s-3$, $w=\mathbf b\cdot B^h$ and $d=\mathbf c-\gamma\mathbf 1$, with powers of $d$ taken componentwise. Chronology restricts $w$ to the first three coordinates. By (4) their values of $d$ are $0,a,2a$, so for $M_j\coloneqq w d^j$,
$$
M_3-3aM_2+2a^2M_1=0.
\qquad (5)
$$
This uses only paid bush tests. A bush with $j$ leaves below $k$ unary ancestors has size $k+j+1$ and output $j!/(k+j+1)!$. Expanding $w$ in powers of $A$ thus gives $w\mathbf c^{\odot j}=j!w A^j\mathbf 1$ for $j\le3$: the largest tree has size $h+4=s+1$. Expanding $d=\mathbf c-\gamma\mathbf 1$ and $A=B+\gamma I$, and using $\lambda_s=0$, gives
$$
\begin{aligned}
M_1&=\lambda_{s-2},\\
M_2&=\gamma^2\lambda_{s-3}+2\gamma\lambda_{s-2}+2L,\\
M_3&=2\gamma^3\lambda_{s-3}+9\gamma^2\lambda_{s-2}+12\gamma L.
\end{aligned}
$$
Write $t=a/\gamma$, $v=\gamma\lambda_{s-2}/L=t-2$, and $Q=\gamma^2\lambda_{s-3}/L$. By (1) at $n=s-2$ and $1/\gamma=2+(s-1)t$,
$$
(s-2)Q=(s-1)v^2+2v-s.
$$
Divide (5) by $\gamma L$ to get
$(2-3t)Q+(9-6t+2t^2)v+12-6t=0$.
Substituting $v=t-2$ and the expression for $Q$ gives the nonzero rational cubic
$$
(s+1)t^3-4s t^2+2(s-3)t+4=0,\qquad
t=\frac{1/\gamma-2}{s-1}.
\qquad (6)
$$

## Incompatibility

The paid tall equality $\lambda_s=0$ says that $1/\gamma$ is a root of
$$
F_s(X)\coloneqq
\sum_{j=0}^s(-1)^{s-j}\binom sj\frac{(s+1)!}{(j+1)!}X^j
=(-1)^s s!L_s^{(1)}(X).
$$
Indeed $F_s(1/\gamma)=(s+1)!\gamma^{-s}\lambda_s$. Schur's irreducibility theorem for the associated Laguerre polynomial $L_s^{(1)}$ implies that every such root has degree $s$ over the prime subfield. This is the alpha-one statement for all $s$, as recorded on p. 584 of [Hajir, *Algebraic properties of a family of generalized Laguerre polynomials*](https://doi.org/10.4153/CJM-2009-031-6), citing Schur. It is not a theorem about a restricted Padé stability class.

Equation (6) would put that same root on a nonzero rational cubic, impossible for $s\ge4$, including $s=5$. With the scalar cap this proves the bound for all $p\ge5$. The additional stage comes from branching rooted conditions, not from any stability restriction; there is no assertion of attainment at $s=p$.

A [second derivation](../../research/strict-sdirk-dependency-depth/COMMON-DIAGONAL-LOCAL-BRANCHING.md) uses a mixed fork and only the first three clocks; it also gives a valuation argument that avoids quoting Schur. This general proof does not change the sharper stage counts already known through order 20.
