# Weighted residue transfer for finite node hulls

Let $K$ be a field. Let $C$ and $O$ be finite sets of nodes with positive multiplicities $m_C$ and $m_O$, and define their monic hulls by
$$
Q\coloneqq\prod_{u\in C}(X-u)^{m_C(u)},\qquad
D\coloneqq\prod_{u\in O}(X-u)^{m_O(u)}.
$$
Suppose both hulls have degree $n\ge1$, and suppose
$$
Q+PR=\sigma D,\qquad \gcd(P,QD)=1 .
$$
The coprimality hypothesis means exactly that $P$ is nonzero at every node. The grids can overlap, with different multiplicities even at the same node.

For $H\in\{Q,D\}$, let $\operatorname{rem}_H$ select the unique representative of degree less than $n$, and take $P^{-1}$ in $K[X]/(H)$. Define
$$
U_H(F)\coloneqq\operatorname{rem}_H(P^{-1}F),\qquad
\Lambda_H(F)\coloneqq[X^{n-1}]U_H(F).
$$
Then for every polynomial $F$,
$$
\boxed{\Lambda_D(F)-\sigma\Lambda_Q(F)=-[X^{-1}]\frac{FR}{QD}.}
$$
Here $[X^{-1}]$ denotes a coefficient in the formal Laurent expansion in $X^{-1}$ at infinity.

## Proof

Suppress the argument $F$ of $U_Q$ and $U_D$, and set
$$
E\coloneqq\frac{U_D}{D}-\sigma\frac{U_Q}{Q}+\frac{FR}{QD}.
$$
The hull identity gives
$$
PE=-\frac{F-PU_D}{D}+\sigma\frac{F-PU_Q}{Q}\in K[X],
$$
since each numerator in the last expression is divisible by its denominator. The denominator of $E$ divides $QD$, which is coprime to $P$, so $E$ itself is a polynomial. Extract its zero $X^{-1}$ coefficient. Since each $H$ is monic of degree $n$ and $\deg U_H<n$, the $X^{-1}$ coefficient of $U_H/H$ is $[X^{n-1}]U_H$. This proves the identity.

## Sharp degree range

For $R\ne0$, set
$$
s\coloneqq\deg R.
$$
Transfer holds for every $F$ of degree at most $2n-s-2$. At the first excluded degree the exact defect is
$$
\Lambda_D(F)-\sigma\Lambda_Q(F)
=-\operatorname{lc}(R)\,[X^{2n-s-1}]F
\qquad(\deg F\le 2n-s-1).
$$
Both statements follow by expanding the quotient with its monic degree-$2n$ denominator. The bound is sharp for these fixed data: take $F=X^{2n-s-1}$. If $R=0$, monicity instead gives $\sigma=1$ and $Q=D$, so transfer holds in every degree.

For a confluent example over $\mathbb Q$, take
$$
\begin{aligned}
Q&\coloneqq X^2(X-1),&\qquad D&\coloneqq X(X-1)^2,\\
P&\coloneqq X-2,& R&\coloneqq X(X-1),&\qquad \sigma&\coloneqq 2.
\end{aligned}
$$
The multiplicities at $0$ and $1$ are swapped, and $Q+PR=2D$. Transfer holds through degree $2$ and fails for the cubic $F=PX^2$: both top coefficients equal $1$, not in ratio $2$.

## Local formula and the distinct-node corollary

Let $u$ have multiplicity $m_u$ in a hull $H$, and put
$$
H_u(X)\coloneqq H(X)/(X-u)^{m_u}.
$$
The local contribution of $u$ is
$$
[t^{m_u-1}]\frac{F(u+t)}{P(u+t)H_u(u+t)} .
$$
The sum of these contributions is $\Lambda_H(F)$. Indeed, $F/(PH)-U_H/H$ is regular at every node, so only the principal parts of $U_H/H$ contribute. Their simple-pole coefficients sum to the $X^{-1}$ coefficient at infinity; terms with pole order at least two contribute nothing there. The local series are formal and have invertible denominators. Thus Taylor coefficients, or Hasse derivatives, work in every characteristic. Ordinary derivatives recover all the same jets only when the required factorials are invertible; in characteristic $p$, this condition is $m_u\le p$ at every node.

In particular, for a distinct-node grid $S$, define
$$
H_S\coloneqq\prod_{u\in S}(X-u).
$$
Here $m_u=1$ and $H_u(u)=H_S'(u)$, so the corollary is the weighted divided difference
$$
\Lambda_{H_S}(F)=\sum_{u\in S}\frac{F(u)}{P(u)H_S'(u)}.
$$
Under the bounds $\deg P\le d$ and $\deg R\le n-d$, with $1\le d\le n$, the general identity gives $\Lambda_D(F)=\sigma\Lambda_Q(F)$ through degree $n+d-2$.

The invertibility condition is substantive. Let
$$
g\coloneqq\gcd(P,H)
$$
be monic. If $\deg g>0$, the inverse is unavailable. Even when a solution of $PU\equiv F\pmod H$ exists, adding $X^{\deg g-1}H/g$ preserves the congruence and changes the top coefficient.
