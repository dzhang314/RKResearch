# Weighted residue transfer over commutative rings

The [field and node-hull formulation](README.md) has a modular version over any nonzero commutative ring $A$ with identity, including rings with zero divisors. The hulls $Q,D\in A[X]$ need only be monic of positive degrees $q,d$. They need not split, have equal degrees, or be coprime to each other. Assume that $P,R\in A[X]$ and $\sigma\in A$ satisfy
$$
Q+PR=\sigma D,\qquad aP+bQ=1
$$
for some $a,b\in A[X]$. No unit condition on $\sigma$ is needed.

The same Bézout identity gives $(a-bR)P+b\sigma D=1$. Multiplying the two identities gives $1=cP+eQD$ for some $c,e\in A[X]$. In particular, $P$ is invertible modulo both hulls. For $H\in\{Q,D\}$, let $\operatorname{rem}_H$ denote the unique representative of degree less than $\deg H$ furnished by monic division, and define
$$
U_H(F)\coloneqq\operatorname{rem}_H(P^{-1}F),\qquad
\Lambda_H(F)\coloneqq[X^{\deg H-1}]\,U_H(F),
$$
where $P^{-1}$ is taken modulo $H$. Then for **every** $F\in A[X]$,
$$
\boxed{\Lambda_D(F)-\sigma\Lambda_Q(F)=-[X^{-1}]\frac{FR}{QD}.}
$$
The Laurent coefficient is at infinity. Monic denominators are invertible in $A((X^{-1}))$: after factoring out the highest power of $X$, the remaining series has constant coefficient $1$.

## Proof

Suppress the argument $F$ of $U_Q$ and $U_D$, and set
$$
E\coloneqq\frac{U_D}{D}-\sigma\frac{U_Q}{Q}+\frac{FR}{QD}.
$$
The hull identity gives
$$
PE=-\frac{F-PU_D}{D}+\sigma\frac{F-PU_Q}{Q}\in A[X].
$$
Write $E=S/(QD)$. Thus $QD$ divides $PS$, and $1=cP+eQD$ implies that $QD$ divides $S$. So $E$ is a polynomial, with zero $X^{-1}$ coefficient. Monicity and $\deg U_H<\deg H$ give $[X^{-1}](U_H/H)=[X^{\deg H-1}]U_H$. This proves the identity without canceling an arbitrary ring element.

## Exact degree boundary

Reduce $R$ by the full denominator:
$$
T\coloneqq QD,\qquad N\coloneqq q+d,\qquad R_0\coloneqq\operatorname{rem}_T R.
$$
Replacing $R$ by $R_0$ changes $FR/T$ by a polynomial and hence does not change its $X^{-1}$ coefficient. If $R_0\ne0$, set
$$
s\coloneqq\deg R_0,\qquad r\coloneqq[X^s]R_0,\qquad m\coloneqq N-s-1.
$$
For $\deg F\le m$ the product $FR_0$ has degree at most $N-1$, so the only term that can contribute to the Laurent coefficient is its coefficient of $X^{N-1}$. Thus
$$
\Lambda_D(F)-\sigma\Lambda_Q(F)=-r[X^m]F\qquad(\deg F\le m).
$$
Transfer holds for all $F$ of degree at most $m-1$. The first excluded degree $m$ is nonnegative because $s<N$. If $m=0$, the guaranteed range is vacuous for nonzero polynomials and $F=1$ is the first test. In all cases the monomial $F=X^m$ has defect $-r\ne0$, even when $r$ is a zero divisor. Some other polynomials of degree $m$ can have zero defect. The vacuous case really occurs: with $Q=D=R=X$, $P=1$, and $\sigma=2$ over $\mathbb Z/4\mathbb Z$, the constant $F=1$ has defect $3$.

If $R_0=0$, transfer holds in every degree. In fact $T$ then divides $Q-\sigma D$, which has degree less than $N$, so monicity gives $Q=\sigma D$. Comparing leading coefficients gives $Q=D$ and $\sigma=1$. Now $PR=0$ gives $R=bQR$; iterating makes $R$ a multiple of every power of the positive-degree monic $Q$, so $R=0$.

If $\deg R<q$, including $R=0$, then $\sigma$ is automatically a unit. Reduction modulo $Q$ gives $R=\sigma U_Q(D)$, so $Q=\sigma(D-PU_Q(D))$. Taking the coefficient of $X^q$ exhibits an inverse for $\sigma$.

## Local interpretation and a zero-divisor example

For a split hull with factors $(X-u)^{m_u}$, $P$ is invertible modulo the hull exactly when every $P(u)$ is a unit. Necessity follows by evaluation. For sufficiency, modulo each factor $P$ is the sum of the unit $P(u)$ and a nilpotent; multiply the resulting Bézout identities to obtain invertibility modulo their product. This does not require the node differences to be units. If distinct nodes within a hull do have unit differences, the factors are pairwise comaximal and the same local Taylor-coefficient (Hasse jet) sum as in the [field note](README.md#local-formula-and-the-distinct-node-corollary) applies. There is no characteristic or squarefree restriction. A nonunit difference makes the two corresponding local denominators noninvertible in $A$, but the modular transfer still applies.

In $A=\mathbb Z/4\mathbb Z$, take
$$
Q\coloneqq X^2,\qquad D\coloneqq X(X-2),\qquad
P\coloneqq1,\qquad R\coloneqq-2X,\qquad \sigma\coloneqq1.
$$
Here $Q+PR=D$ and $m=2$. For $F=X^2$, its remainders modulo $Q,D$ are $0,2X$, respectively, and $FR/(QD)=2X^{-1}$. The defect is $2$, a nonzero square-zero element. The polynomial $2X^2$ instead has zero defect in the same degree. The nodes $0,2$ of $D$ have nonunit difference, so the field-style local denominator is unavailable.

The modular construction and the identity commute with unital base change between nonzero rings: the hulls stay monic, and the Bézout identities and remainders map to the corresponding ones over the target. Sharpness need not survive noninjective base change. Here reduction modulo $2$ kills the defect, sets $R=0$, and makes the two hulls equal.
