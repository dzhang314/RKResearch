# Graph support, first zero at row 3, and silent row 8

Consider a ten-stage strict SDIRK tableau $A,\mathbf b$ of ordinary order at least eight over a characteristic-zero field, with five physical quadratic zeros, genuine graph support, and all off-zero weights zero. Let $U$ denote the physical zero set. Assume the first zero is row 3 and physical stage 8 is silent.

**Result.** This chart is impossible over every characteristic-zero field. Together with the [live-eighth theorem](../sdirk-eight-five-zero-graph-third-live-eighth/README.md), this excludes literal first zero at row 3 throughout the genuine graph case with no active off-zero stages. The first-zero-at-4 chart and coefficient fields of positive characteristic are not addressed here.

## 1. The joint cubic gap field

All five zeros are live at distinct clocks by the [four-site exclusion](../sdirk-eight-five-zero-graph-four-ordinary-duplicate/README.md), so a silent stage 8 is off-zero. Normalize $T=X/\gamma$, $D=1/\gamma$, $A'=A/\gamma$. The first normalized zero clock is $a=1+2u$ with $Q(u)=4u^3-12u^2+3u+2=0$. The literal last-two weights are live, and their normalized clocks are $D-1$ and $D-1-v$. The [literal reverse ghost gate](../sdirk-eight-four-zero-gaussian-rear/README.md) gives $H(v)=v^3-4v^2-v+2=0$. The initial graph is
$$P=P_0+\lambda R,\qquad P_0(T)=2T-1-T^2/2,\qquad R(T)=(T-1)(T-1-u).$$

The joint quotient $\mathbb Q[u,v]/(Q/4,H)$ is a degree-nine number field. The replay verifies this without choosing a real root: $\theta=u+2v$ has the monic polynomial
$$
\theta^9-33\theta^8+\tfrac{1605}{4}\theta^7-2117\theta^6+
\tfrac{59583}{16}\theta^5+\tfrac{81123}{16}\theta^4-
\tfrac{1330293}{64}\theta^3+\tfrac{334959}{32}\theta^2+
\tfrac{107595}{8}\theta-\tfrac{40639}{4}.
$$
It checks irreducibility over $\mathbb Q$, verifies the polynomial identity in the original joint quotient, and reconstructs both $u,v$ from $\theta$ by an exact nine-dimensional change of basis, checking the two recovered expressions coefficientwise in the original quotient. Thus every actual pair $(u,v)$ realizes this field, not merely one chosen conjugate of each gap.

## 2. Reconstruct the diagonal and interior zeros without losing rank drops

Let $P_3(T)=(T-a)(T-D+1+v)(T-D+1)$ and $I_D(T^i)=D^i/(i+1)$. Set $m_i=I_D(T^iP_3)$ for $0\le i\le4$. The two interior normalized live zeros, ordered $b,c$, are the roots of some monic quadratic $T^2+kT+q$. Therefore ordinary precision seven gives
$$m_iq+m_{i+1}k+m_{i+2}=0\qquad(i=0,1,2).$$
Its Hankel determinant $H_m=\det(m_{i+j})_{i,j=0}^2$ vanishes. In the joint gap field the exact monic factorization of $H_m$ consists of $D^6$ and an irreducible degree-nine factor. The gcd of $H_m$ and the principal Cramer pivot $\Delta=m_0m_2-m_1^2$ is exactly $D^2$. Thus every admissible $D$ is in the degree-nine factor, where $\Delta$ is invertible. The replay explicitly verifies a Bézout inverse there and that the reconstructed $k,q$ satisfy all three moment equations. No zero-pivot fiber is discarded without a guard.

Over this exact diagonal quotient take the quadratic algebra
$$ B=-k/2+W,\qquad C=-k/2-W,\qquad W^2=k^2/4-q.$$
The two signs represent both chronological interior orders. Neither splitting over the base field nor an ordering is assumed.

## 3. The common graph parameter fails both orientations

The supported grade-four and grade-five discrepancy arguments of the [live-eighth theorem](../sdirk-eight-five-zero-graph-third-live-eighth/README.md) depend only on the actual first three chronological zeros $a,b,c$, not on physical row 8. They apply unchanged here. In detail $F_3$ is clean on the zeros, $F_4|_U$ is the one scaled Legendre mode $L_4$, $F_5|_U$ is spanned by $L_3,L_4$, and $L_4(a)\ne0$ by the first-diagonal and nonzero-clock primitive argument. The second-zero $TP$ read is a homogeneous linear condition $F(P)=0$. The three grade-five $T^2P$ discrepancies must lie in the two Legendre modes, yielding another homogeneous linear condition $H_5(P)=0$ after multiplying by the nonzero $L_4(a)$. Thus a shared $\lambda$ necessarily satisfies
$$H_5(R)F(P_0)-H_5(P_0)F(R)=0.$$
The source computes this value using $b=B,c=C$ in the exact quadratic algebra above. The norm of its two possible signs is a nonzero polynomial residue of degree eight in the diagonal $D$ quotient. A zero in either ordering would force the norm zero. Hence neither actual order is possible. This also handles a split quadratic, without claiming that a branch exists when a particular geometric guard fails.

Run `python check_towers.py` with SymPy 1.14. It independently constructs the joint gap field, reconstructs the complete diagonal and interior-node tower, and performs the common-parameter norm test. The ring identities for the two-mode determinant and quadratic orientation norm are supplied by the [live-eighth companion Lean source](../sdirk-eight-five-zero-graph-third-live-eighth/README.md). This packet relies on exact arithmetic replays and the cited rooted reductions, not a native end-to-end `HasOrder` theorem. No stage interval changes.
