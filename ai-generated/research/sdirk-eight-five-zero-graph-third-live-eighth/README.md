# Graph support, first zero at row 3, and live row 8

Consider a strict ten-stage SDIRK tableau $A,\mathbf b$ of ordinary order at least eight over a characteristic-zero field. Set $\mathbf c=A\mathbf1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$, $G=\operatorname{diag}(\mathbf g)$, and $U=\ker G$. Assume exactly five physical quadratic zeros, genuine graph support, no active off-zero weight, the first zero at actual physical row 3, and a live physical row 8.

**Result.** This chart is impossible over every characteristic-zero field. The proof uses all algebraic rear orientations, not a real or ordered-field assumption. Positive-characteristic, silent-eighth, and off-zero-active cases are not claimed in this packet.

## 1. Ordinary moments determine the geometric towers

By the [support-rank census](../sdirk-eight-five-zero-support-rank/README.md) and [four-site graph exclusion](../sdirk-eight-five-zero-graph-four-ordinary-duplicate/README.md), all five physical zeros are live at five distinct clocks. Normalize $A'=A/\gamma$, $\mathbf x=\mathbf c/\gamma$, $D=1/\gamma$, $\boldsymbol\eta=\mathbf g/\gamma^2$. The first physical zero is at $a=x_3=1+2u$ and the actual forward gap has $4u^3-12u^2+3u+2=0$, by the literal arithmetic third-zero phase. On off-zero rows $\eta_i=P(x_i)$ for a supported quadratic graph. Its first two residual reads make
$$
P=P_0+\lambda R,\qquad P_0(T)=2T-1-T^2/2,\qquad R(T)=(T-1)(T-1-u).
$$
The graph parameter $\lambda$ is not determined by its first two rows. The actual supported vector is $\mathbf q=P(\mathbf x)-\boldsymbol\eta$.

The three live terminal zero clocks, in reverse chronological order, are $D-1,D-1-v,D-1-w$. The literal rear identities give $w=2-v$ (star) or $w=2v$ (arithmetic). The four known clock values are these plus $a$, and the remaining ordinary clock $b$ is the second chronological zero. The third chronological zero, denoted $c$, is physical stage 8. Let $P_4$ be the monic polynomial at the four known clocks, and $I_D(T^j)=D^j/(j+1)$. Then the ordinary fifth-site pivot is literally
$$ M_0=I_D(P_4)=b_{\text{second zero}}P_4(b)\ne0,$$
because the actual weight is live and the five clocks are distinct. Write $M_i=I_D(T^iP_4)/D^i$. The moment pin is $b=D M_1/M_0$, and the two projected moment equations are
$$M_0M_2-M_1^2=M_0M_3-M_1M_2=0.$$

Work over the irreducible forward gap field $K=\mathbb Q(u)$. In the star use $V=(v-1)^2$, so the two nonterminal rear factors are $(T-D+2)^2-V$. In the arithmetic phase keep $V=v$. Take the resultant of the two moment equations in $V$, dividing out only known nonzero powers of $D$ in the input equations. In $K[D]$ it factors by degree and multiplicity as follows:

| Phase | Factors in the moment resultant | Nonzero factors whose geometric fibers force $M_0=0$ |
| --- | --- | --- |
| Star | 1 (multiplicity 4), 5, 15 | 5 |
| Arithmetic | 1 (multiplicity 8), 2, 4, 8, 26 | 2 and 8 |

The degree-one factor is $D$, forbidden. For each remaining factor the exact replay reconstructs **both moment polynomials** in its quotient field and takes their monic gcd in $V$. It is linear in every such factor. Each pivot inverse is verified by the corresponding Bézout relation, not assumed invertible. This makes the reconstruction valid at every root of that factor in any extension. On the remaining regular fields, it recovers $V$ and $b$ and verifies the fifth-node pivot before inversion.

## 2. Two supported discrepancy equations in a common graph parameter

Let
$$
L_4(T)=70T^4-140DT^3+90D^2T^2-20D^3T+D^4,\qquad
L_3(T)=T^3-\tfrac32DT^2+\tfrac35D^2T-\tfrac1{20}D^3.
$$
Write $J$ for the polynomial primitive from zero. The grade-three read $A'_U P$ is exactly $JP$ because $F_3=GE_1$ is clean on $U$. The grade-four pure restriction to $U$ is the span of $L_4$: it is at most one-dimensional by $GE_2$, and $L_4$ does not vanish on all five distinct zero clocks. The restriction of $M\mathbf q$ spans the same line, since its earliest nonzero supported coordinate reads the nonzero diagonal of $M=CA-AC-A^2$. At first zero $a$, if $P(a)$ vanished then $L_4(a)$ would vanish as well. The actual diagonal reads would then give $P(a)=JP(a)=J(TP)(a)=0$ at a nonzero Gauss clock, contradicting the [native quadratic primitive lemma](../sdirk-eight-five-zero-graph-four-ordinary-nongauss/README.md). Thus both $P(a)$ and $L_4(a)$ are nonzero.

Write $F(P)$ for the second-zero gate at $b$ resulting from the first and second $TP$ reads:
$$
F(P)=L_4(a)\big[a(JP)(b)-J(TP)(b)+(b-a)P(b)\big]
       -L_4(b)\big[aP(a)-J(TP)(a)\big]=0 .
$$
This is linear in $P$. Denote the coefficient of $L_4$ in the $TP$ discrepancy by $\mu=[aP(a)-J(TP)(a)]/L_4(a)$. The three actual grade-five $T^2P$ discrepancies at the first three zero rows are, successively,
$$
\begin{aligned}
d_a &=a^2P(a)-J(T^2P)(a),\\
d_b &=b^2P(b)+a^2[(JP)(b)-P(b)]-J(T^2P)(b),\\
d_c &=c^2P(c)+(a+b)[J(TP)(c)+\mu L_4(c)-cP(c)]\\
&\qquad-ab[(JP)(c)-P(c)]-J(T^2P)(c).
\end{aligned}
$$
The last line uses only the two earlier taps into the actual supported input: if their weighted contributions are $p,q$, then $a^2p+b^2q=(a+b)(ap+bq)-ab(p+q)$. No inverse of an output weight or tap is needed.

By the [support census](../sdirk-eight-five-zero-support-rank/README.md), $\dim GE_3=4$ and $F_5$ has dimension six. Since $GE_3$ vanishes on $U$, the two independent scalar evaluations of $L_3,L_4$ span $F_5|_U$. Thus the determinant of their evaluations at $a,b,c$ and the discrepancy vector $(d_a,d_b,d_c)$ is zero. Define $H(P)$ as this determinant multiplied by the nonzero $L_4(a)$, so it is polynomial and linear in $P$. There must be a shared $\lambda$ satisfying $F(P_0+\lambda R)=H(P_0+\lambda R)=0$. Eliminating it without division gives the necessary condition
$$
H(R)F(P_0)-H(P_0)F(R)=0.
$$

## 3. Both orientations and complete regular fibers

In arithmetic $c=D-1-2V$ is already defined in the reconstructed field. In the star the two actual orientations have
$$c=D-2+W,\qquad W^2=V$$
with either sign of $W$. Evaluate the parameter-elimination polynomial as $\alpha+\beta W$ in this exact quadratic algebra. Its norm $\alpha^2-V\beta^2$ must vanish if either orientation is a solution. There is no assumption that $W$ is in the base field, and this norm check also covers a split quadratic.

The exact norm is nonzero in **each** of the regular towers, of diagonal degrees 15 (star), 4 and 26 (arithmetic), checking all other necessary guards and the literal fifth-node pivot. The rank-drop and physical zero-denominator factors were excluded before this stage. Hence the entire live-eighth chart is impossible over characteristic-zero fields.

Run `python check_towers.py` with SymPy 1.14. It constructs all exact fields and runs the full algebraic norm check in about a minute on the recorded environment. The accompanying `RKCert.Research.SDIRKEightFiveZeroGraphThirdLiveEighth` source records the ring identities behind the common graph-parameter elimination, the two-mode determinant, and the quadratic orientation norm. The rooted-tableau reductions and symbolic tower are mathematical source proofs and exact replays, not one native `HasOrder` theorem. The Lean audit source is attached separately.
