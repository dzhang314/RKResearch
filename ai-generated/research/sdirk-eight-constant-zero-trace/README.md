# No constant-trace supported line at three distinct strict SDIRK8 zeros

Consider a strict ten-stage SDIRK tableau of ordinary order at least eight over a field of characteristic zero or greater than seven. Its common diagonal is a nonzero $\gamma$, $c=A1$, $g=Ac-c^{\odot2}/2$, and there are exactly three physical zero entries of $g$, at distinct clocks. Let $U=\ker \operatorname{diag}(g)$, and use the actual saturated forward/reverse spaces $E_j,F_j,W_j,Z_j$ as in the [saturated flags](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md).

**Result.** No supported degree-two forward vector has nonzero constant scalar trace in this stratum. The proof reduces such a vector to one explicit coefficient characteristic (**17**) and then excludes all four physical arrangements there using genuine grade-four rooted reads. This handles the degree-zero trace of a possible supported line, not general nonconstant quadratic graphs, and gives no global ten-stage lower bound.

## 1. A forced constant residual and three third-Gauss zero clocks

Normalize the putative vector to scalar trace 1. Since $F_2=\langle g\rangle$, it is $v=1+\alpha g$, supported on $U$. Its normalization and $g_1=\gamma^2/2$ force $\alpha=-1/g_1$; all seven off-zero residuals equal $g_1$. All seven off-zero rows are live and at distinct clocks: otherwise the six ordinary paid tests $b^{\mathsf T} C^j g=0$ for $0\le j\le5$ kill the total weight at every active off-zero clock by a Vandermonde, leaving only three clocks for the ordinary quadrature, which has rank four. A zero clock can still equal an off-zero clock.

The identity $b^{\mathsf T} C^j v=I(X^j)$, $0\le j\le5$, says the quadrature on the three zero rows alone is ordinary degree-five quadrature. Its Hilbert rank three forces all three zero weights nonzero, and monic nodal orthogonality makes their centered clocks $y=2c-1$ the three roots of $P(y)=y^3-3y/5$. In centered time the weights at the two nonzero roots are $5/18$, and the weight at $y=0$ is $4/9$ (the first and second centered moments give these values). In particular this case is all-active.

The affine trace tests at the seven distinct off-zero clocks show $E_1\cap U=0$ and $W_1\cap U_{\rm row}=0$. Hence $F_3=GE_1$ and $Z_3=W_1G$ are clean on $U$. Applying $A$ to $v$ at the earliest zero therefore reads its scalar primitive $c$, while the actual triangular read sees only $\gamma$. The first zero clock is $\gamma$. The analogous reverse read of $v^{\mathsf T}B$, with $B=\operatorname{diag}(b)$, says the last zero clock is $1-\gamma$. The remaining zero is at $1/2$; the earliest and latest clocks cannot coincide because all three are distinct. The endpoint weights and clocks require no numerical ordering or real embedding.

## 2. An exact three-group diagonal constraint

Write $S$ for the principal submatrix on the three zero rows of $BA+A^{\mathsf T}B-bb^{\mathsf T}$. Its row sums are zero: on $U$, the actual supported reads of $Av$ and $v^{\mathsf T}BA$ are $c_i$ and $b_i(1-c_i)$, respectively, and $b^{\mathsf T}v=1$. The paid grade-seven self-pair of the degree-three column $(2C-I)v$ gives $y^{\mathsf T} S y=0$: its scalar trace is $2X-1$, and $2I(fJf)=I(f)^2$ for that trace.

For the monic cubic $P$ with roots $y_i$, any distinct pair satisfies $P'(y_i)+P'(y_j)=(y_i-y_j)^2$. Since $S$ is symmetric with zero row sums,
$$\sum_i S_{ii}P'(y_i)
=-\sum_{i<j} S_{ij}(P'(y_i)+P'(y_j))
=y^{\mathsf T} S y=0.$$
The diagonal is $S_{ii}=b_i(2\gamma-b_i)$. With the exact three Gauss weights above, $\sum_i b_iP'(y_i)=2/5$ and $\sum_i b_i^2P'(y_i)=1/15$, so $12\gamma=1$. But $2\gamma-1=-5/6$ must be a root of $P$, and $P(-5/6)=-17/216$. Thus only characteristic 17 remains.

## 3. Four forced literal arrangements in characteristic 17

In characteristic 17, $\gamma=10$, $g_1=16=-1$ and $v=1+g$. The earliest zero is at least stage three: at that clean row, the prefix columns $1,c$ have independent actual probes $e_i^{\mathsf T},e_i^{\mathsf T}A$ with determinant $-c_i^2/2\ne0$, and the nonzero $e_i^{\mathsf T}M$ annihilates both. The same statement applies to the reflected weighted tableau, legitimate since all weights are nonzero. The first two residuals in either orientation are equal and nonzero, so their normalized ratio $\kappa(u)=1+2u-u^2=1$ with $u\ne0$ forces $u=2$. The [literal first-three identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) then force uniform first-three clocks $(\gamma,3\gamma,5\gamma)$ and three off-zero residuals in each direction. The six exterior physical clocks are $(10,13,16\mid 2,5,8)$, in forward order. The three zeros occur in positions 4–7 in the chronological order $(10,9,8)$.

The seventh off-zero clock is $1/2=9$. To see this, let $I_0$ be integration minus the degree-five three-point Gauss quadrature. The six displayed exterior clocks sum to 3; if their monic product is $Q_6$, then
$$I_0(XQ_6)=\bigl(7/2-3\bigr) I_0(Q_6),\qquad
 I_0(Q_6)=I_0(X^6)=1/2800\ne0.$$
The first equality uses reflection symmetry and cancellation through degree five; the final equality uses the squared monic third Legendre polynomial. The degree-seven nodal product of all off-zero clocks must annihilate $I_0$, giving the claimed seventh clock. Their exact weights follow by the seven Vandermonde equations from precision zero through six. In the exterior order shown above they are $(15,11,2\mid 2,11,15)$; the off-zero row at 9 has weight 12. The three zero weights in their physical order are $(5,8,5)$. The independent replay verifies precision seven and all six weighted residual moments too; these scalar tests do not by themselves enforce ordinary order eight. Each zero clock is shared with one off-zero row, not duplicated within the zero group.

## 4. Two literal rooted read contradictions

The clean grade-three condition also gives the global identity $Av=Cv$. Indeed $Av-c\in\langle g,Cg\rangle$, and its first two actual reads are $-c_1,-c_2$: the affine pure coefficient is therefore $-c/g_1=c$ in this characteristic. Also $Ac=c^{\odot2}/2+g$ exactly, and $Ac^{\odot2}=c^{\odot3}/3$ at every zero coordinate by the same grade-three cleanliness.

**The extra off-zero row is position 4 or 5.** The paid grade-four pure feature $A(Cg)$ pairs to zero with the actual degree-three row of density $8+4X+2X^2+X^3$ and pure correction $(3+6X)g$. Its effective row (including $b$) is supported on the first five physical rows: its coefficients, attached to the clocks/residuals $(10,16),(13,16),(16,16),(9,16),(10,0)$ in that order, are $(10,12,16,13,1)$. For the four off-zero rows in this list $A(Cv)$ is zero: before the first zero there is no possible input, and if the off-zero row at 9 is just after the first zero its sole incoming zero tap is zero by $Av=Cv$. At the first zero clock 10, the read of $A(Cv)$ is $10\gamma$. Since $Cg=Cv-c$, the corresponding five reads of $A(Cg)$ are $(2,10,9,3,16)$. Thus the protected scalar row reads $16\ne0$, a contradiction.

**The extra off-zero row is position 6 or 7.** The fourth and fifth physical rows are zeros at clocks 10 and 9. The degree-three test row $b^{\mathsf T}(C+9I)(1+g)$ is supported exactly on those rows, with coefficients $(10,8)$ and scalar trace $X+9$. Pairing it with the actual fourth-grade feature $A c^{\odot3}$ is required to give $I((X+9)X^4/4)=8$ in characteristic 17. But interpolate $X^3$ at the first three physical clocks $(10,13,16)$ with $Q(X)=6+12X+5X^2$. The strict predecessor clocks of either fourth or fifth row are among these three, so their actual $A c^{\odot3}$ reads are
$$(JQ)(10)=9,\qquad (JQ)(9)+\gamma(9^3-Q(9))=13.$$
Here the $JQ$ terms are actual clean reads of $A1,Ac,Ac^{\odot2}$. The protected scalar row instead reads $10\cdot9+8\cdot13=7$, another contradiction.

The tests are linear combinations of ordinary marked rooted pairings with total grade at most seven. They do not assume any putative completion of the coefficients. Since the scalar values in this census are all in the prime field, these contradictions work over every ambient characteristic-17 field, not just $\mathbf F_{17}$.

## Replay and Lean scope

Run `python check_f17.py` (standard library only) to reconstruct the forced active quadrature and check the masks and their actual read residues in all four arrangements. `RKCert.Research.SDIRKEightConstantZeroTrace` proves a general cubic derivative identity, the characteristic restriction given the two scalar premises, and the two literal contradictions over arbitrary rings of characteristic 17. The full saturated tableau-to-scalar reduction is the source proof above, not a native end-to-end `HasOrder` theorem. Native replay was checked on Lean/Mathlib 4.36.0; see `proof-audit.lean`.
