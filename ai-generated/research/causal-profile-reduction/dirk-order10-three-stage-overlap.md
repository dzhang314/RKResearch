# A three-stage crossed cubic overlap needs three distinct clocks and two live hops

In the [eleven-stage equality face](dirk-order10-no-adjacent-cubic-pivots.md),
let $i<j$ be the earned interior zero pivots of the forward and reverse
grade-three Volterra kernel seeds. Suppose $j=i+2$, with the sole
middle row indexed by $k=i+1$. Then **$a_{kk}$, $a_{ki}$, and
$a_{jk}$ are all nonzero, and $c_i,c_k,c_j$ are pairwise distinct**.
This excludes the explicit middle, the missing-hop, and all repeated
clock faces of this three-row branch. It does not exclude the general
three-row branch or raise the unrestricted stage floor.

This theorem is over every field admitting order ten. Over a
nontrivial commutative ring, reduction to a residue field selects the
same four nonunit diagonal positions, with the same separation; the
three middle-and-hop entries at a three-row overlap are nonzero and
the three clocks are still pairwise distinct in the original ring.
Those entries need not be units in the ring.

## Exact local structure

Write $x,y,z$ for the clocks at $i,k,j$, $d=a_{kk}$,
$p=a_{ki}$, $q=a_{jk}$ and $w=a_{ji}$. The forward kernel
column on the cut is $(f,g,h)$ with $f\ne0$. The reverse kernel
row on the cut is $(\alpha,\beta,\gamma)$ with $\gamma\ne0$.
The physical restriction of $R=CA-AC-A^2$ gives
$$
\begin{aligned}
 p(y-x-d)f-d^2g&=0,\\
 q(z-y-d)\gamma-d^2\beta&=0,\\
 ((z-x)w-qp)f+q(z-y-d)g&=0 .
\end{aligned}
$$
No outside tap contributes to these three identities: the forward
seed is zero before $i$, the reverse seed is zero after $j$,
and both outer diagonals vanish. The pure and single-primitive
reads have the following literal forms:
$$
\begin{aligned}
 U_r&=\alpha f x^r+\beta g y^r+\gamma h z^r,\\
 V_{\ell,r}
 &=\beta y^r(p x^\ell f+d y^\ell g)
    +\gamma z^r(w x^\ell f+q y^\ell g).
\end{aligned}
$$

If $d=0$, the kernel equations give $p(y-x)=q(z-y)=0$
and $(z-x)w=qp$. Both hops cannot be present: they would force all
three clocks equal, contradicting the last relation. The optional
direct skip also preserves its clock. Therefore either all primitive
reads vanish, or every one comes from a single clock $\xi$ with
$V_{\ell,r}=S\xi^{\ell+r}$ and the pure reads have at most $\xi$
and one spectator clock. The former alternative already contradicts
the crossed cubic primitive test.

If $d\ne0$ and one hop vanishes, the corresponding middle kernel
equation gives $g=0$ (if $p=0$) or $\beta=0$ (if $q=0$).
The only surviving primitive tap is the outer skip. It must have
$x=z$ if live, and the middle row contributes nothing to pure
reads. This reduces to the same one-primitive-clock case.

If $d\ne0$ and $x=y\ne z$, the first kernel identity gives
$pf+dg=0$, and the last then gives $(z-x)(wf+qg)=0$.
Both receiving contributions vanish. Similarly if $y=z\ne x$,
the second identity gives $d\beta+q\gamma=0$, and the other
two give $dw=qp$. Thus $\beta p+\gamma w=0$ and the two
receiving contributions cancel. All equal clocks reduce directly
to a single-clock overlap. Finally if only $x=z$ and both hops
are live, eliminating $g$ gives $-pq(y-x)^2=0$, impossible
unless all clocks coincide.

## Why even a spectator clock cannot rescue a single primitive clock

Let the nonzero forward and reverse profiles be
$P=a x+b x^2+e x^3$ and $Q=(1-x)(h+\ell x+m x^2)$.
Write $M_n=I(x^nQ)$ and $L_k=I(x^kPQ)$.
Assume the primitive tests agree with $S\xi^{r+\ell}$, $S\ne0$,
at the six pairs with $r+\ell\le2$, and the pure tests have
$L_k=T\xi^k+U\eta^k$ for $k\le3$. All are actual paid reads of
the original tableau. Neither $\xi$ nor $\eta$ is assumed nonzero.

The three primitive rows at total two give
$$
 aM_4=12S\xi^2,\quad bM_5=-60S\xi^2,\quad eM_6=60S\xi^2.
$$
This uses the determinant-one matrix obtained by row clearing with
$12,60,60$. At $\xi=0$, this yields $L_3=0$; the two-clock plain
form then also gives $L_1=L_2=0$. The two rows at total one plus
the row for $L_2$ have determinant one and give
$aM_3=bM_4=eM_5=0$. With two or more nonzero coefficients of $P$,
the resulting zero windows overlap into three consecutive moments
(starting at 3 or 4); with a single coefficient, $L_1=0$ gives
the missing first moment. The size-three shifted Beta test gives
$Q=0$.

For $\xi\ne0$, put $W=eM_5$. Using the rows at totals zero and one,
and the products of the total-two equations, gives
$$
5\xi L_1=W,\qquad 10L_2-W=60S\xi,\qquad L_3=12S\xi^2 .
$$
For clarity, set $A_1=aM_3$, $B_1=bM_4$, $B_0=bM_3$, $C_0=eM_4$.
The exact identities used are
$10A_1-3W=-60S\xi$, $5B_1+6W=60S\xi$,
$6L_1-12S=2B_0+3C_0$,
$A_1B_1=12S\xi^2 B_0$, and $B_1W=-60S\xi^2C_0$.
They entail $6\xi L_1=12S\xi-B_1$ by canceling $60S\xi$.
The three displayed $L$-identities imply
$L_3-2\xi L_2+\xi^2L_1=0$, hence
$U\eta(\eta-\xi)^2=0$ and $L_2-\xi L_1=0$.
So $W=60S\xi$, and substitution through the six rows yields
$M_{r+1}=\xi M_r$ for $r=2,3,4,5$.
The four resulting vanishing tests for $(x-\xi)Q$ kill it by
the $4$ by $4$ shifted Beta matrix for weight $x^2(1-x)$.
The largest denominator paid is ten. The determinant is
$1/(2^{11}3^6 5^4 7^4)$; the inverse last row
$(-12600,88200,-176400,105840)$ followed by the paid size-three
test is a division-free certificate. This contradicts $Q\ne0$.

## Lean

[DIRKTwoClockPrimitiveOverlap.lean](../../lean/RKCert/ReviewedNative/DIRKTwoClockPrimitiveOverlap.lean)
checks the scalar obstruction, explicitly separating the zero clock
and the four-consecutive-moment Beta test.
[DIRKThreeStageOverlap.lean](../../lean/RKCert/ReviewedNative/DIRKThreeStageOverlap.lean)
checks the local geometric reductions and the repeated clock branches.
[DIRKOrderTenCrossedZeros.lean](../../lean/RKCert/ReviewedNative/DIRKOrderTenCrossedZeros.lean)
checks the actual finite row/column clipping, the paid identities, and
the field and ring conclusions. Replay and typed axiom audit used
Lean/Mathlib 4.36.0.
