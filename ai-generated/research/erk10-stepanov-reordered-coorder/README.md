# A pair-order-independent obstruction to the five-opening Stepanov chart

No fourteen-stage, order-ten tableau exists in the following specific explicit architecture, even with arbitrary signed output splits and reordering of the four repeated interior Lobatto pairs. The assumptions retained are substantive: the five opening rows are the canonical two-clean-donor opening, every high row is genuinely locally pure through derivative size five, the final high row is the unique endpoint at 1, the literal $D(1)$ identity holds, and high aggregate $\mathbf d_1,\mathbf d_2,\mathbf d_3$ vanish separately at each high clock. This is not an unrestricted ERK lower bound. The real-algebraic interval remains 14–15.

The authentic 15-stage witness and the exact 14-stage order-nine control are in the [preceding packet](../erk10-stepanov-five-opening/README.md). Its earlier fixed-high-block moment obstruction is not used in this proof. In particular no published value of $a_{87}$, any high tap, any opposed pair amplitude, or any internal output split is held fixed.

## Architecture and true order constraints

Write $A$ for the strict explicit tableau, $\boldsymbol c=A\mathbf1$, and $C=\operatorname{diag}(\boldsymbol c)$. The five opening rows have clocks
$$
 0,\quad e,\quad 2p/3,\quad p,\quad q ,
$$
with $e,p,q\ne0$ and $p\ne q$. The second and third are the standard explicit order-one/order-two preparatory rows. The last two are actual order-three donors: each uses no tap on stage two, the first uses only the origin and third row, and the second uses the origin, third row, and first donor; their monomial primitives are paid through degree two. The nine high rows use only $0,p,q$ in the opening, beside arbitrary causal earlier high taps. Their first eight positions consist of two actual stages at each of the four interior six-point Lobatto nodes, in any order. The final high row is at 1. Output is supported only on high rows and the origin. Put $B$ for the nine-by-nine strictly lower triangular high block.

For nominal clock letters and the usual Butcher weight columns define the row vectors
$$
 \mathbf d_j=\mathbf b C^j A-\mathbf b(I-C^{j+1})/(j+1).
$$
Ordinary order ten forces $\mathbf d_j\boldsymbol\Phi_t=0$ whenever $|t|+j+1\le10$: compare the actual output on a unary parent of $t$ with $j$ leaf marks and its same-budget clock moments. Consequently both $\mathbf d_4$ and $\mathbf d_1 C^k A$ for $k=0,1,2$ annihilate every actual size-at-most-five derivative column. Their high restrictions are ordinary row vectors; no claim of a signed transpose tableau is needed.

The two genuine pure size-five columns
$$
 A\mathbf c^{\odot3}-\mathbf c^{\odot4}/4,\qquad
 A^2(A\mathbf c-\mathbf c^{\odot2}/2)
$$
vanish at the origin and at all high stages. Their actual restrictions at $p,q$ are independent: the second is a nonzero multiple of the third opening column there, and their determinant, after extracting that nonzero multiplier and choosing the order of the two columns, is $-3p q^2(p-q)^2/16$. The derivation is the explicit donor computation in the earlier packet. Any of the rows above supported in the opening on $0,p,q$ must therefore have zero coefficients at $p,q$. Its high restriction must then kill the evaluations of $X,X^2,X^3,X^4$ by the four actual bushes.

The literal identity $\mathbf d_0=0$ is assumed. Each $\mathbf d_j$ for $j=1,2,3$ has sum zero at every high clock. In addition $\mathbf d_1$ is zero on the opening: its only possible opening coefficients are at $0,p,q$; its total high clock moments are zero by the group sums, and its true moments on $1,\boldsymbol c,\boldsymbol c^2$ kill the remaining three coefficients by interpolation. Thus each $\mathbf d_1 C^k A$ is indeed supported in the opening only at the required three positions. The same is immediate for $\mathbf d_4$.

## Required exact high site means and chronological consequences

For every $f\in X\mathcal P_3$, the high restrictions of all five rows $\mathbf d_0,\ldots,\mathbf d_4$ annihilate $E f$, where $E$ evaluates on the nine high clocks. Write $W_x$ for the nonzero aggregate weight at each distinct high site $x$. Ordinary precision nine for the six-site clock rule fixes these weights to the unique Lobatto masses, including the origin; none is zero. Since $f(0)=Jf(0)=0$, the origin does not contribute to any of the following polynomial integrals. For $n=0,\ldots,4$, integration by parts and precision nine show
$$
 \sum_i b_i x_i^n (B E f)_i
   =\sum_i b_i (1-x_i^{n+1}) f(x_i)/(n+1)
   =\sum_i b_i x_i^n Jf(x_i).
$$
Here both polynomials used for quadrature have degree at most nine. Inverting the Vandermonde on the five distinct high sites makes their **individual weighted high means** exact on this whole four-dimensional space.

If an interior group at $r$ completes before all four distinct interiors have appeared, its actual two rows use at most three distinct predecessor clocks from the interior four. For the set $S$ of these possible labels, test
$$
                         f_S(X)=X\prod_{a\in S}(X-a).
$$
The mean's actual output is zero, while $(Jf_S)(r)\ne0$. The scalar gate is exact for every $r$ and every $S$ of cardinality at most three: all sixty values have nonzero reduction modulo 227. Hence the first four high occurrences are distinct, and each pair's second occurrence lies in the second sweep. The later physical share of each pair is nonzero as well: otherwise the site mean uses only its first occurrence, which has at most three distinct predecessors and fails the very same exact gate. These arguments permit negative individual masses.

## Impossible rank at the two sweeps

For the four interior clocks, let $G$ be the exact group primitive on $X\mathcal P_3$, using evaluation on those four distinct nonzero interiors as its domain coordinates. It is fixed by the exact means. Let $B_-$ be the actual high primitive of their respective first-sweep occurrences, represented on the same four inputs. Put $\Delta=G-B_-$. Every row of $\Delta$ is nonzero by the preceding support hull gate.

At site $x$, let $\lambda_x$ be the later coefficient of the opposite pair $\mathbf d_1$ multiplied by $W_x/b_x^+$, where $b_x^+$ is its nonzero later share. The group mean identity gives
$$
 B_x^+-B_x^-=(W_x/b_x^+)(G_x-B_x^-)
$$
on $X\mathcal P_3$, regardless of whether the earlier share vanishes. Since the high parts of the actual annihilating rows $\mathbf d_1 C^k A$ kill all four polynomial inputs, one obtains the exact matrix equations
$$
             \boldsymbol\lambda C_{\rm site}^{\,k}\Delta=0,\qquad k=0,1,2.
$$
At least one $\lambda_x$ is nonzero: on the last interior occurrence before the unique terminal 1, literal $\mathbf d_0=0$ determines that column's only available output tap. There $\mathbf d_1$ is exactly $b_x^+(1-x)^2/2\ne0$.

If at most two components of $\boldsymbol\lambda$ are nonzero, the first two clock moments isolate each active row of $\Delta$, a contradiction. If at least three are nonzero, the three marked rows are independent and force $\operatorname{rank}\Delta\le1$. But for the first two high clocks $x,y$, distinct by the first sweep, test $f=X(X-x)$ and $g=X^2(X-x)$. Both actual early rows' strictly high actions on these tests vanish: the first sees no high predecessor and the second sees only $x$. The two-by-two determinant of their exact primitives is
$$
 (Jf)(x)(Jg)(y)-(Jg)(x)(Jf)(y)
                       =-x^3 y^2(x-y)^2/24\ne0 .
$$
Thus the first two rows of $\Delta$ are independent, again a contradiction. This closes the two-sweep rearrangement as well as the original Stepanov order of pairs.

## Replay and scope

    sha256sum -c sources.sha256
    python3 check.py
    lean ../../lean/RKCert/Research/ERK10ReorderedCoorderMod227.lean

The replay uses the neighboring authenticated coefficient file, reducing its real algebraic Lobatto nodes with the same integral map as in the preceding packet. The Lean Core receipt computes all sixty support tests independently, after clearing denominators by 60. The field transfer and actual rooted necessity above are mathematical proofs; the native proof is of the precise finite arithmetic. A different low interface with another pure-response rank, an unpaid aggregate co-order, another scalar mesh, or a different high stage budget is not covered.
