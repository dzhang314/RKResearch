# Cubic dirt is impossible in the paid-head six-tail SDIRK7 chart

This closes the proposed **rank-one dirty cubic escape** from the
clean-tail chronologies, provided the first three coordinate columns
are actual grade-four pure defects. It does not rule out rational
nine-stage strict SDIRK in other head geometries, and does not change
a global stage bound.

Work over any characteristic-zero field, with a nine-stage triangular
order-seven tableau of nonzero common diagonal $\gamma$. Assume the last
six physical clocks are pairwise distinct, the last weight is nonzero,
and each of the first three coordinate columns is in the reviewed
defect space $F_4$. This head assumption follows from a
quadratic-clean tail and three distinct helper clocks whose quadratic
defects are each nonzero. Over $\mathbb Q$, if all six tail weights are
nonzero, the separate collision theorem already supplies their
distinctness.

Let $c=A1$, $C=\operatorname{diag}(c)$, and $r=(bC)A$. All three rows
$b,bA,r$ are zero at the three helpers, by their paid budgets on $F_4$.
From reviewed primitive moments, the rows

$$
 e=bA-b(1-c),\qquad D=r-b(1-c^2)/2
$$

annihilate clock powers through degrees five and four respectively.
There are at most six sites on their support. Thus $e=0$ by
degree-five interpolation. Triangularity at the last stage gives

$$
 c_9=1-\gamma,\qquad
 D_9=b_9\left(\gamma c_9-(1-c_9^2)/2\right)=-b_9\gamma^2/2\ne0.
$$

If $D_i=0$ at any tail site, its support would have at most five
sites, and degree-four interpolation would force $D=0$. Thus $D$
has full tail support. Equivalently $D$ is a nonzero multiple of the
six-site barycentric row $1/\prod_{j\ne i}(c_i-c_j)$; the proof
below does not require choosing the multiple.

Now take any actual cubic defect $v\in F_3$. The primitive-extension
row $r$ annihilates both $v$ and $Cv$ at order seven:
$Av$ and $A(Cv)$ are pure defects in grades four and five,
respectively, and the outer clock read costs one grade.
The pure density $b(1-c^2)/2$ does so as well since its tests against
$v$ have degree at most three. Therefore

$$
 Dv=D(Cv)=0.
$$

Let $P$ be the cubic polynomial interpolating $v$ at the first four
tail sites. The same two equalities hold for $P(c)$, since $D$
annihilates all powers through four. The difference $v-P(c)$ can be
read by $D$ only at the last two sites. Its two weighted equations
have determinant $D_8D_9(c_9-c_8)\ne0$; the difference vanishes
there too.

The tested moments $bC^jv=0$ for $0\le j\le3$ now act on
the four coefficients of $P$ by the uniform $4\times4$ Hilbert
matrix $H_{jk}=1/(j+k+1)$. The ordinary bush moments through
degree six are exactly this law. Its inverse is the integer matrix

    16  -120   240  -140
  -120  1200 -2700  1680
   240 -2700  6480 -4200
  -140  1680 -4200  2800

and hence $P=0$. No positivity or sign assumption on $b$ or on
the field was used. The result rules out *every* nonzero tail cubic
defect, not merely the isotropic rank-one candidate.

The accompanying native source is
[SDIRKSevenTailCubicPurity.lean](../../lean/RKCert/Research/SDIRKSevenTailCubicPurity.lean),
using the reviewed HasOrder and zeroSpace predicates. It replayed
on stock Lean 4.36.0 with only standard axioms. Run
**python3 check-cubic-purity-linear.py** for an independent replay of
the exact Hilbert inverse and the six-site linear inference on
arbitrary distinct rational clock inputs. The universal argument
is the interpolation proof above.

## Mathematical extension to other orders

The same causal argument works at order $p\ge5$ when the
head coordinate columns belong to $F_{p-3}$, every tail clock
is distinct, and the final diagonal and weight are nonzero.
The first and second errors annihilate degree $p-2$ and
$p-3$, respectively. If the tail has at most $p-2$ sites,
both errors would vanish, contradicting the terminal
$-b_{\rm last}\gamma^2/2$ second error. If it has exactly
$p-1$ sites, the second error has full support and is proportional
to the $(p-1)$-site barycentric row.

For $v\in F_j$ both the true second primitive row and its
degree-two density annihilate its consecutive probes
$C^\ell v$ for $0\le\ell\le p-j-3$. Each successive top
Vandermonde coefficient of the tail interpolant of $v$ must
vanish, so that interpolant has degree at most $j$. If
$2j+1\le p$, pairing with clock powers through degree $j$
is the paid nonsingular Hilbert matrix of size $j+1$.
Hence the entire tail is clean through grade
$\lfloor(p-1)/2\rfloor$. This is a mathematical extension,
not another Lean theorem in this bundle. Its field proof also
works in characteristic greater than $p$, because the Hilbert
determinant $\prod_{k=1}^{j}(k!)^4/\prod_{k=1}^{2j+1}k!$
is a unit there.
