# Weak-four quartic: uniform first-clock crossing from the actual payments

2026-11-25. Exact algebraic argument and rational-check script, not a Lean compilation. No diagonal, degree-12 scalar, fixed fibre, or held arithmetic enters this theorem. All intervals below mean the algebraic formal-primitive integral (not a completion of the base field).

## The abstract interface and the actual source

Let the base be a linearly strictly ordered field. State the root part in a chosen ordered extension with the selected-root property for the finitely many strict opposite-value intervals used below (an ordered real closure suffices mathematically; only the finite one-gap factory, with base inequalities carried back by an order embedding, is needed). Let $Q,Z$ be quartics, $Q\ne0$, and let $Z$ be the product over four distinct marks $a,c,d,h$ in the base, all different from 0 and 1. Require $Q$ nonzero on those marks and at 1. Scale $Q$ monic and write $F=QZ$ (not the auxiliary fit called $P$ in native `ERK16`). The hypotheses are exactly
$$
\begin{array}{ll}
 \int_0^1 X F T =0\quad(\deg T\le6);\\
 \int_0^a XQ=\int_0^a X^2Q=0, & \int_0^c X(X-a)Q=0;\\
 \int_d^1(1-X)Q=\int_d^1(1-X)^2Q=0, &
 \int_h^1(1-X)(d-X)Q=0 .
\end{array}
$$
Conclusion: $a>d$. Moreover, if $Q$ has just three roots in the strict unit interval, then not both $c>a$ and $h<d$.

Native source: `Width24OrdinaryWeakHead.weak_four_remaining_physical_cases` in `ERKOrder16WeakFourRemaining` pays carrier rank three, $Q(1)\ne0$, and excludes all but its two physical options. `weak_four_inactive_unshared_remaining` eliminates the five-row option and pays precisely four distinct contrast rows, no clock 1, and inactive physical origin with $b_0=0$. `reverse_contrast_true_support` supplies nonzero clocks and $Q$ values at all four marks. Use `width24_weak_four_extra_port` (or the native wrapper in `ERKOrder16WeakFourPorts`): its actual `Z` is the nodal hull of the four marks, and its reverse `firstConstant`, `firstLinear`, `secondMasked`, `weighted` are exactly the first two lines. Its chronological selectors take the last two physical contrast rows (the “last new clock” is the same as the last still-unused row because clocks are distinct). The first two physical contrast rows in forward order are distinct other rows. Call their reflected clocks $d,h$. Apply `rank_three_forward_mask_with_source` and `Width24RankThreeWeakMask.forward_prefix` to $R=X,X^2$ at the first and $R=X(X-(1-d))$ at the second. These kill the one possible earlier origin and, at the second, the first contrast predecessor; the terminal is not a predecessor. The affine reflection `PositiveRule19.integral_reflect` gives the third line. This does not presuppose any numerical order of the four clocks.

The raw global paid degree is $1+8+6=15$, equivalently the weight-$X$ rule is **degree 14 before its weight**. In the reverse signed law the test $ZT$ costs at most $4+6=10$, not 11. All local and reference sign tests below use only the finite exact positive rule `PositiveIntervalGrid19` and its oriented affine/reflection operations, which are valid before/after order-preserving transport. The local first and second primitive payments have raw degree at most 6.

## Selected roots and reusable finite comparison

On the strict positive unit mesh, remove zeros of $F$. If there are at most six sign changes, put one linear separator in each opposite-sign adjacent nonzero gap (strict midpoint works), with global sign chosen so that $F T$ is nonnegative at all mesh points and positive at a live point. A live point exists since $F$ has degree 8 and the 19 points are distinct. The degree of $T$ is at most six, contradicting the paid weighted orthogonality. Seven disjoint strict sign gaps therefore produce at least seven distinct interior roots in the chosen ordered extension. Factoring seven leaves a linear polynomial. In fact all eight roots are simple: a repeated root would leave at most six odd-multiplicity roots, whereas seven disjoint opposite-sign intervals each need an odd-multiplicity root in the fully split factorization. There is at most one non-interior root, no root at 1, and a root at 0 can only be a $Q$ root. In particular $Q$ has at least three strict interior roots.

The following standard finite comparison is useful here and for other stopped-clock arguments. Take two positive densities $\rho_0,\rho_1$ of a common finite positive unit rule. If $\rho_1/\rho_0$ is nondecreasing at the mesh points and the threshold $s$, then
$$
 \int \rho_1(X)(X-s)L^2\ \ge\
 \frac{\rho_1(s)}{\rho_0(s)}\int \rho_0(X)(X-s)L^2
$$
whenever raw degree is in budget. The summands in the difference are individually nonnegative. When both corresponding rules have $n$ positive weighted nodes and degree $2n-1$ before density, the number of nodes strictly above $s$ is the maximal dimension of a subspace of the $\deg L<n$ coefficient space on which the displayed mass with $X-s$ is positive definite. This is evaluation isomorphism via Lagrange; a subspace of larger dimension meets the kernel of projection to above-threshold coordinates. Thus monotone ratio gives coordinatewise increasing node order (reverse for decreasing ratio), with no quadrature formula for the change of density. For $n=7$ all comparisons here have density degree $\le2$ and raw degree $2+1+2(6)=15$. This is the `FiniteGaussianLocalizer` comparison in a form suited to simple rational bracket certificates.

Let $J_7,J_8$ be monic orthogonal polynomials for density $X$, $L_7$ for $X(1-X)$, and $K_7$ for $X^2$. Their increasing roots will be denoted by the corresponding polynomial letter with a subscripted root position; $\xi_i$ are the $J_8$ roots. The exact brackets are in the script below. The first three are positive seven-node rules exact before density through degree 13: use monic division and Lagrange from orthogonality through degree six. Positivity of each weight follows from the squared cardinal of degree 12 on the fixed positive mesh. The same rule/positivity argument works for every $\rho$ below, with no assumption that the actual stopped nodes are independent of $\rho$.

If $F$ has a non-interior root $e>1$, its other seven roots $t_i$ are the positive Gaussian nodes for $X(e-X)$. The ratios $(e-X)/(1-X)$ and $e-X$ are respectively increasing and decreasing, so $L_{7,i}\le t_i\le J_{7,i}$. If $e\le0$, the density is $X(X-e)$; the ratios $X-e$ and $(X-e)/X$ are increasing and decreasing, respectively (the second is constant when $e=0$); hence $J_{7,i}\le t_i\le K_{7,i}$.

If all eight roots are interior, write $F=J_8+\tau J_7$. Indeed, remove the leading degrees eight and seven, and square-test the remainder of degree at most six against the $X$ weight to get zero. The bracket table shows $J_7$ interlaces $J_8$. Signs at the $J_7$ roots are independent of $\tau$; the monic tails give one simple root of $J_8+\tau J_7$ in each of the eight strips cut by $J_7$. When $\tau$ increases, every root strictly decreases: evaluate the newer polynomial at an old root; its sign is that of $J_7$ on the strip, which is the sign on the right of the newer polynomial's root. The two monic boundary members $XK_7$ and $(X-1)L_7$ belong to the same family by the same degree-six orthogonality. Their roots at 0 and 1 bracket the possible parameters. In particular
$$
 K_{7,i-1}\le t_i\le L_{7,i}\ (2\le i\le7),\qquad
 t_1<L_{7,1},\quad t_8>K_{7,7}.
$$
If $\tau\ge0$, additionally $t_i\le \xi_i$; if $\tau\le0$, $t_i\ge \xi_i$. These are abstract orthogonal references, not fibre evaluations.

## Two-node local reference test

If the first left port has exactly two $Q$ roots $r_1<r_2$ below $a$ and the other two $r_3,r_4>a$, rescale $X=aY$. Its two equations make $r_1/a,r_2/a$ the two-node Gaussian rule for $Y(U-Y)(V-Y)$, where $U=r_3/a,V=r_4/a$ are greater than 1. Exactness through degree three and positive weights again follow by division and cardinal squares. At the right port use $Y=(1-X)/(1-d)$ and the analogous ordered roots outside that reflected interval. If $1\le R\le U,\ 1\le S\le V$, the actual/reference density ratio is increasing, since each factor is $1+(U-R)/(R-Y)$ or its analogue. For $\deg L\le1$ apply the localizer inequality with threshold $s$, raw degree at most 6. A positive-definite $2$-by-$2$ reference Gram implies both actual nodes $>s$: if at most one is above, an affine $L\ne0$ vanishing there would give a nonpositive actual form. A single positive affine reference direction implies the larger node $>s$. The exact Gram entries and all case comparisons are checked by the script below (finite decimals here are exact rationals).

## Excluding the full noncrossed sign class

Suppose $a<d$. Both must be in $(0,1)$. In detail, if $a<0$, all four $Q$ roots are interior (the mark $a$ is the sole exterior root of $F$); $XQ$ then has fixed strict sign on $(a,0)$, contradicting the first payment. If $d>1$ the first right payment analogously fails. Any $a>1$ or $d<0$ in the assumed order would already give two exterior marks. The endpoints 0 and 1 are not marks.

Each of the first two tests on its respective interval forces at least two sign changes of $Q$ there: were there at most one, multiply by the signed separator of degree at most one and use the positive affine mesh, with the density $X$ or $1-X$. Hence
$$
 r_1<r_2<a<d<r_3<r_4
$$
are all four $Q$ roots, strictly interior. If $0<c<a$, the left masked test on $[0,c]$ and its difference from the first-port masked test on $[0,a]$ supply a change on both sides of $c$ thus $r_1<c<r_2$. If $c>a$, the difference supplies a change on $(a,c)$, so $c>r_3$. If $c<0$, $X(X-a)Q$ has fixed strict sign between $c$ and 0, so this is impossible. Right-reflecting gives $r_3<h<r_4$ when $h>d$ is interior, $h<r_2$ if $h<d$, and $h>1$ is impossible. These sign checks use only exact low-degree affine integrals on proper intervals, even exterior ones.

- **Eight interior roots.** Let $m$ count the members of $\{c,h\}$ below $a$. If $m=0$, $r_1=t_1,a=t_3$ and $r_1/a<.051/.226<.226$; the $R=S=1,s=.226$ reference forces both roots above that threshold. If $m=2$, $r_4=t_8,d=t_6$ and the small reflected ratio is below $.021/.161<.2$; use $R=S=1,s=.2$ at the right. If $m=1$, $r_2=t_3,a=t_4,r_3=t_6,r_4\ge t_7$; hence $U>.759/.5>1.5$ and $V>.896/.5>1.7$. For $\tau\ge0$, $r_2/a<.287/.399<.72$; for $\tau\le0$, $r_2/a<.319/.454<.72$. Contradict the positive affine direction at $(R,S,s)=(1.5,1.7,.72)$.
- **One exterior mark $e>1$.** It must be $c$. For the seven remaining nodes use $L_{7,i}\le t_i\le J_{7,i}$. If $h>d$, $r_1=t_1,a=t_3$ and the small left ratio is below $.057/.318<.2$, impossible. If $h<d$, $r_2=t_3,a=t_4,r_3=t_6,r_4=t_7$. Then $r_2/a<.353/.5<.72$, but $U>.838/.548>1.5,\ V>.949/.548>1.7$, impossible by the same large-root reference.
- **One exterior mark $e<0$.** It must be $h$. Use $J_{7,i}\le t_i\le K_{7,i}$. If $c<a$, $r_4=t_7,d=t_5$ and the small reflected ratio is below $.023/.24<.2$, impossible. If $c>a$, $r_1=t_1,a=t_3,r_3=t_5,r_4\ge t_6$ and $r_1/a<.089/.352<.26$. But $U>.734/.4>1.8$, $V>.885/.4>2.2$, contradicting positive definiteness at $(1.8,2.2,.26)$.

Thus $a<d$ is impossible, and equality is excluded by the actual distinct labels.

## Bonus: three strict Q roots cannot have both secondary stops outward

Let $r_1<r_2<r_3$ be the strict interior $Q$ roots, and let $e\notin(0,1)$ be the fourth; all marks are interior. The first pairs force $d<r_2<a$. If $c>a$ and $h<d$, subtract the first masked integrals as above to obtain the exact seven-node order
$$
 h<r_1<d<r_2<a<r_3<c .
$$
For $e>1$, the $L_7,J_7$ brackets give $r_1/a<.18025/.68155<.265$, $r_3/a>.838/.735>1.14$, and $e/a>1/.735>1.36$. The left port has exactly two roots, and $(R,S,s)=(1.14,1.36,.265)$ excludes it. For $e\le0$, use $J_7,K_7$ at the right: the small reflected ratio is below $.115/.6<.2$ since $r_3=t_6>.885$ and $d=t_3<.4$. The right port again has exactly two roots and $R=S=1,s=.2$ excludes it. This branch includes $e=0$ without any division by $e$.

Neither result settles the whole crossed branch. For four strict interior $Q$ roots, crossing remains necessary; for three, at least one secondary clock must point inward. Any further pruning should start on that reduced region.

## Exact reproducibility

Run the following with standard Python fractions. This independently checks polynomial moments, rational isolating signs, interlacing, reference localizer entries, and strict inequalities in the disjoint cases. It is not a Lean certificate or a computation on physical fixed fibres.

Run [`checks/check_crossing.py`](checks/check_crossing.py) with `python3`.
