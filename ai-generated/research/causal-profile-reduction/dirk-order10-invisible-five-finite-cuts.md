# The five-distinct invisible DIRK10 cut: exact trace, conic, and finite exclusions

Assume actual **HasOrder 10** on eleven lower-triangular stages,
with the five distinct invisible dirty rows of the preceding
note. Let $g=Ac^2-c^3/3$, and use its degree-at-most-three
fit $U$ on the five dirty nodes. Write $V$ for the monic dirty
nodal polynomial. The six clean nodes are the full Lobatto set,
with all weights individually nonzero, and
$$
 H_t(x)=42xJ_4(x)=U(x)M(x)+aV(x),\qquad \deg M\le2.
$$
The new exclusions are:
1. $U(0)\ne0$ and $U$ is nonzero at the *first* nonzero clean
   stage, in characteristic zero and characteristic 227.
2. The branch $a=0$ and all five ghosts before the first
   nonzero clean stage is impossible in characteristic zero
   and characteristic 59.

A clock-only Lean certificate checks the finite arithmetic.
The tableau-to-scalar reduction and general conic formulas
are mathematical. Neither result excludes every five-distinct
candidate or changes the unrestricted 11–12 bound.

## The complete clean leakage band

Let $T=I H_t$, where $I P(x)=\int_0^x P(t)\,dt$ is the formal
zero-constant primitive. The physical terminal indicator $e_t$
has exact grade-five profile $H_t$ and $A e_t=0$. Hence $T(c)$
is a true grade-six defect. The scalar has $T(1)=1/30$, so it is
independent of $g\mathcal P_3(c)$, which vanishes on all clean
rows. The anchored Cauchy test separates polynomials of degree
at most four from $F_6$ (the true origin and clock probes 0
through 3 are paid). As $E_6$ has rank ten, $F_6$ has rank at
most five. The five columns just exhibited attain it:
$$
 F_6 = g\mathcal P_3(c) \oplus K T(c).
$$
The finite clock checks verify that $T$ is nonzero at each
nonzero clean node. The same separation with degree $10-j$
and defect grade $j$, for $j=7,8,9$, gives $\dim F_j\le j$.
These bounds are attained by all five dirty indicators
(from $g\mathcal P_4(c)$) and the independent clean traces
$T(c),C T(c),\ldots,C^{j-6}T(c)$. Thus the clean parts of
$F_7,F_8,F_9$ are respectively $T$ times affine, quadratic,
and cubic polynomials. $F_4,F_5$ vanish on the clean sites
by their actual rank-two and rank-three ghost bases.

## Two forward scalar restrictions

Use the true grade-three clean-supported column $h=U(c)-g$.
If $U(0)=0$, its first live clean row has clock $s\ne0$.
At that pivot $R h$ (where $R=CA-AC-A^2$) is zero in the clean
coordinate since $R h\in F_5$. Its pivot value is $-A_{ii}^2 h_i$,
so the actual diagonal is zero. The primitives of $h,Ch$
therefore give
$$
 I U(s)=I(xU)(s)=0.
$$
There is another live clean row, since a nonzero cubic vanishing
at 0 cannot vanish at more than two other clean labels. Let $t$
be the clock of the next one. The input $(C-s)h$ is zero through
the preceding row at $s$, so its Volterra image vanishes there.
Its clean trace in $F_6$ is a constant times $T$, and $T(s)\ne0$;
therefore the clean trace is identically zero, refunding the
diagonal at $t$. Its grade-five primitive gives
$I((x-s)U)(t)=0$. The three conditions on the coefficients of
$x,x^2,x^3$ are nonsingular for every distinct pair from the
five nonzero fixed clean sites modulo 227 and modulo 59.

Now suppose $U(s)=0$ at the first nonzero clean stage. The
anchored grade-four column $v=Ch$ is zero through $s$. Since
$Rv$ is zero there, its grade-six clean trace $K T$ vanishes
everywhere. At its first later live site $t$, the diagonal
is therefore zero. The actual $A v$ is zero at $s,t$ and
has exact grade-five clean profile $I(xU)$; the actual
$A C v$ is zero at both sites and has grade-six clean
discrepancy a single multiple of $T$. Hence
$$
 U(s)=I(xU)(s)=I(xU)(t)=0,\qquad
 T(t)I(x^2U)(s)-T(s)I(x^2U)(t)=0 .
$$
This four-by-four coefficient matrix is nonsingular for every
distinct pair of nonzero clean clocks modulo 227. The repeated
factor restrictions require no conjectural vanishing of the
grade-six trace.

## An exact entire-block conic

This step uses no split-prime certificate. It holds over paid
fields for which the six clean quadrature weights are nonzero.
For a nonzero clean clock $x$ write $b_x$ for its true output
weight. Let $B=(X-1)J_4$ be the monic polynomial of the five
nonzero clean clocks and $W=XJ_4$ that of the five nonterminal
clean clocks. Use the genuine marked row
$G=\beta(1-C)^2A-\beta(1-C)^3/3$ as in the previous note.

There is a single bivariate polynomial $Q(X,Z)$ of total degree
at most two, monic quadratic in $X$, such that on every
nonzero clean row $x$ and dirty donor $z$,
$$
 A_{x,z}=\frac{\kappa Q(x,z)}{b_x B'(x)\,g(z)V'(z)},\qquad
 G_z g(z)V'(z)=\kappa\ne0.
$$
No original ghost clock is shifted or identified with a clean row.
Indeed, the row constraints $Ag=A(Cg)=0$ at clean $x$ give the
degree-at-most-two barycentric numerator in $z$. The literal
column constraints $\beta A$ and $\beta C A$ vanish at a dirty
donor (its weight is zero); the origin row is zero. Thus there
is also a degree-at-most-two barycentric numerator in $x$ on
the five nonzero clean labels. The two grid interpolations
give bidegree at most $(2,2)$. Its leading coefficient in $x$
is $\kappa$, from $G_z=\sum_x b_x A_{x,z} x^2$. The next
reflected defect $D_3$ annihilates $E_5$, so it is a combination
of $G,CG$, which are independent on the ghost sites. On a ghost,
$D_3(z)/G_z$ is
$3-\sum_{x\ {\rm clean},\,x\ne0}x-[X^1]Q(X,z)$,
by the next barycentric coefficient. Thus the coefficient of
$X$ is affine in $z$, giving the stated total degree.

This also determines the whole receiving clean block in terms
of $Q$ and the marked weights $G_q$. For nonzero clean $x$ and
nonterminal clean $q$, let $\ell_q$ be the usual degree-four
cardinal on the five labels of $W$. Then
$$
 A_{x,q} = I\ell_q(x) + \frac{G_q Q(x,q)}{b_x B'(x)}.
$$
To prove it, apply the exact clean grade-five primitive to
$\ell_q(c)$, note the terminal column is zero, and replace
the ghost sum by the negative of the clean sum via $G$'s
annihilation of $E_6$ on the polynomial $Q(x,Z)\ell_q(Z)$
of degree at most six. These formulas give simultaneous
causal restrictions; the three zeros preceding the last
nonterminal clean donor determine $Q(\cdot,q_{\rm last})$.
They do not by themselves yield a contradiction.

## The fixed-factor branch with a wholly early ghost prefix

Suppose $a=0$. Then $U$ is a nonzero scalar multiple of a monic
cubic factor of $xJ_4$ by the degree bounds. Since $U(0)\ne0$,
its roots are exactly three interior Lobatto nodes. The remaining
interior node is the first live clean stage. This follows either
from the general characteristic-zero first-stage test, or directly
in characteristic 59: $I(xU)$ is nonzero at every root of this
fixed cubic factor, whereas if any such clean row came first,
its true primitive $A(Ch)$ would be zero there.

The row $G$ is zero on clean sites where $U$ is nonzero, since
the first four moment tests on $\sum_{\rm clean} G_i U(c_i)c_i^k$
are paid (test $C^k h\in E_6$), and at most two nonterminal
clean sites can contribute. The terminal $G$ coordinate is
already zero. At the three later clean interior roots of $U$,
$G$ is nonzero: the five ghost sites and these three sites are
eight distinct clocks, since $U$ is nonzero on dirty sites,
and $G$ on them kills powers 0 through 6. Nonzero $G$ on this
eight-site set is the one-dimensional barycentric row, with
every coefficient nonzero.

Assume all five ghost rows precede the first nonzero clean row
in physical order. The reverse prefix covering the four nonzero
interior clean rows then has no ghost donors, even in a product
with the unweighted marked row $G$. In reverse chronological
order let their reflected clocks be $u,v,w,z$, and write
$\xi_x=G_i/b_i$ at clock $x$. We know
$\xi_u=u^3/6$, $\xi_v,\xi_w\ne0$, and $\xi_z=0$.
For a receiving clean index $i$ normalize its reversed donor
taps as $b_j A_{ji}/b_i$, with unchanged diagonal. This is
just local normalization of original row equations, not an
assertion that the normalized prefix has full order.

At $z$, the power moments $k=1,2,3,4$ are exact with right
sides $z^{k+1}/(k+1)$ because $D_1=0$, $D_2=G$,
$D_3\in G\mathcal P_1$ and $D_4\in G\mathcal P_2$. Thus its
four normalized taps on $u,v,w,z$ are the solution of the
fixed square Vandermonde-power system. Denote its first
three taps by $a_u,a_v,a_w$. Moreover $GA\in G\mathcal P_1$
and $(GY)A\in G\mathcal P_2$: these follow by paid
annihilation of $E_5$ and $E_4$, respectively, and the zero
terminal column. Thus both rows vanish at $z$, so
$$
 \sum_{x=u,v,w} a_x\xi_x=0,\qquad
 \sum_{x=u,v,w} a_x x\xi_x=0 .
$$
These equations determine $\xi_v,\xi_w$ from the earned
$\xi_u$, with nonzero divisors in the certificate.

At $v$, the power-1 and power-2 readings give the two
normalized taps $(t_v,d_v)$ using the known $\xi_v$ in
the second right side. The normalized ratios for the
affine $D_3/G$ are then $3u/2$ at $u$ and
$(t_v u^3+d_v v^3-v^4/4)/\xi_v$ at $v$.
The affine $GA/G$ likewise has values $u/2$ at $u$ and
$(t_v \xi_u+d_v\xi_v)/\xi_v$ at $v$. Call these affine
functions $\Gamma$ and $L$ respectively. At $w$, the
power-1, 2, 3 readings determine three taps with right
sides $w^2/2,\ w^3/3+\xi_w,\ w^4/4+\Gamma(w)\xi_w$.
Their scalar action on $(\xi_u,\xi_v,\xi_w)$ must give
$L(w)\xi_w$. The fixed-clock test checks the opposite
inequality in all 24 possible orders modulo 59.

## Exact residue certificates and scope

The supporting Lean and Python files check the quartic
splits, no-zero trace, ranks, and intermediate nonzero
divisors in $\mathbb F_{227}$ and $\mathbb F_{59}$. Both
primes preserve the distinct fixed roots. In characteristic
zero one reduces only the fixed clock splitting field at a
maximal ideal above the selected prime. Its clock generators
are integral over the corresponding localized rational
ring (the quartic is monic there). Each required minor and
later divisor has nonzero residue in every reduced clock
ordering, and is a unit at the selected prime. The residual
nonzero test then transfers back. No unknown tableau
entry or weight is reduced modulo a prime.

In characteristic 227 the forward restrictions apply
directly. In characteristic 59 the origin and fixed-factor
primitive tests and wholly early ghost obstruction apply
directly; the general first-interior exclusion is not
claimed there. The cases with nonzero coefficient of $V$
and with a later/interleaved ghost remain open here.
