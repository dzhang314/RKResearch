# Five invisible cubic defects: repeated-clock exclusion and a clean tail

This note concerns actual DIRK order ten on eleven stages over a
field. Put $g=Ac^2-c^3/3$. Assume all its dirty rows are invisible
($b_i g_i=0$) and **exactly five physical rows are dirty**. Denominators
only use the paid orders. The five-row case with four distinct
dirty clocks is excluded below. With five distinct dirty clocks,
there is a scalar cubic fit and a fixed clean-stage skeleton.
The case where all dirty rows share one physical clock is separate.
Neither the distinctive-clock skeleton nor this note is a new
unrestricted 12-stage bound. The results here are mathematical.

## Six clean Lobatto clocks

The six-possible-clock lemma of the signed dirty inventory applies
to the clean clock set: invisible rows have no output mass, and
the true terminal is clean at 1. There are only six physical
clean rows, including the origin and terminal. Thus the six clocks
are distinct, the ordinary quadrature is exactly the six-point
Lobatto rule, and all six individual weights are nonzero. The
proof uses the first four paid moments of the degree-six nodal
hull $x(x-1)J_4(x)$ and the degree-five Lagrange cardinals, as
in the four-invisible-row note.

Write $G=\beta Y^2 A-\beta Y^3/3$, where
$Y=\operatorname{diag}(1-c)$. This is the genuine reflected cubic
row, not a defect of a guessed transposed method. It annihilates
$E_6$ and is nonzero at the latest active row whose clock is
different from 1: there its clock complement is $u\ne0$,
the diagonal is $u/2$ by the exact reflected quadratic condition,
and $G_i=b_i u^3/6$. It vanishes at all later rows by triangularity.

## Four labels on the five dirty rows are impossible

If there are exactly four distinct dirty clocks, the four
payable columns $g,cg,c^2g,c^3g$ isolate each dirty label
in the row test against $G$. Thus each dirty clock group
has $\sum G_i g_i=0$. The three singleton dirty rows have
$G_i=0$. The only repeated dirty group has two rows. The
paid column $g^2\in F_6\subset E_6$ now gives
$G_1g_1^2+G_2g_2^2=0$ on that pair, in addition to
$G_1g_1+G_2g_2=0$. If $g_1\ne g_2$, both $G$ entries
are zero. If they are equal, their sum is zero.
Thus every dirty label's unweighted aggregate of $G$ is
zero, including if a dirty clock also equals a clean clock.

The clock tests of $G$ through degree five now isolate
the six distinct clean rows, giving zero at all six.
But the earned nonzero $G$ entry above is at an active row,
necessarily one of those clean rows. Contradiction.
The two paid constraints $g,g^2$ are important; the first
one alone does not separate two unequal dirty amplitudes.

## Five distinct labels: nonzero reverse entries and cubic fit

Let $V(x)$ be the monic nodal polynomial of the five distinct
dirty clocks. The four paid tests against $g\mathcal P_3(c)$
imply the barycentric formula
$$
 G_i g_i=\kappa/V'(c_i)
$$
on the five dirty rows. If $\kappa=0$, all ghost entries of
$G$ would vanish, and its six clean clock tests would force
$G=0$. Hence $\kappa\ne0$ and every ghost entry of $G$ is
nonzero. No ghost row can follow the latest active nonterminal
row; that row is physical stage 10, with nonzero diagonal.

The paid $g^2$ test says
$\sum_{i\ {\rm dirty}}g_i/V'(c_i)=0$. This is the leading
coefficient of the interpolating quartic for the five values
$g_i$. Thus the actual dirty amplitudes are evaluations of a
single nonzero polynomial $U$ of degree at most three.
Also $\dim E_6=10$: the six clock powers through degree
five independent on the clean rows and the four independent
dirty columns $g\mathcal P_3(c)$ give the lower bound,
and $G\ne0$ gives the upper bound.

In this branch $F_5=g\mathcal P_2(c)$, so every true E5
column has literal evaluation of its formal scalar on the
six clean rows. In particular the physical terminal
indicator has scalar profile $H_t(x)=42xJ_4(x)$:
on the six clean rows its degree-at-most-five scalar
is the usual terminal cardinal. Thus
$H_t(c)-e_t=gM(c)$ for a polynomial $M$ of degree at most two.
On the five dirty rows this gives $H_t(c_i)=U(c_i)M(c_i)$.
Equivalently there is a constant $a$ such that
$$
 42xJ_4(x)=U(x)M(x)+a V(x).
$$
No coincidence between dirty and clean labels is excluded
by this identity.

## Chronology before and after the dirty rows

Each clean row has exact integrating equations on ordinary
clock polynomials of degree at most four, since the primitive
defects through grade five vanish there. Both $Ag$ and $A(Cg)$
vanish there as well. A first nonzero clean row preceded by
at most two distinct dirty clocks would therefore have zero
incoming sums from each of them; its diagonal would have to
equal both $c/2$ and $c/3$. Thus the first nonzero clean row
is at stage 5, 6, or 7.

At least four dirty rows precede the second nonzero clean row.
To see this, let $a,b$ be the first two nonzero clean clocks
in physical order, and look at the prefix through the row
with clock $b$. On the prefix ghost coordinates the two
columns $g,Cg$ are independent, and the taps into the two
clean target rows annihilate them. If there are $k$ ghost
coordinates in the prefix, the observation map from ghost
data into these two clean rows therefore has rank at most
$k-2$. For inputs
$P(x)=x(x-a)(x-b)(s+t x)$, only those ghost coordinates
can feed the two rows: the input vanishes at all prefix
clean clocks. Their outputs are exactly $IP(a),IP(b)$ by
grade-five cleanliness. This map on $(s,t)$ is injective:
if both values vanished, its primitive of degree at most
five would have three double roots at $0,a,b$. Thus $k\ge4$.

Finally, the last ghost is followed by at least three
clean rows, so its physical index is at most eight.
Its indicator belongs to $F_7$ by $g\mathcal P_4(c)$
interpolation; its image under $A$ lies in $F_8$. Its
two paid ordinary moments have degrees 0 and 1 in the
probe. If there were at most two later clean rows, their
distinct clocks and nonzero weights would force the
column entries into both to vanish. No earlier row can
use the column and there are no later ghosts. The unweighted
stage could then simply be removed without changing any
order condition, contradicting the 11-stage floor.

The cubic factor identity, all-five-live ghost entries in
the true reverse row, and these prefix bounds are simultaneous
necessary restrictions. They do not yet exclude the five-distinct
case.

The separate [finite cuts](dirk-order10-invisible-five-finite-cuts.md)
exclude a fixed-factor branch with all five invisible stages early.
They do not exclude arbitrary chronological interleaving.
