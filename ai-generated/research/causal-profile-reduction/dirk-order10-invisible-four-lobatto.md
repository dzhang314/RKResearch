# Four distinct invisible dirty rows are impossible in DIRK10/11

Suppose an eleven-stage lower triangular tableau has the actual
reviewed **HasOrder 10**. Put $g=Ac^2-c^3/3$ and assume every dirty
row ($g_i\ne0$) is unweighted ($b_i=0$). This note excludes the
case of exactly four physical dirty rows at four distinct clocks.
It works over every characteristic-zero field and in characteristic
227. There is no sign, ordering, or realness hypothesis. It does
not exclude the several other invisible or single-clock branches
and does not change the unrestricted 11–12 stage interval.

The accompanying exact Python and portable Lean scalar certificates
check **only fixed clock data**. The order-to-matrix deduction
below is mathematical, not a native Lean tableau theorem.

## The repeated clean clock and its marked reverse rows

The saturated native ranks are $\dim E_4=7,\ \dim E_5=9,\
\dim F_5=3$, with $C(2),D(1),D(2)$, true zero origin, terminal
clock $1$, nonzero terminal weight, and zero terminal column.
Use $F_5=g\mathcal P_2(c)$, by independence on the four distinct
dirty clocks. The four ghost indicators belong to $E_6$ by
interpolation from $g\mathcal P_3(c)$.

Write $\beta=(b_i)_i$ as a row, $Y=\operatorname{diag}(1-c_i)$,
and define the divided genuine reflected defects
$$
 D_k=\beta Y^k A-\beta Y^{k+1}/(k+1),\qquad G=D_2.
$$
All uses of $D_k$ below are true marked rows from the original
tableau, not formal order of a weighted-transpose tableau.
The paid $D_0,D_1$ are zero. The row $G\ne0$ annihilates $E_6$:
at the latest active nonterminal numerical clock, put $u=1-c_i$.
The diagonal there is $u/2$ by $D_1$, and $G_i=b_i u^3/6\ne0$
by causality. In particular $G$ vanishes past this row (later
output-active sites all have reflected clock zero). Since the four
dirty indicators are in $E_6$, $G$ vanishes at them.

There are at most six distinct clean clocks: seven such clocks
would give seven clock powers independent of the four dirty
indicators, contradicting $G\ne0$. There are at least six by the
terminal-containing possible support test in the signed inventory;
all ordinary quadrature comes from the clean rows. The seven
physical clean rows therefore have one repeated clock and six
distinct labels, including 0 and 1. The latter are exactly the
six-point Lobatto rule labels: the four interior roots of
$$
 J_4(x)=x^4-2x^3+\tfrac43x^2-\tfrac13x+\tfrac1{42},
$$
plus 0 and 1. Indeed, multiply the interior nodal polynomial
by $x(x-1)$ and use its first four paid moments against the
unit functional; the weighted beta matrix determines $J_4$.
Their aggregate weights, obtained by integrating the degree-five
cardinal polynomials, are $1/30$ at each endpoint and
$7(1+6x(1-x))/60$ at each interior node. They are all nonzero
in the claimed fields. The two rows at the repeated clock need
not both have a nonzero weight or have weights of the same sign.

The clean clock powers through degree five now separate the six
distinct clean labels. Hence $G$ is nonzero exactly on the two
repeated clean rows, where its values are opposite. Its later
physical entry is the latest active row with reflected clock
$u\ne0$. Denote the later physical stage by $p$, the earlier
copy by $q$, and their ordinary aggregate weight by
$W=b_p+b_q\ne0$. Then $A_{pp}=u/2$ and $G_p=b_p u^3/6$,
while $G_q=-G_p$.

All four ghost entries of $GA$ are nonzero. The row annihilates
$E_5$, since $G$ annihilates $E_6$. Its ghost entries times $g$
annihilate powers 0,1,2 on four distinct labels, so a zero at
one forces zeros at all. If they were all zero, the six clean
clock moments through degree five would give $GA\in K G$.
This is impossible: the equality subspace of the repeated pair
would then be invariant under $A$ and componentwise products,
so every rooted-tree column would agree on the pair. Folding the
later stage into the earlier by adding its donor column and
weight, then deleting its row, preserves lower triangularity
and all order conditions, contradicting the 11-stage floor.
In particular no ghost is physically after $p$, which is
therefore stage 10. No assumption on the location of $q$ is made.

Thus $\operatorname{Ann}E_5=\operatorname{span}(G,GA)$ by
rank two. Also $\operatorname{Ann}E_4$ intersected with the
terminal-zero constraint has dimension three: the terminal
indicator is outside $E_4$ by the reviewed unanchored
endpoint-Cauchy test. The rows $G,GA,(GA)Y$ are all in this
intersection and are independent, because $GA$ has four nonzero
ghost entries at distinct clocks while $G$ has none there.
Consequently
$$
 D_3=\alpha G+\theta GA,\qquad
 D_4=\alpha' G+(\mu GA+\nu (GA)Y).
$$
Set $\kappa=(u^3/6)\theta$ and $\Lambda(y)=(u^3/6)(\mu+\nu y)$.

## Four cuts in reverse physical order

Number the ordinary clean clocks other than the repeated clock
and terminal in *reverse physical order*. Their reflected values
are distinct. Let the first three be $v,w,z$; together with $u$
they are four distinct members of $\{1\}\cup\{J_4=0\}$.
Ordinary weights at these sites are individually nonzero.
A reflected primitive at one such site receives paid contributions
only from output-active rows on its reverse prefix. The physical
ghost rows need not be removed: their weights are zero in these
reads. The terminal's reflected clock is 0, so its term in each
power $k\ge1$ is zero.

There is a true reverse Volterra kernel of form
$\lambda=\beta Q(Y)+\delta G$ with nonzero degree-at-most-three
$Q$ and $Q(0)=0$, as certified by the crossed-cubic seed theorem
(using here reflected variable $y$). Its first physical nonzero
entry in reverse order has zero diagonal. It is supported on
the seven clean rows. It cannot pass the first three ordinary
labels $v,w,z$ (else $Q$ would have four distinct roots).
If the earlier copy $q$ has already been passed, the two
vanishing core entries force $WQ(u)=0$ and hence $Q(u)=0$;
then it cannot pass both $v,w$. The first core $p$ has
nonzero diagonal. It remains to check the following cases.

For a target ordinary label $y$ before encountering $q$,
normalize the ordinary donor coefficients by its individual
weight; the coefficient of the first core donor $p$ is
$t=b_p A_{p,i}/b_i$. The equations in powers $k=1,2,3,4$
have right sides $y^{k+1}/(k+1)$. The first core column is
$u^k$ modified by subtracting $\kappa$ at $k=3$ and
$\Lambda(y)$ at $k=4$. The other columns, including the
receiving diagonal, are literal clock powers. This follows
from the marked $D_k$ equations above: $G_i=0$ and
$(GA)_i=G_p A_{p,i}$ until $q$ is encountered.

* At $v$, powers 1 and 2 give $t_v,d_v$. These determine
  $\kappa$ and $\Lambda(v)$ from powers 3 and 4 by dividing
  their uncorrected residuals by $t_v$.
* If $q$ has not appeared by $w$, powers 1 through 3 at $w$
  give $(t_w,s_w,d_w)$. Power 4 gives $\Lambda(w)$ by
  dividing its uncorrected residual by $t_w$. Interpolating
  these two values gives $\Lambda(u)$ and $\Lambda(z)$.
  If $q$ appears only after $z$, the powers 1 through 4 at
  $z$ solve the last ordinary diagonal $d_z$.
* If $q$ appears even before $v$, the only contributing
  nonzero reflected clock for the first two powers is $u$.
  The second moment is $u$ times the first, but the two paid
  right sides then differ by $W u^3/6\ne0$. This case is
  already impossible.

To cover $q$ after one or two ordinary labels without dividing
by $b_q$, compare its primitive reads with those at $p$.
Set $d=A_{qq}$ and
$$
 h=\frac{b_p}{W}\left(\frac u2+A_{p,q}-d\right).
$$
Normalize each off-core tap from ordinary label $x$ by $W$.
The equations at $q$ have right sides $u^{k+1}/(k+1)$;
the diagonal column is $u^k$, the $h$ column is $u^k$
with the same modifications $-\kappa$ at $k=3$ and
$-\Lambda(u)$ at $k=4$, and the off-core columns are $x^k$.
Indeed $G_q=-G_p$, $(GA)_q=G_p(A_{p,q}-d)$, and
$(GA)_p=G_p u/2$. Adding each defect at $p$ to that at
$q$ leaves only the difference times the appropriate
coefficient of $GA$, and the total normalized core tap
including the added stage at $p$ is $d+h$.

* If $q$ appears after only $v$, powers 1 through 3 in the
  columns $h,v,d$ determine these coefficients; power 4
  gives $\Lambda(u)$ by division by $h$. Interpolate with
  $\Lambda(v)$. At the next ordinary label $w$, the two
  same-clock core taps are represented by their aggregate
  and their $GA$ contrast, separately. The four columns
  are ordinary powers of $u,v,w$ (the third is the
  diagonal) and a pure contrast column
  $(0,0,-\kappa,-\Lambda(w))^T$. Powers 1 through 4
  determine the remaining possible diagonal $d_w$.
  The kernel cannot reach $z$ because $u,v,w$ would all
  already be roots of $Q$ in addition to 0.
* If $q$ appears after $v,w$ and before $z$, $\Lambda(u)$
  was already determined using the ordinary rows at $v,w$.
  The four power equations in the columns $h,v,w,d$ give
  $d$ at $q$. Again $z$ cannot be the kernel pivot.

Thus every possible reverse zero pivot is among the tested
diagonals of the clock-only systems.

## Exact good reduction of the clock systems

Modulo 227 the polynomial $42J_4$ has exactly the distinct
roots $24,51,177,204$. The companion certificate checks all
120 distinct choices of $(u,v,w,z)$ from those four residues
and 1. It solves each stated square system, rejects a zero
determinant, and checks that every displayed diagonal and
all divisors $t_v,t_w,h$ used in the interpolations are nonzero.
The differences of distinct clock labels and the paid
denominators 2 through 10 are also nonzero. The Python script
uses exact residue elimination; the Lean proof uses exact
Cramer's rule and kernel evaluation, not floating point.

For characteristic zero, this modular test reduces **only the
clock splitting field**, not any entry or weight of the tableau.
Inside the coefficient field take the finite splitting field
generated over $\mathbb Q$ by the four distinct roots of $J_4$.
Each root is integral over $\mathbb Z_{(227)}$, since $J_4$ is
monic there. The ring generated by all four is finite integral
over $\mathbb Z_{(227)}$, and has a maximal ideal above 227 by
lying over. Upon reduction, the roots remain distinct (the
reduced quartic is squarefree and splits) and produce one of the
checked ordered tuples. Start with the paid denominators and
then proceed in the exact displayed calculation order: each
matrix determinant or interpolation divisor verified nonzero
in that residue field is a unit in the localization at this
maximal ideal, so its division is well-defined there. Each
solution coordinate has the tested residue. A zero diagonal
in characteristic zero would have zero residue, contrary to
the check. This also proves that no singular earlier system
or forbidden division was silently omitted. In characteristic
227 the field already contains the four prime-field roots
and the exact same test applies directly.

Therefore the required reverse zero diagonal cannot occur.
