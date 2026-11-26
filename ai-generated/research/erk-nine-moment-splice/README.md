# Exact universal-ring order nine in 16 explicit stages

This literal tableau pays all rooted order conditions through nine in
16 stages over $\mathbb Z[1/9!]$, and has exact order nine in every
nonzero commutative ring in which $9!$ is a unit. The requirement on
$9!$ is necessary by the tall tree. The count improves the prior
18-stage paid moment splice and the older 21-stage uniform-path
construction, without changing the real-algebraic upper bound of 13
or asserting a minimum over any coefficient domain.

The common coefficient denominator is
$35271936000=2^{11}3^9 5^3 7$. Put
$v_4\coloneqq[\bullet]^{\#3}$ and
$u\coloneqq[\bullet]\#[v_4]$.
The tree $[\bullet]^{\#3}\#[u]$ has ten vertices and factorial
240. Its raw output is $115/27216$, and its cleared defect is
$8/567$. The defect is a unit, establishing exactness after each
nonzero unital base change. The literal $A$ and $\mathbf b$ are
in tableau.json. The standalone check.py reconstructs the
tableau by small paid linear interpolations, checks every
denominator and all 486 paid rooted equations, and checks this next
defect.

The forward nine-stage prefix is unchanged from the 18-stage
moment splice. It starts with the seven-stage paid order-six seed
and its literal endpoint. The five actual polynomial readouts
$E_0,E_1,I_1,I_1^x,E_{1/2}$ define the degree-four projection
$\Pi$. Here $E_z$ is evaluation at $z$, $I_z$ is integration from
0 to $z$, and $I_1^x$ is the integral against $x$ on $[0,1]$.
The last forward row uses the degree-three reconstruction from
the first four readouts to produce the local evaluation
$E_{1/2}$. On a tree $t$, the discrepancy
$\rho_t=g_t-\Pi\mathbf u_t$ is zero through order five,
vanishes at 0 and 1 through order seven, and has integral zero
through order six. Here $g_t(x)=|t|x^{|t|-1}/t!$ is the exact
polynomial and $\mathbf u_t$ is the prefix tree-weight vector.

Use the nine grouped quadrature clocks of the previous splice:
$-1/2,3/2$ carry $-1/23625$ each;
$0,1$ carry $481/7560$ each;
$1/4,3/4$ carry $17408/23625$ each;
$1/3,2/3$ carry $-729/1000$ each;
and $1/2$ carries $6/7$. It integrates every polynomial through
degree eight. Keep the clock-zero weight at the prefix origin.
Split each of the clock-one and two quarter masses into one
unit weight 1 and its remainder. The reverse clocks are now
$$
   (1,-1/2,1/3,2/3,1/4,1/2,3/4,3/2,1/4,3/4,1).
$$
At a repeated clock the remainder is at the later label. The
reverse strictly lower triangular matrix $L$ uses just its
first four labels as donors, all distinct and unit-weight.
Write $y_i=1-x_i$. Prescribe
$L\mathbf1=\mathbf y$ and
$L\mathbf y=\mathbf y^{\odot2}/2+\mathbf u$.
On the seven distinct nonendpoint labels 2 through 8, make
$w_ix_i y_i u_i$ proportional to the Lagrange leading
coefficient, with $u_2=-y_2^2/2$ fixing the common factor.
Thus $\mathbf u$ kills $x(1-x)$ times polynomials through
degree five; this is even more than needed for order nine.

Row 1 is zero, row 2 reads only row 1, and rows 3 and 4 read
the first two donors. The matrix of donor inputs
$\mathbf1,\mathbf y,\mathbf y^{\odot2},\mathbf u$ on labels
1 through 4 has determinant $5/168$, a unit. For later nonzero
rows use these donors and pay their two remaining actions
by requiring that
$$
       L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\qquad L\mathbf u
$$
annihilate $x(1-x)$ times degree-at-most-three polynomials.
Only labels 5 through 8 need nonzero target actions after
the four donor rows; the corresponding weighted determinant
is $9/1284505600$. The final clock-one row is zero.

Let $T$ be the weighted transpose of $L$ in forward chronology,
$E$ evaluation at the suffix clocks, and $J=I_x$ the primitive
operator. The lower-left block is $(EJ-TE)\Pi$. Since every
live donor column has a unit weight, the normalized transpose
does not invert any of the other masses. For the full nonlinear
proof, an extension has suffix error
$e_{[t]}=Te_t+(TE-EJ)\rho_t$. Since a first primitive error
costs six nonroot vertices, through degree eight each rooted
product has at most one such error. Propagating it gives
weights against words of length at most two in $T$ and clock
multiplication. Move each word to the reverse side. If its
actual value on $\mathbf1$ is $\mathbf h$ and its scalar
value with the adjoint primitive $J^*f(x)=\int_x^1 f$ is $P$,
the weighted effect of a source $f=\rho_t$ is
$$
 \langle L\mathbf h-EJ^*P,Ef\rangle_w
       -\langle\mathbf h-EP,EJf\rangle_w .
$$
This is polynomial Fubini and quadrature, with degree at most
eight. The clock-zero contribution vanishes because $f(0)=0$.
At word length zero the row sums are exact. At length one the
new error is a multiple of $\mathbf u$, tested only on endpoint-
vanishing polynomials through degree six. At length two the
word error is $0$ or $\pm\mathbf u$, and its next error belongs
to the span of the two prescribed vectors and $\mathbf u$.
The source then has degree five and both endpoint zeros.
Moreover its primitive has degree at most six and vanishes at
both endpoints, by the exact $I_1$ read of the seed. All these
terms are killed by the listed moments.

There are four literal mergers. The unused clock-one label has
zero suffix row and prefix row $I_1\Pi$, identically the old
forward endpoint. Both pairs of quarter labels are unused
as reverse donors, so each pair becomes two identical forward
rows with its common prefix part $I_x\Pi$ and no suffix part.
The midpoint suffix label is also not a donor. Its prefix
read $I_{1/2}\Pi$ equals the old ninth row: the difference
from the degree-three reconstruction has the form $x(1-x)Q$,
$\deg Q\le2$, and zero integral and first moment. Its odd part
about $1/2$ is zero by the unit integral
$\int_0^1 x(1-x)(x-1/2)^2=1/120$. Its symmetric part has zero
half-interval integral. Redirect all outgoing coefficients and
transfer the output weights, giving $9+11-4=16$ stages. The
reduced checker exhausts equality of the padded rows and confirms
all 16 remaining rows are distinct.
