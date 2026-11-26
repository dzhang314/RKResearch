# Order raising from the seven-stage ERK6 seed: an exact suffix obstruction

The fixed prefix in this note is the seven-stage endpoint-duplicate
tableau of the exact ERK6 minimum witness. The statement is about
extensions preserving its literal strict rows, not about arbitrary
ERK tableaux. Weights at the prefix stages may be changed.
All arguments are algebraic over a nonzero commutative unital ring
with $p!$ a unit; we use the literal cleared rooted equations.
In particular no field positivity is assumed.

## A parallel tail cannot raise the order

For a fixed prefix, write the suffix-by-suffix strict block as
$D$. If $D^k=0$, a context of $k$ successive unary root
grafts reads only a row functional on the child column restricted
to the prefix: the suffix columns of $A^k$ vanish. Thus any
two extensions with this property and order through $p_0$
have identical readouts for every such unary context if the
prefix child columns through order $p_0-k$ span the prefix.
Agreement on that spanning set is exactly the set of already
paid unary equations.

In fact the first six rows of the seed suffice to block a single
parallel layer ($D=0$). Their five clock labels are
$0,1/3,1/2,2/3,1$, with unit pairwise differences.
The bush columns $1,\mathbf c,\ldots,\mathbf c^4$ span the
clock-constant columns on those rows. The defect
$-18(A\mathbf c-\mathbf c^2/2)$ is the coordinate vector
$\mathbf e_2$ there, distinguishing the repeated $1/3$
clock. The six columns thus span by child order five.
The seventh row of the known order-six tableau is itself a
parallel extension of those six. Consequently any number of
new rows in one parallel layer that respect order six leave
the seed's entire unary readout fixed, including the first
unpaid tall-seven defect $-10/3$. Neither new clocks nor
changes to the earlier weights avoid this obstruction.

## A prefix relation with a prescribed nonzero suffix response

In an arbitrary proposed extension set
$$
 \begin{split}
 \mathbf c&\coloneqq A\mathbf1,\quad
 C\coloneqq\operatorname{diag}(\mathbf c),\quad
 \mathbf g\coloneqq\mathbf c\odot(\mathbf1-\mathbf c),\\
 \mathbf y&\coloneqq-18(A\mathbf c-\mathbf c^2/2),\qquad
 \mathbf x\coloneqq A\mathbf y,\\
 \mathbf r&\coloneqq(C-I)\mathbf x-(2/9)\mathbf y
                         -9\mathbf g+45\mathbf g^2 .
 \end{split}
$$
Here coordinate powers and products are componentwise. On the
prefix, $\mathbf y=\mathbf e_2$ and
$\mathbf x=(0,0,2/3,1/3,-9,9/8,81)$. Direct evaluation of the
five clock labels gives
$$
 (C-I)\mathbf x-(2/9)\mathbf e_2=9\mathbf g-45\mathbf g^2
                  \qquad\text{on the prefix}.
$$
For example the values at $1/3,2/3$ are $-2/9$ and at $1/2$
are $-9/16$; the exceptional physical row $2$ is corrected by
$-(2/9)\mathbf e_2$. Hence $\mathbf r$ is zero on all
seven prefix stages.

The stage polynomial of a formal tree column is
$(|t|/t!)X^{|t|-1}$. Unary graft integrates from zero and adding
a leaf at the root multiplies by $X$. The formal polynomials
of $\mathbf y,\mathbf x,C\mathbf x$ are zero. The formal
polynomial of $\mathbf r$, which uses trees of order at most
five, is
$$
 P(X)\coloneqq45[X(1-X)]^2-9X(1-X).
$$
Let $\mathcal I f\coloneqq\int_0^Xf$, let
$\mathcal C f\coloneqq Xf$, and let
$\ell(f)\coloneqq\int_0^1f$. These are polynomial coefficient
operations with the paid divisors. Both $A$ and $C$ preserve
the vectors zero on the prefix; on that subspace their suffix
actions are $D$ and $C_s$. Write $\mathbf b_s,\mathbf r_s$
for the suffix data. Every word $w$ of length at most
$L\coloneqq p-5$ must therefore satisfy
$$
 \mathbf b_s\cdot w(D,C_s)\mathbf r_s
             =\ell\bigl(w(\mathcal I,\mathcal C)P\bigr).             \tag{1}
$$
In particular, using the polynomial beta integral,
$$
 S_k\coloneqq \ell(\mathcal I^k P)
 =-\frac{9k(k-1)(k+1)}{(k+5)!}\qquad(0\le k\le L).                \tag{2}
$$
Indeed $\ell(\mathcal I^k f)=\int_0^1(1-X)^kf(X)/k!$ and the
two needed moments are $(k+1)/(k+3)!$ and
$2(k+1)(k+2)/(k+5)!$. In particular $S_0=S_1=0$, and
each $S_k$ for $k\ge2$ is a unit. Thus for $p\ge7$ a suffix
must have at least $L+1=p-4$ stages. When it has exactly that
many, (2) is the unique full suffix chain at $k=L$. The first
entry of $\mathbf r_s$, every adjacent suffix edge, and the
last suffix weight are then units.

## Economical cyclic coordinates and the two-clock barrier

Suppose the suffix has the economical width $L+1$.
Use indices $0,\ldots,L$ for suffix coordinates. The Krylov
matrix $K=(\mathbf r_s,D\mathbf r_s,\ldots,D^L\mathbf r_s)$
is lower triangular with unit diagonal entries in the sense
that each diagonal entry is a unit. Let $J$ be the strict
shift $J\mathbf e_j=\mathbf e_{j+1}$ when $j<L$, and zero
on the last basis vector. Then $D K=K J$;
$T\coloneqq K^{-1}C_s K$ is lower triangular with diagonal
the physical clocks $\xi_j$, and $\mathbf b_s\cdot K$ is
the row $S=(S_0,\ldots,S_L)$.
In particular, adjacent equal clocks force
$$
       \xi_{j+1}=\xi_j\quad\Longrightarrow\quad T_{j+1,j}=0,       \tag{3}
$$
by the adjacent entry of $C_sK=KT$. This is required even
without any assumption of distinct clocks.

The exact functional identity
$\ell(\mathcal I^a\mathcal C f)
 =\ell(\mathcal I^a f)-(a+1)\ell(\mathcal I^{a+1}f)$
and the words of (1) with one clock letter give
$$
 S J^a T
 =S J^a-(a+1)S J^{a+1}
       +S_L(\xi_{L-a}-1)\varepsilon_{L-a},                       \tag{4}
$$
where $\varepsilon_j$ is the $j$-th coordinate row.
All entries to the left of $L-a$ are paid in (1); the entry
at $L-a$ follows by triangularity. With prescribed clocks,
the one-clock identities determine each column below its
diagonal by reverse triangular solving with pivot $S_L$.
In particular, put
$\alpha\coloneqq S_{L-1}/S_L$ and
$\beta\coloneqq S_{L-2}/S_L-\alpha^2$. They give, in the
available columns,
$$
 \begin{split}
 T_{j+1,j}&=\alpha(1-\xi_j)-(L-j),\\
 T_{j+2,j}&=\beta(1-\xi_j)+\alpha.                                \tag{5}
 \end{split}
$$
For a word $J^a T J^b T J^c$ with $a+b+c+2\le L$,
apply (4) to the first $T$. The first two resulting terms
are the reference by the same functional identity and the
one-clock conditions. The last gives the exact additional test
$$
               (\xi_{L-a}-1)\,T_{L-a-b,c}=0.                     \tag{6}
$$
Notice that the tested entry is at least two below the
diagonal. This is the coupling that a scalar clock recurrence
alone does not account for.

For the seed response, when $L\ge4$,
$$
 \alpha=\frac{(L-2)(L+5)}{L+1},\qquad
 \beta=-\alpha\left(1+\frac{12}{L(L+1)}\right).
$$
The economical suffix is impossible for every $p\ge9$.
It suffices to prove this over a residue field since the
tableau, order, and the unit top moment specialize. There
$\alpha$ is a unit; if $\beta=0$, (6) at $a=0,1$
forces $\xi_L=\xi_{L-1}=1$, contradicting (3) and
$T_{L,L-1}=-1$. If $\beta\ne0$, the distance-two
entry in (5) has a single zero as a function of its clock.
If $\xi_L\ne1$, (6) with $a=0$ forces all of
$\xi_0,\ldots,\xi_{L-2}$ to equal that zero. If
$\xi_L=1$ but $\xi_{L-1}\ne1$, $a=1$ similarly
forces $\xi_0,\ldots,\xi_{L-3}$ equal. Three consecutive
equal clocks are impossible: their two adjacent coefficients
in (5) differ by one, yet (3) requires both zero. The only
shorter case is $L=4$ in the second branch. Here
$\alpha=18/5,\ \beta=-144/25$; the equal clocks
$\xi_0=\xi_1=3/8$ give $T_{1,0}=-7/4$, also a
contradiction. If the final two clocks both equal one, the
same contradiction $T_{L,L-1}=-1$ applies.

Thus the fixed-prefix width floors at orders $7,8,9$ are
respectively $10,11,13$, and for all $p\ge9$ this gives
$s\ge p+4$ in this architecture. These are not lower bounds
for methods that change the seven original strict rows.

## Productive replacement: sequential successor controls

For a general, not necessarily economical suffix, write
$$
                 A=\begin{pmatrix}A_0&0\\ B&D\end{pmatrix}.
$$
The seven prefix columns
$$
    \mathbf1,\ \mathbf c,\ \mathbf c^2,\ \mathbf c^3,\
          \mathbf c^4,\ \mathbf y,\ \mathbf x
$$
are an integral basis: the first five interpolate the five
clock labels with unit gaps, $\mathbf y$ separates the
$1/3$ fibre, and $x_7-x_5=90$ separates the endpoint
fibre with a unit pivot. Fix any strict $D$. Prescribe
values of $A$ applied to these seven probes freely on
each suffix row. At row $i$, subtract the already known
contributions of the predecessor suffix rows through $D$;
the unit prefix basis solves that row of $B$ uniquely.
The probes themselves at earlier rows are already determined,
so there is no implicit step. In particular the clock,
$y_i$, and $x_i$ may be specified independently using
the controls on $\mathbf1,\mathbf c,\mathbf y$.

Equivalently, expand the prefix restriction of each child
column in the seven probes and subtract the same expansion
from the full column. Its remaining, prefix-zero residual
propagates under $A$ only through $D$. The child lift on a
suffix row is the controlled probe expansion plus $D$
on that residual; then the ordinary root product gives the
stage value. This is an exact triangular reparameterization
of extensions, with no new denominators. For a split
one-residual band at economical width, conversely a proposed
lower triangular $T$ paying the chosen word moments with
unit clock gaps can be converted
to physical $C_s,D,\mathbf r_s,\mathbf b_s$: solve
$$
(\xi_i-\xi_j)K_{ij}=\sum_{\ell=j+1}^i K_{i\ell}T_{\ell j}
\quad(j<i)
$$
with $K_{ii}=1$, then use $D=KJK^{-1}$,
$\mathbf r_s=K\mathbf e_0$, and the readout $SK^{-1}$.
An invertible physical diagonal rescaling is also permitted.
At $p\ge9$ the economical case just proved impossible
means a viable sequential attempt must allow at least one
additional suffix site; in a longer cyclic basis the paid
one-clock rows no longer exhaust each column.

The companion [band constructions](BAND-CONSTRUCTIONS.md)
give two feasible partial constructions at orders seven and
eight. The full higher-order rooted equations include
other prefix-kernel relations and nonlinear root products.
They are not settled by (1) or by the calibration map.
