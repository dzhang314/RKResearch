# Exact universal-ring order ten in 21 explicit stages

**Current upper bound:** the [18-stage general-ring method](../erk10-eighteen-ten-clock/README.md) is strongest. The intermediate [19-stage](../erk10-nineteen-compressed-reverse/README.md) and [20-stage](../erk10-twenty-compressed-reverse/README.md) constructions are retained as separate results.

The literal tableau in tableau.json has exact order ten in 21
explicit stages over every nonzero commutative unital ring in
which $10!$ is invertible. The factorial condition is necessary
by the tall tree. The previous paid moment splice used 23 rows;
the earlier uniform midpoint construction used 26. The
15-row real-algebraic upper is not changed.

The common coefficient denominator is
$987614208000=2^{13}3^9 5^3 7^2$.
Put $v_6\coloneqq[\bullet]^{\#5}$. For the eleven-vertex tree
$[\bullet]^{\#3}\#[[v_6]]$, the factorial is 462, the raw
output is $1031/476280$, and the cleared defect is $1/11340$.
This is a unit without having to invert 11. Check.py constructs
the literal strict tableau, verifies the denominator restriction
and all 1,205 paid rooted equations, and checks this unit defect.

The same 13-row prefix as in the 23-row order-ten splice starts
with the paid ten-stage order-seven seed. Append its endpoint;
its derivative gives $E_1$, evaluation at 1. The seed moments
$I_1,I_1^x,I_1^{x^2}$ are realized by the seed weights multiplied
by clock powers, which attach root leaves. Together with the
origin and endpoint these forms interpolate on polynomials of
degree at most four, and give the two new primitive rows at
$1/2,1/3$. The resulting six readouts
$E_0,E_1,I_1,I_1^x,E_{1/2},E_{1/3}$ define the degree-five
projection $\Pi$, with determinant $-1/19595520$. The prefix
discrepancy $\rho_t$ is zero through tree order six, vanishes at
0 and 1 through tree order eight, and has integral zero through
tree order seven.

Use the nine symmetric quadrature sites
$-1/2,0,1/4,1/3,1/2,2/3,3/4,1,3/2$ with weights
$-1/23625,481/7560,17408/23625,-729/1000,6/7,-729/1000,
17408/23625,481/7560,-1/23625$.
Precision eight and symmetry imply precision nine. Assign the
clock-zero weight to the old origin. Split each of the clock-one
and two quarter masses into weight 1 and its remainder. The
reverse clock order is
$$
   (1,-1/2,1/3,2/3,1/4,1/2,3/4,3/2,1/4,3/4,1).
$$
The remainder at each repeated clock is the later label. Using the
first four labels as donors, construct $L$ by the same short
reverse architecture as for order nine. With $y_i=1-x_i$,
put $L\mathbf1=\mathbf y$ and
$L\mathbf y=\mathbf y^{\odot2}/2+\mathbf u$.
Make the seven products $w_ix_i y_i u_i$ on labels 2 through 8
proportional to the Lagrange leading coefficients, normalized by
$u_2=-y_2^2/2$. This kills the six moments
$x(1-x)x^k$, $0\le k\le5$. Row 1 is zero; row 2 reads
only row 1; rows 3 and 4 read the first two donors.
The four inputs $\mathbf1,\mathbf y,\mathbf y^{\odot2},\mathbf u$
on labels 1 through 4 have determinant $5/168$. On labels
5 through 8 choose the remaining two actions so the vectors
$$
  L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\qquad L\mathbf u
$$
annihilate the four weighted residual polynomials
$x(1-x)(x^k-6/((k+2)(k+3)))$, $1\le k\le4$.
The weighted determinant is $9/575458508800$.
Other later rows set the two actions to zero; the final clock-one
label is a zero row and has no donor use.

The full tableau uses the weighted transpose $T$ in forward
chronology and lower-left block $(EJ-TE)\Pi$, with $E$ the suffix
evaluation and $J$ the primitive from zero. No nonunit individual
mass is ever divided out. The proof of the rooted equations uses
the extension formula $e_{[t]}=Te_t+(TE-EJ)\rho_t$ as in the
order-nine construction. A first primitive error costs seven
nonroot vertices. Through degree nine, only one can occur in a
rooted product, so errors are sums of source terms from words of
length at most two. Moving a word through the weighted transpose,
then integrating polynomials in either order, replaces its effect
on $f=\rho_t$ by
$$
  \langle L\mathbf h-EJ^*P,Ef\rangle_w
       -\langle\mathbf h-EP,EJf\rangle_w,
$$
where $\mathbf h$ and $P$ are the actual reverse and exact scalar
word values on 1. The first test is exact by the row sums at
length zero. At length one the new error is a multiple of
$\mathbf u$ and $f$ has both endpoint zeros and degree at most
seven. At length two $f$ has degree six, both endpoint zeros
and integral zero, so lies in the stated four-dimensional
residual space. The word error is $0$ or $\pm\mathbf u$, and its
next error is a linear combination of $\mathbf u$ and the two
prescribed vectors. Since the primitive of $f$ has degree at most
seven and both endpoint zeros, its paired term also vanishes.
This accounts for all trees through order ten.

The unused clock-one row is literally the prefix endpoint. Each
quarter pair consists of two non-donors, hence has identical
rows after the weighted transpose, both given by the same
$I_x\Pi$ in the prefix and zero on the other suffix labels.
Redirect their outgoing coefficients and combine the weights.
Consequently the 13-row prefix and eleven-label suffix yield
$13+11-3=21$ actual evaluations. Exhaustive comparison of
all padded rows after those merges finds no further identical row.
