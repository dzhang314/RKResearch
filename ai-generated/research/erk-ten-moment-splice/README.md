# Exact tenth-order ERK in 23 paid stages

The literal explicit tableau in tableau.json has exact order ten
over every nonzero commutative unital ring in which $10!$ is a unit.
That factorial condition is necessary by the ten-vertex tall tree.
The previous universal explicit midpoint construction gives 26
stages; the 15-stage real-algebraic upper is a different statement
and is not changed here. No minimum or literature-priority claim is
made.

The common denominator of the reduced literal coefficients is
$$
  74912366592000=2^{24}3^6 5^3 7^2 .
$$
The 1,205 paid rooted equations are verified by check.py, with no
assumed nonlinear searches or numerical tolerances. Put
$v_6=[\bullet]^{\#5}$ and
$$
   t_\star\coloneqq [\bullet]^{\#3}\#[[v_6]] .
$$
This eleven-vertex tree has factorial 462, raw output
$407/188160$, and cleared defect $-3/4480$, a unit in the
coefficient ring. In particular exactness does not rely on division
by $11$ or on characteristic zero after base change.

## Forward and reverse data

The polynomial stage model and the weighted transpose assembly
are the same as in the companion exact order-nine witness.
Let $g_t(x)\coloneqq |t|x^{|t|-1}/t!$, write $E_z$ for
evaluation at $z$, $I_z$ for integration from 0 to $z$, and
$I_1^{x^j}$ for the moment with factor $x^j$ on $[0,1]$.
Start with the ten-stage paid order-seven seed (full literal
rows in check.py). Append its output as an endpoint stage.
The origin and the endpoint realize $E_0,E_1$ through tree
order eight, with no cap at the origin. The seed output
multiplied entrywise by the $j$th power of the seed clock
realizes $I_1^{x^j}$ through tree order $7-j$, by adding
$j$ root leaves. On the polynomials of degree at most four,
the five degree-restricted moment and endpoint actions
$E_0,E_1,I_1,I_1^x,I_1^{x^2}$ give a paid interpolation basis.
Use it to realize $I_{1/2},I_{1/3}$ as two new rows; their
stage slopes implement $E_{1/2},E_{1/3}$ through tree order six.
This gives a 13-row prefix.

Define $\Pi$ by the six actual readouts
$E_0,E_1,I_1,I_1^x,E_{1/2},E_{1/3}$ on polynomials of degree
at most five. Its determinant, in this order and the monomial
basis, is $-1/19595520$. The prefix discrepancy
$\rho_t\coloneqq g_t-\Pi\mathbf u_t$, with $\mathbf u_t$ the
prefix tree-weight vector, is zero through tree order six,
has both endpoint zeros through tree order eight, and has
integral zero through tree order seven. The equality
$I_1\Pi=\mathbf b_7$ with zero padding is literal.

Use the order-nine witness's quadrature:
a symmetric pair at $-1/2,3/2$ with weights $-1/23625$;
at $0,1$ with weights $481/7560$;
at $1/4,3/4$ with weights $17408/23625$;
at $1/3,2/3$ with weights $-729/1000$;
and the center $1/2$ with weight $6/7$. It integrates degree
eight and hence degree nine, since its centered ninth moment
vanishes by symmetry. Use the weight at 0 on the old origin.
Split the weight at 1 into 1 and its remainder; split that
at $1/4$ into 1, 1 and its remainder; split that at $3/4$
into 1 and its remainder. The twelve reverse labels have clocks
$$
    (1,1/4,1/4,-1/2,1/3,2/3,3/2,1/2,3/4,3/4,1/4,1).
$$
The first copies of 1 and $3/4$ carry 1; the first two copies
of $1/4$ carry 1. Write $\mathbf w$ for their individual
weights and $y_i\coloneqq1-x_i$. The reverse rows prescribe
$$
 L\mathbf1=\mathbf y,\qquad
 L\mathbf y=\mathbf y^{\odot2}/2+\mathbf u .
$$
Support $\mathbf u$ on labels $2,4,5,6,7,8,9$. The products
$w_ix_i y_i u_i$ are proportional to the seven-node Lagrange
leading coefficients and $u_2=-y_2^2/2$. Thus $\mathbf u$
annihilates $x(1-x)$ times all polynomials of degree at most
five under the weighted sum. All denominators are paid.

The first reverse row is zero; row 2 reads row 1 only; rows
3 and 4 read labels 1 and 2. All later nonzero rows use
labels 1 through 4. On these donors the matrix of the actions
on $\mathbf1,\mathbf y,\mathbf y^{\odot2},\mathbf u$ has
determinant $-243/1024$. The two remaining actions are chosen
so
$$
 \mathbf g_3\coloneqq L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,
       \qquad \mathbf v\coloneqq L\mathbf u
$$
annihilate the same four weighted moments, taken against
$$
 f_k(x)\coloneqq x(1-x)\left(x^k-\frac{6}{(k+2)(k+3)}\right),
   \qquad 1\le k\le4 .
$$
Use labels 5 through 8 to cancel the first four rows'
contributions, setting both errors zero on the other later
labels. Their moment determinant is $1/156800000000$.
The last reverse clock-one label has zero incoming row
and is not a donor. The checker gives the exact Cramer formulas.

## Assembly, row equality and order

In forward chronology use the normalized transpose $T$ of
$L$, defined by $w_iT_{ij}=w_jL_{ji}$ before reversing labels.
All nonzero reverse donor columns have unit weights, so the
formula requires no division by the other weights. With $E$
evaluation at the suffix clocks and $J f\coloneqq\int_0^x f$,
take the forward prefix, the lower-left block
$K\coloneqq(EJ-TE)\Pi$, and the suffix matrix $T$.
Add the endpoint weight from the unused reverse clock-one
label to the existing prefix endpoint and remove its duplicate
row: it had no suffix incoming entries and $I_1\Pi$ is the
literal prefix endpoint. Also the two $3/4$ suffix labels,
both not donors in reverse, have zero suffix rows. Both have
prefix row $I_{3/4}\Pi$. In the 24-row intermediate numbering,
merge row 16 into row 15, redirecting all outgoing coefficients
and transferring its weight 1. Thus $13+12-2=23$ rows remain.
The checker exhausts equality on complete padded rows after
the redirections; none remain identical.

For clarity the order certification has the same short proof as
the order-nine companion. If $e_t$ is the suffix tree-weight
error, then
$$
     e_{[t]}=T e_t+(TE-EJ)\rho_t.
$$
Here degree means $|t|-1$. A first primitive error has degree
seven, so through degree nine every product contains at most
one erroneous primitive factor. Propagation amounts to weighted
words of length $\ell\le2$ in $T$ and multiplication by the
clock. Applied to a source $f=\rho_t$ of degree $d$, the total
degree is $d+\ell+1\le9$. Reverse the word via the weighted
transpose; let $\mathbf h$ be its reverse action on
$\mathbf1$, and let $P$ be its scalar counterpart with
$J^*f\coloneqq\int_x^1 f$ in place of $L$. Exact quadrature
and reversing polynomial integration give the error
$$
   \langle L\mathbf h-EJ^*P,Ef\rangle_w
        -\langle \mathbf h-EP,EJf\rangle_w .
$$
The omitted origin contributes zero because $f(0)=(Jf)(0)=0$.
It vanishes for length zero by the row sums. At length one
the input word is exact and the first defect is a multiple
of $\mathbf u$; $f$ has degree at most seven and both endpoint
zeros, which is the paid six-moment condition. At length two
the source has degree six, both endpoint zeros and integral
zero, so lies in the span of the four $f_k$. Each length-two
reverse error is $0$ or $\pm\mathbf u$; its next error belongs
to the span of $\mathbf u,\mathbf g_3,L\mathbf u$.
The last term also vanishes, because $Jf$ has degree at most
seven and both endpoint zeros. This establishes all nonlinear
rooted conditions in the paid range. The literal replay
checks them again and proves the unit next defect.
