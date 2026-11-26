# Exact paid-ring explicit methods of orders eleven and twelve

These are absolute ERK upper witnesses over every nonzero
commutative ring with the indicated factorial invertible.
They do not improve the smaller upper bounds over real algebraic
numbers and do not assert stage minima.

The current [27- and 30-stage tableaux](../erk-signed-reverse/README.md) use a different reverse construction. The [32-stage construction](ORDER-12-IN-32-STAGES.md) in this archive reuses the difference between two existing quarter-clock rows. Run `python check-32.py` to check the archived [tableau](tableau-12-32.json), all 7,813 rooted conditions, and the two order-thirteen defects whose unit ideal proves exact order after any nonzero coefficient change. The 33-stage method below is the preceding construction.

| Order | Physical stages | Prior uniform-path upper | Paid rooted equations | Common denominator | Unit next cleared defect |
|---:|---:|---:|---:|:---|:---|
| 11 | 28 | 31 | 3047 | $13910206464000=2^{14}3^6 5^3 7\cdot 11^3$ | $-10/567$ |
| 12 | 33 | 37 | 7813 | $93893893632000000=2^{15}3^9 5^6 7\cdot 11^3$ | $1/3326400$ |

The literal matrices and weights are in tableau-11.json and
tableau-12.json. Run check.py with argument 11 or 12 to reconstruct
and verify them. For the order-12 construction the exact 16-row
order-nine seed is included as paid9-seed.json. Everything is exact
rational arithmetic. Factorial invertibility, already necessary
by the displayed order's tall tree, suffices for every coefficient
in the checkers.

Write $v_j\coloneqq[\bullet]^{\#(j-1)}$ for a bush with $j$
vertices. The order-11 witness's next failed tree is
$[\bullet]\#[[[[v_7]]]]$, with 12 vertices, factorial 60480,
and raw output $557/34292160$. The order-12 witness fails
$[\bullet]^{\#2}\#[[v_9]]$, with 13 vertices, factorial 1170,
and raw output $255877/299376000$. Both cleared defects in the
table are units; the second does not require inverting 13.

## Forward observations from an ordinary seed

Write $p$ for the target and put $m\coloneqq p-4$. Start from
a paid ordinary explicit method of order $m+1$. Its derivative
polynomial for a tree $t$ is
$g_t(x)\coloneqq |t|x^{|t|-1}/t!$.
Write $E_a$ for evaluation at a clock $a$, $I_a$ for the
integral from 0 to $a$, and $I_1^{x^k}$ for integration on
$[0,1]$ with factor $x^k$. On actual derivatives through tree
order $m+1-k$, the seed output multiplied by its clock to
the $k$th power realizes $I_1^{x^k}$: multiplication attaches
$k$ leaves at the root. The first stage realizes $E_0$.
The appended literal seed endpoint realizes $E_1$ on
derivatives through tree order $m+2$.

If the available actual functionals span on polynomials of
degree at most $g-1$ and are exact through tree order $g$,
any combination realizing $I_a$ on those polynomials forms a
new strict incoming row. Its derivative realizes $E_a$
through tree order $g+1$. Every new stage here comes from
this single operation.

* At $p=11$, take the 13-row paid order-eight seed. With the
  endpoint appended, $E_0,E_1,I_1,I_1^x,I_1^{x^2}$ realize
  $I_{1/3}$ through order five. Add this row, use its new
  evaluation with the same five functionals at order six,
  and add the three local rows at $1/12,1/3,2/3$.
  The new local evaluation order is seven. The prefix has
  $13+1+1+3=18$ rows. The three tested basis determinants are
  $-1/1512000,-1/514382400,11/4936942338048$.
* At $p=12$, take the 16-row paid order-nine seed and append
  its endpoint. At order six use $E_0,E_1$ and the first four
  integral moments to add rows at $1/3,2/3$. At order seven
  use their new evaluations, $E_0,E_1$ and the first three
  integral moments to add four rows at $1/12,1/4,1/3,1/2$.
  The prefix has $16+1+2+4=23$ rows. The tested determinants
  are $1/53343360000,1/1312446693600,275/95865912019648512$.

At order $m$, the last group of evaluation functionals together
with $E_0,E_1,I_1,I_1^x$ determines a unique polynomial
$\Pi$ of degree at most $m-1$ from the actual forward readouts.
The last determinant in each bullet is for this map. Every
listed determinant is a paid unit. For the prefix tree vectors
$\mathbf a_t$, let $\rho_t\coloneqq g_t-\Pi\mathbf a_t$.
It is zero through tree order $m$, has both endpoint zeros
through tree order $m+2$, and has zero integral through
tree order $m+1$. The equality of the row $I_1\Pi$ with the
literal seed output (zero-padded) holds on all input vectors.

## One quadrature and a short reverse block

The common quadrature is symmetric about $1/2$. Its table is:

| Clocks | Weight per clock |
|:--|--:|
| $0,1$ | $35663/1524600$ |
| $1/12,11/12$ | $576/4235$ |
| $1/6,5/6$ | $-9/1925$ |
| $1/4,3/4$ | $448/2475$ |
| $1/3,2/3$ | $783/15400$ |
| $1/2$ | $262/1155$ |

The monomial equations through degree ten are checked
exactly; symmetry pays degree eleven. Use the clock-zero
weight on the origin. Split the masses at $1,1/3,1/2,2/3$
into 1 and their respective remainders. In reverse chronology
the fourteen labels are
$$
 (1,1/12,1/6,5/6,1/4,1/3,1/2,2/3,3/4,11/12,1/3,1/2,2/3,1).
$$
At each repeated clock the later label takes the remainder.
Only the first four reverse labels are used as donors;
their weights are units. The value of the split is that the
labeled unit masses can be used in the moment systems, while
the paired non-donors still merge in forward chronology.

Put $y_i\coloneqq1-x_i$ and write $\mathbf w$ for the
individual weights. The strictly lower triangular reverse
matrix $L$ satisfies $L\mathbf1=\mathbf y$ and
$L\mathbf y=\mathbf y^{\odot2}/2+\mathbf u$.
On the nine distinct nonendpoint labels make $w_ix_i y_i u_i$
proportional to the Lagrange leading coefficients (and zero
elsewhere). Normalize by $u_2=-y_2^2/2$. All the differences
and divisors here are paid, and $\mathbf u$ annihilates the
weighted tests $x(1-x)x^k$ for $0\le k\le7$.

The first row is zero; the second uses only the first donor;
the third and fourth use the first two donors. For the
later rows the inputs $(\mathbf1,\mathbf y,\mathbf y^{\odot2},
\mathbf u)$ on the first four donors have determinant
$-605/288$, a unit. Set the two remaining actions so that
$L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3$ and $L\mathbf u$
annihilate the following weighted tests:
* At $p=11$, all $x(1-x)x^k$ for $0\le k\le5$.
* At $p=12$, the six polynomials
  $x(1-x)(x^k-6/((k+2)(k+3)))$, $1\le k\le 6$.

Use labels 5 through 10 for the six controls in each of these
two vectors after subtracting the initial contributions.
The two test determinants are $49/140808648255897600$
and $49/405528906976985088000$ respectively. The later
actions are zero elsewhere; the unused clock-one remainder
has a zero reverse row and column.

## Order and literal row counts

Let $T$ be the weighted transpose of $L$ in forward chronology,
$E$ evaluation on suffix clocks, and $J$ the primitive from
zero. Put the lower-left block equal to $(EJ-TE)\Pi$.
The output uses the suffix weights and the origin weight.
Only live reverse donor columns are inverted in the formula
$w_i T_{ij}=w_j L_{ji}$ before reversing; all are units.

An extension's suffix error satisfies
$e_{[t]}=T e_t+(TE-EJ)\rho_t$. Its first possible nonzero
degree (tree order minus 1) is $m+1$. Through degree $m+3$,
a product over root children has at most one such error.
Propagation gives a source $f=\rho_t$ followed by at most
two letters, each either $T$ or multiplication by the clock.
For a word of length $\ell$ the source degree is at most
$m+2-\ell$. Transpose the word; write $\mathbf h$ for its
actual reverse action on 1, and $P$ for the exact scalar
action with $J^*f(x)\coloneqq\int_x^1 f$ in place of $L$.
The weighted error is
$$
 \langle L\mathbf h-EJ^*P,Ef\rangle_w
     -\langle\mathbf h-EP,EJf\rangle_w .
$$
This follows by exact quadrature and reversing polynomial
integration; the omitted zero-clock term vanishes. Length
zero is exact by row sums. At length one the new error is
a multiple of $\mathbf u$, and $\deg f\le m+1$ with both
endpoint zeros. At length two, $\deg f\le m$ and $f$ has
endpoint zeros and integral zero. The word error is 0 or
$\pm\mathbf u$; its next error is in the span of $\mathbf u$
and the two paid vectors. The primitive $Jf$ has both
endpoint zeros and degree at most $m+1$, so its contribution
also vanishes. This proves the full order conditions.

The unused clock-one row is the literal forward endpoint,
because its normalized transpose row is zero and $I_1\Pi$
is the original endpoint read. The two labels at each of
$1/3,1/2,2/3$ are non-donors; they have zero suffix rows
and identical prefix read $I_x\Pi$, so merge. Outgoing
coefficients and weights are redirected before deletion.
The final counts are $18+14-4=28$ and $23+14-4=33$,
and no two reduced padded rows are equal. The independent
rooted replay in check.py repeats all the order tests on the
reduced literal arrays, not only on the symbolic splice.
