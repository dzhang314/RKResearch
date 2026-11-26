# Exact ninth-order ERK in eighteen paid stages

There is a 18-stage explicit Runge–Kutta method of exact order nine
over every nonzero commutative unital ring in which $9!$ is invertible.
This condition is necessary by the nine-vertex tall-tree equation.
The new witness improves the earlier universal upper bound of 21.
It leaves unchanged the sharp bound of 21 within uniform leapfrog
paths and the smaller real-algebraic upper bound.

The complete strict rows and weights are in tableau.json. Their
least common denominator is $85614133248000=2^{27}3^6 5^3 7$.
The standalone check.py reconstructs and verifies the literal table,
all 486 rooted equations through nine, and the next defect. If
$v_6=[\bullet]^{\#5}$ is the six-vertex bush, then the ten-vertex
tree
$$
 t_\star\coloneqq[\bullet]^{\#3}\#[v_6]
$$
has factorial 60, raw output $289/17280$, and cleared defect $1/288$.
This is a unit in $\mathbb Z[1/9!]$, so the next condition fails
after every unital map to a nonzero coefficient ring.

## Forward observations

For a tree $t$ put $g_t(x)\coloneqq |t|x^{|t|-1}/t!$, its exact
stage-derivative polynomial. A rooted sum multiplies these polynomials;
extension takes their integral from zero to $x$. Use the functionals
$$
  E_z f\coloneqq f(z),\qquad I_z f\coloneqq\int_0^z f(x)\,dx,\qquad
  I_1^x f\coloneqq\int_0^1 x f(x)\,dx .
$$
The integrals are rational polynomial operations. Let $\mathcal P_k$
denote the polynomials of degree at most $k$.

Take the known paid seven-stage order-six seed (its literal rows
are in check.py), with output $\mathbf b_6$ and clock vector
$\mathbf c_6$. Append its output as the eighth incoming row.
The origin and that new row realize $E_0,E_1$ on stage
profiles through tree order seven, since the new stage value is
the computed endpoint of an order-six step. The old rows
$\mathbf b_6$ and $\mathbf b_6\odot\mathbf c_6$ realize
$I_1,I_1^x$ through tree orders six and five respectively; the
clock multiplication attaches a leaf at the root.

The four functionals $E_0,E_1,I_1,I_1^x$ form a basis on
$\mathcal P_3$ with paid unit determinant. Their combination
representing $I_{1/2}$ is the ninth incoming row, so that
stage realizes $E_{1/2}$ through tree order five.
The five functionals $E_0,E_1,I_1,I_1^x,E_{1/2}$ have
determinant $1/57600$ on $\mathcal P_4$ in the listed monomial
coordinates. Let $\Pi$ send any nine-vector to the polynomial
in $\mathcal P_4$ with those five actual readouts. In particular
$I_1\Pi$ equals the padded old output row literally. If
$\mathbf u_t$ is the prefix tree-weight vector, put
$$
     \rho_t\coloneqq g_t-\Pi\mathbf u_t .
$$
It is zero through tree order five. It vanishes at 0 for all
trees and at 1 through tree order seven. It has integral zero
through tree order six.

## Reverse rows and unit pivots

The quadrature below pays the monomials through degree eight.

| Clock $x$ | Grouped weight |
|:--|--:|
| $-1/2$ and $3/2$ | $-1/23625$ each |
| $0$ and $1$ | $481/7560$ each |
| $1/4$ and $3/4$ | $17408/23625$ each |
| $1/3$ and $2/3$ | $-729/1000$ each |
| $1/2$ | $6/7$ |

Keep the clock-zero weight at the prefix origin. Split the
clock-one weight into 1 and its remainder. Split the
clock-$1/4$ weight into 1, 1 and its remainder. The eleven
suffix labels in reverse chronology have clocks
$$
   (1,1/4,1/4,-1/2,1/3,2/3,3/2,1/2,3/4,1/4,1).
$$
Write $\mathbf w$ for their individual weights and put
$y_i\coloneqq1-x_i$. The reverse strictly lower triangular
matrix $L$ will satisfy
$$
   L\mathbf1=\mathbf y,\qquad
   L\mathbf y=\mathbf y^{\odot2}/2+\mathbf u .
$$
Here $\mathbf u$ is supported on labels 2, 4, 5, 6, 7, 8;
$u_2=-y_2^2/2$. On these six distinct clocks, take the
products $w_i x_i y_i u_i$ proportional to the Lagrange
leading coefficients, with label 2 setting the common factor.
Thus $\mathbf u$ annihilates $x(1-x)\mathcal P_4$ under the
weighted sum. Every divisor is a unit over $\mathbb Z[1/9!]$.

Row 1 is zero. Row 2 reads just label 1. Rows 3 and 4 read
labels 1 and 2 to set their sums and their actions on
$\mathbf y$. For the later nonzero rows use the first four
labels as donors. The four inputs $\mathbf1,\mathbf y,
\mathbf y^{\odot2},\mathbf u$ have determinant $-243/1024$
on them. This leaves two independently assignable actions.
Define the two error vectors
$$
 \mathbf g_3\coloneqq L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,
 \qquad \mathbf v\coloneqq L\mathbf u .
$$
For each use only labels 5, 6 and 7 to cancel the first four
rows' three weighted moments against
$$
       f_k(x)\coloneqq x(1-x)
           \left(x^k-\frac{6}{(k+2)(k+3)}\right),\qquad
           1\le k\le3 .
$$
The $3$ by $3$ determinant is $3/500000000$. On the other
later labels prescribe both errors zero. The last row, at
the second clock-one label, is zero and is not a donor.

## Assembly and why it pays the rooted equations

In forward chronology let $T$ be the weighted transpose of
$L$; before relabeling, $w_i T_{ij}=w_j L_{ji}$. Only the first
four reverse columns of $L$ can be nonzero, and their weights
are units. Thus no other weight must be inverted. Let $E$
evaluate a polynomial at the suffix clocks, and put
$$
 (J f)(x)\coloneqq\int_0^x f,\qquad
 (J^* f)(x)\coloneqq\int_x^1 f,\qquad
 K\coloneqq(EJ-TE)\Pi .
$$
Take the tableau with prefix, bottom-left block $K$, and suffix
block $T$. The output uses the suffix weights and the clock-zero
weight at the origin. The unused reverse clock-one label becomes
a zero row and column in $T$. Its $K$ row is $I_1\Pi$, exactly
the old output row used as the eighth incoming row. These
two evaluations are therefore identical.

There is also a literal merge at clock $1/2$. The corresponding
reverse label is not a donor, so its $T$ row is zero and its
prefix read is $I_{1/2}\Pi$. Compare $\Pi$ on an arbitrary
prefix input with the degree-three reconstruction from
$E_0,E_1,I_1,I_1^x$. Their difference has the form
$x(1-x)Q(x)$ with $\deg Q\le2$, and its zeroth and first
integral moments vanish. Its odd part about $1/2$ must
vanish: that part is proportional to
$x(1-x)(x-1/2)$, whose first centered moment is $1/120$,
a unit. Thus the difference is symmetric with integral zero,
so its integral on $[0,1/2]$ is zero as well.
This proves that the corresponding suffix row equals the
literal ninth prefix row. In the 19-row intermediate
numbering, redirect row 12 to row 9 and transfer its
weight $6/7$. These two merges give $9+11-2=18$ physical
rows. The checker compares every padded row after redirection;
all remaining rows are pairwise distinct.

Write $e_t$ for the difference between the actual suffix
tree-weight vector and $E g_t$. Extension obeys the identity
$$
    e_{[t]}=T e_t+(TE-EJ)\rho_t .
$$
Here use degree $|t|-1$. Since $\rho_t$ is zero through degree
four, the first possible primitive error has degree six.
Through degree eight, there is room for only one erroneous
primitive in a product at the root. The other factors give
scalar monomials. Inductively every weighted error is thus
a sum of terms
$$
   \lambda_B(\rho_t)\coloneqq
         \mathbf w\cdot \bigl(B(TE-EJ)\rho_t\bigr),
$$
where $B$ consists of copies of $T$ and clock multiplication
and has length $\ell$ with $\ell+\deg(t)+1\le8$.

Transfer the word to reverse chronology. Let $\mathbf h$
be the resulting word in $L$ and clock multiplication acting
on $\mathbf1$, and let $P$ be its scalar counterpart acting
on 1 with $J^*$ in place of $L$. Write
$\langle\mathbf r,\mathbf z\rangle_w
\coloneqq\sum_i w_i r_i z_i$. Polynomial integration in either
order and exact quadrature give
$$
  \lambda_B(f)
   =\langle L\mathbf h-EJ^*P, E f\rangle_w
      -\langle\mathbf h-EP,EJ f\rangle_w .
$$
For quadrature the largest degree is $\ell+\deg(f)+1\le8$.
The omitted clock-zero sample contributes nothing because
$f(0)=(Jf)(0)=0$.

For $\ell=0$ the expression vanishes by the row sums. For
$\ell=1$ the input word is exact and the new error is a
multiple of $\mathbf u$. The relevant discrepancies have
degree at most six and vanish at both endpoints, so the
five weighted moments kill the expression. For $\ell=2$
the discrepancy has degree five and vanishes at both
endpoints with integral zero, hence lies in the span of
the three $f_k$. The actual two-letter values are
$\mathbf x^{\odot2},\mathbf x\odot\mathbf y,L\mathbf x,
L\mathbf y$, so their errors are 0 or $\pm\mathbf u$.
Their next errors are linear combinations of
$\mathbf u,\mathbf g_3,\mathbf v$, since the scalar input
has degree at most two. These annihilate the three test
polynomials. Also $Jf$ has degree at most six and vanishes
at both ends, killing the remaining term. This proves the
full order-nine claim, independently of the tree census.
