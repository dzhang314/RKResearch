# Even-order uniform midpoint prefixes: sharp width and unique equality

This is a generalization of the [order-twelve paid midpoint-prefix
width bound](MIDPOINT-PREFIX-MINIMUM.md), not a lower bound on
unrestricted DIRK. The upper construction is the standard implicit
midpoint extrapolation. Below is an elementary rooted-flag proof of its
order, together with a uniqueness theorem for the whole equal-square
branch architecture at the minimum width.

Let \(p=2r\), \(r\ge1\). Over every nonzero commutative ring inverting
\((2r)!\), the usual disjoint \(1,\ldots,r\)-substep midpoint branches
have exact rooted order \(2r\) in \(r(r+1)/2\) stages. Within the
architecture of disjoint branches having constant squared step on
each branch, this is the smallest possible width, even allowing
arbitrary output weights and arbitrary signed steps with that square.
At minimum width, the literal tableau and weights are unique up to
interleaving the branches without changing their internal order.

## Actual rooted upper proof by homogeneous midpoint primitives

In branch \(m=1,\ldots,r\), choose \(h=1/m\); row \(j\),
\(0\le j<m\), has clock \(c=(j+1/2)h\), earlier same-branch entries
\(h\), diagonal \(h/2\), and no cross-branch entries. Output weights
are \(\lambda_m/m\) at each row of branch \(m\), where
\[
  \lambda_m=\prod_{1\le l\le r,\ l\ne m}\frac{m^2}{m^2-l^2}.
\]
Thus the \(\lambda_m\) are evaluation-at-zero Lagrange weights on
\(h^2=1/m^2\). Factoring the two products \(m-l\) and \(m+l\)
gives a sharper denominator statement:
\[
 \frac{\lambda_m}{m}
  = \frac{(-1)^{r-m}2m^{2r-1}}{(r-m)!(r+m)!}
  = \frac{(-1)^{r-m} 2m^{2r-1}\binom{2r}{r-m}}{(2r)!}.
\]
Each matrix denominator divides \((2r)!\) as well. In particular
one copy of the factorial clears every literal tableau entry.

Over \(\mathbb Q\), for each integer \(d\ge0\) take the unique
polynomial
\[
 U_d(X,h)=\sum_{k=0}^{\lfloor d/2\rfloor}
          u_{d,k}h^{2k}X^{d+1-2k}
\]
with \([U_d(X+h/2,h)-U_d(X-h/2,h)]/h=X^d\).
It exists by triangular elimination, since the centered finite
difference of \(X^q\) begins with \(qX^{q-1}\), and thereafter
decreases the \(X\) exponent by even increments with an equal
increase in the \(h\) exponent. In particular \(u_{d,0}=1/(d+1)\)
and \(U_d(0,h)=0\).

On an actual stage of clock \(c\), the literal matrix read on
\(\mathbf c^d\) is the completed previous quadrature
\(U_d(c-h/2,h)\), plus half the increment \(h c^d\). So its value
is \([U_d(c+h/2,h)+U_d(c-h/2,h)]/2\). The centered average is even
in \(h\); its leading term is \(c^{d+1}/(d+1)\). Therefore
\[
 (d+1) A\mathbf c^d=\mathbf c^{d+1}
      +\sum_{k=1}^{\lfloor(d+1)/2\rfloor}
           a_{d,k}\mathbf u^k\mathbf c^{d+1-2k},
\]
where \(\mathbf u=h^2\) on each branch. All powers and products of
stage vectors are componentwise. As matrix rows only read their
own branch, \(A\) commutes literally with multiplication by
\(\mathbf u^k\).

Define the auxiliary band at grade \(g\) as the span of
\(\mathbf u^k\mathbf c^d\) with \(k\ge1\) and \(2k+d\le g\).
The displayed formula supplies primitive discrepancies; the
matrix action and clock multiplication each increase the band
grade by at most one, and the product adds grades. The weighted
read of any monomial \(u^k c^d\) is
\(\sum_m\lambda_m h^{2k}U_d(1,h)\), by the telescoping difference.
As a polynomial in \(u=h^2\), \(u^k U_d(1,h)\) has degree at most
\(k+\lfloor d/2\rfloor<r\) whenever \(2k+d<2r\).
Thus the weighted read is its value at zero: zero for \(k\ge1\),
and \(1/(d+1)\) for \(k=0\). This establishes every paid band
annihilator and scalar moment.

For clarity, the sufficient flag implication is an induction on
root attachments, not a test of only the tall or the bushy trees.
For tree \(t\), take its normalized elementary stage vector
\(\mathbf X_t = [t!/|t|]\boldsymbol{\Phi}_t(A)\). It is
\(\mathbf 1\) for a leaf, and attaching \(u\) at the root of
\(t\) gives \(\mathbf X_t\cdot(|u|A\mathbf X_u)\).
The band rules just checked imply
\(\mathbf X_t-\mathbf c^{|t|-1}\) lies in the band at
grade \(|t|-1\), through \(2r\). Applying the paid read and
multiplying by \(|t|\) gives the cleared rooted order equations.
This is precisely the sufficient hypothesis of the repo's
SufficientFlags.hasOrder bridge.

Though the homogeneous primitive coefficients above were used
over \(\mathbb Q\), only the literal tableau entries are present
in the cleared order identities. So those identities already
hold over \(\mathbb Z[1/(2r)!]\) and pass to every unital algebra
over it, with no field or ordering hypothesis.

Finally the normalized first unpaid tall defect is exactly
\[
  (2r+1)!\,\mathbf b^T A^{2r}\mathbf1-1
       =(-1)^{r+1}{\binom{2r}{r}\over 2^{2r}}.
\]
Indeed each branch has stability
\(((1+z/(2m))/(1-z/(2m)))^m\). Its log has coefficient
\(u^k/[(2k+1)2^{2k}]\) at degree \(2k+1\), and \(z\)
at degree one. Through degree \(2r+1\), the only positive
\(u\)-degree not removed by the extrapolation is \(r\), consisting
of the single log term of that degree. Its moment is
\(\sum\lambda_m (1/m^2)^r=(-1)^{r+1}/(r!)^2\), by the
monic interpolation nodal polynomial. Multiplying by
\((2r+1)!\) gives the stated defect. It is a unit because all
prime factors of \(\binom{2r}{r}\) are at most \(2r\).
The supplied compact exact checker independently evaluates the
actual tall reads rather than assuming this formula.

## Sharp lower and rigidity without prescribing output

Allow arbitrary individual weights and branch terminal times.
Assume only ordinary midpoint causal taps as above, where step
\(h_{m,j}\) can vary within branch \(m\) subject to
\(h_{m,j}^2=u_m\). The [telescope](MIDPOINT-PREFIX-MINIMUM.md)
still makes \(2A\mathbf c-\mathbf c^2=\mathbf u/4\).
In particular an actual order-\(2r\) tableau, not merely the
constructed tableau, satisfies
\[
 \mathbf b^T P(\mathbf c,\mathbf u) = \mathcal I(P(X,0)),
 \qquad \mathcal I(X^a)=1/(a+1),
 \qquad \operatorname{wdeg}P\le 2r-1,
\]
by the actual forward products, clock lifts and scalar moments.
The tall tree of order \(2r\) makes \((2r)!\) a unit.

In any field specialization, for \(0\le n<r\), let \(E_n\)
be the nonzero squared steps of branches of length \(>n\).
If \(n+|E_n|<r\), the paid polynomial
\[
 X\prod_{j=0}^{n-1}\bigl(X^2-(j+1/2)^2Y\bigr)
   \prod_{v\in E_n}(Y-v)
\]
vanishes stagewise, but has nonzero weighted read
\(\prod_{v\in E_n}(-v)/(2n+2)\). This is the same support proof as
for twelve: zero-square branches have clock zero, and the first
\(n\) rows of a nonzero constant-square branch have signed
half-integer clocks of squared indices at most \(n-1\). So
\(|E_n|\ge r-n\) and summing physical branch counts gives the
triangular lower bound, also after reduction from any nonzero
commutative ring. At equality there is exactly one nonempty
branch of each length \(1,\ldots,r\); \(E_0\) consists of their
\(r\) distinct nonzero squared steps in every field reduction.

Now fix \(0\le n<r\) in a field. Omit the initial \(X\) and the
factor of the unique branch of length \(n+1\), giving
\[
 M_n(X,Y)=\prod_{j=0}^{n-1}\bigl(X^2-(j+1/2)^2Y\bigr)
           \prod_{\substack{m>n\\m\ne n+1}}(Y-u_m).
\]
The first product kills every row of depth \(<n\); the second
kills other branches of length \(>n\). Hence the sole
possibly nonzero row is the terminal row of branch \(n+1\).
Its \(M_n\) output is
\(\prod_{m>n,m\ne n+1}(-u_m)/(2n+1)\ne0\).
Its paid \(XM_n\) output replaces \(2n+1\) by \(2n+2\).
The ratio forces the literal clock at that row to equal
\((2n+1)/(2n+2)\). Nonzero \(M_n\) also forces its
half-integer squared index to be \(n\), not a smaller one.
A signed sum of \(n\) units and one half-unit has this
extremal index only when all signs agree. Hence all signed
steps on that branch are \(1/(n+1)\). No orientation of the
field is used: the extremal assertion is on the integer sign
sum before mapping, and factors for smaller integer indices
already vanish literally in the field.

Over a general nonzero commutative ring, the previous conclusion
holds in every maximal-ideal residue field. On a branch the sum of
any two signed steps now reduces to the same unit \(2/m\) everywhere,
so this sum is a unit of the ring. Since the squared steps are
literally equal, their difference is literally zero. The
squared steps themselves and all inter-branch differences are
units by the same residue criterion. Thus the support calculation
for \(M_n\) works with the now constant signed actual steps in
the ring itself, and its paid output is a unit. The same ratio
forces the literal common signed step to equal \(1/(n+1)\),
not just modulo the Jacobson radical.

It remains to see the weights are unique. For branch of length
\(\ell\) and a row of depth \(j<\ell\), use the mask
\[
 \prod_{k=0}^{j-1}\bigl(X^2-(k+1/2)^2Y\bigr)
        \prod_{\substack{m>j\\m\ne\ell}}(Y-u_m)
\]
of weighted degree \(2r-2\). It is supported on that branch at
depths \(\ge j\). Its value at depth \(j\) is a unit: the first
product contributes \(u_\ell^j\prod_{k<j}(j-k)(j+k+1)\),
with all integer factors \(\le2r\), and the other factors are
unit differences of squares. Descending by depth in each branch,
the fixed paid reads therefore determine every weight uniquely.
Since the literal extrapolation weights above already work,
they are the unique weights.

This width/rigidity theorem does not cover genuinely unequal
absolute steps within a branch, cross-branch taps, or general
lower triangular tableaux. No unrestricted DIRK minimum at any
order is being asserted by it.

## Arithmetic replay

Run \(\texttt{python3 -B verify-even-family.py}\). It covers every
even order 2–20, checks all compact sufficient-flag numbers using
exact rational arithmetic and literal row reads, and checks the
unit next tall defect. It also compares the order-twelve tableau
to the already independently all-tree-verified literal file.
The proof above, not a search for a finite list of residuals,
is what makes the formulas valid for higher even orders.
