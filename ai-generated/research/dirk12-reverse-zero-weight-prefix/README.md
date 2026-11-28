# A residue obstruction from initial zero scores in a weighted reverse block

This is a local obstruction for **sufficient weighted reverse flags**
in a DIRK12 splice, not an unrestricted stage lower bound. In
particular it needs the pointwise next reverse moment and the paid
cubic profile described below. Changing only higher reverse rows or
higher-grade constraints cannot fix a failing prefix. Changing the
leading proper score order, allowing a larger cubic numerator space,
or releasing the pointwise reverse \(C(2)\) ansatz can avoid it.

Let \(\mathit K\) be the literal lower-triangular reverse transpose
of the suffix matrix. Include the terminal row at \(x_0=1\),
followed by \(m\) proper scored rows, with \(y_i=1-x_i\), scores
\(\mathbf w\), and \(\mathbf W_j=\mathbf w\odot\mathbf y^j\).
At an unpaid prime \(p>3\), suppose the coefficient data are
\(p\)-integral and the proper \(x_i\) have distinct residues,
all different from 0 and 1. Reduce all of these data modulo \(p\)
without dividing by any score. The imposed low flags are
\[
  \mathit K\mathbf W_1=\mathbf W_2/2,\qquad
  \mathbf G=\mathit K\mathbf W_2-\mathbf W_3/3,\qquad
  \sum_i x_i^j G_i=0 \quad(1\le j\le q).
\]
Here \(1\le q<m\), and \(\mathbf G\) is the weighted cubic profile.
The zero reflected terminal clock makes \(G_0=0\) directly.
Let \(d=m-q-1\). On the proper rows the moment conditions imply
\[
 G_i=\frac{P(x_i)}{x_i\prod_{j\ne i}(x_i-x_j)}
 \quad\text{for some polynomial }P\text{ of degree at most }d.
\]
Indeed the displayed vectors annihilate all \(q\) tests
by the top divided-difference identity for polynomials of degree
at most \(m-2\). Their dimension is \(d+1=m-q\) by distinct
evaluation and nonzero cofactor denominators, exactly the nullity
of the moment matrix by Vandermonde.

If the first \(d+1\) proper score residues are zero, the literal
causal equation for \(\mathbf G\) makes all of its first \(d+1\)
proper entries zero there too. Hence \(P=0\) and all of
\(\mathbf G\) is zero. At the first nonzero proper score \(w_i\),
the earlier inputs in each of \(\mathbf W_1,\mathbf W_2\) are
zero. The two lower row equations therefore force the same
literal diagonal to be both \(y_i/2\) and \(y_i/3\), impossible.
Existence of a nonzero proper weight is automatic if the scalar
quadrature is exact through degree two: otherwise the first
and second positive moments would both equal the terminal weight,
yet their values \(1/2,1/3\) differ modulo \(p\).

## Exact one-gap instance

For a potential width-19 splice using ten old rows, eleven
scored suffix rows and two whole copies, consider the 12 scalar
sites \(j/8\) for \(0\le j\le12,\ j\ne9\), with the unscored
origin and all eleven prescribed scored rows. The scalar degree
eleven quadrature fixes the weights uniquely. The nontrapezoid
low cubic match at head \(1,5/4,3/2,11/8\) allows a paid
affine cubic *profile* in exact rational arithmetic, so the scalar
gate alone does not exclude it.

But \(m=10,q=8,d=1\). At \(p=37\) the weights at \(5/4\) and
\(3/2\) are \(148/31185\) and \(962/5145525\), both zero in
the residue field. All clock guards hold because the nonzero
index gaps are at most 12 and the denominator is 8. This excludes
every continuation of that head, including all choices of the two
old shared sites. The third score also vanishes modulo 37,
although the first two are enough.

The standalone exact replay derives the entire scalar quadrature
from integrated cardinal polynomials and checks both the paid
scalar cubic match and the literal residue guards. The core-only
Lean file verifies the numerical scalar diagonal contradiction for
each possible first live row and the two zero-score residue gates,
not the general Vandermonde/causality argument.
