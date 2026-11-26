# Parity extrapolation for exact unit-diagonal DIRK order

Let $p\ge1$, $r=\lceil p/2\rceil$, and
$U_p\coloneqq\mathbb Z[1/p!]$. There is an explicit formula
for a lower triangular RK tableau with unit diagonal entries,
exact cleared rooted order $p$, and
$$
                          s=\frac{r(r+1)}2 .
$$
It works in every nonzero commutative unital ring with
$p!$ invertible. The next tall-tree defect is a unit,
including when $(p+1)!$ is not a unit. For $p\ge3$ the
constructed diagonal is **not common**. This is an upper
bound, not a minimum in the DIRK class.

## The two branch types

For even $p=2r$ choose $n_i=2i$, $1\le i\le r$.
Branch $n=2m$ comprises $m$ consecutive implicit
midpoint steps of size $2H/n$ across macrostep $H$.

For odd $p=2r-1$ choose $n_i=2i-1$.
Branch $n=2m+1$ comprises $m$ such midpoint steps,
then one implicit Euler step of size $H/n$.
In either branch the strict entries into stage $j$ from
all earlier stages of that branch are $2/n$, and the
diagonal is $1/n$. A midpoint output weight is $2/n$;
the optional final implicit Euler weight is $1/n$.
The $i$-th branch has exactly $i$ stages.

Use the same interpolation weights as in midpoint
extrapolation, namely
$$
 \lambda_i=\prod_{j\ne i}\frac{n_i^2}{n_i^2-n_j^2}.
$$
They reproduce the value at zero of polynomials of
degree at most $r-1$ in $z=1/n^2$.
Put the branch matrices on the diagonal and multiply
their output weights by $\lambda_i$. No additional
stage is needed for this affine combination, because
$\sum_i\lambda_i=1$.
All $n_i\le p$, and their squared differences factor
as $4(i-j)(i+j)$ in the even case or
$4(i-j)(i+j-1)$ in the odd case. The sum factors
for distinct indices are at most $p-1$; all necessary
inverses already belong to $U_p$. When $p=1$
there is just one implicit Euler stage.

## Direct parity proof on literal rooted trees

This proof uses the actual stage recursion, including
its diagonal contribution. Write $q=|t|$ and
$F(t)=\prod_{u\text{ child of }t}u!$, so $t!=qF(t)$.
In this section first work over $\mathbb Q$.
For a polynomial $Q$, define polynomials
$\mathcal M Q$ and $\mathcal E Q$ by
$$
 \begin{array}{ll}
 \Delta_2(\mathcal M Q)(X)=Q(X+2)+Q(X),&
         (\mathcal M Q)(1)=Q(1),\\
 \Delta_2(\mathcal E Q)(X)=2Q(X+1),&
         (\mathcal E Q)(0)=0,
 \end{array}
 \qquad \Delta_2 f(X)=f(X+2)-f(X).
$$
Existence and uniqueness follow by solving triangularly
in polynomial degree; the leading coefficient on
$\Delta_2 X^j$ is $2j$. Each map raises the degree
of a nonzero $Q$ by one and divides its leading
coefficient by $\deg Q+1$.

If $Q(-X)=\varepsilon Q(X)$, where $\varepsilon=\pm1$,
both maps give parity $-\varepsilon$.
Indeed for each equation $-\varepsilon f(-X)$ has
the same difference. For $\mathcal E$ it has the same
value at zero. For $\mathcal M$, its difference equation
at $-1$ gives
$(\mathcal M Q)(-1)=-\varepsilon Q(1)$, so the reflected
candidate has the same value at $1$.
This proves the parity by uniqueness.

At the lattice point $X=2j-1$ the first operator reads
$$
  (\mathcal M Q)(2j-1)
       =Q(2j-1)+2\sum_{\ell<j}Q(2\ell-1).
$$
The unscaled stage polynomials are therefore
$$
 \phi_{\bullet}=1,\qquad
 \phi_t=\prod_{u\text{ child of }t}\mathcal M\phi_u .
$$
At stage $j$ of branch $n$, the literal raw stage
value is $n^{-(q-1)}\phi_t(2j-1)$: a factor $1/n$
is paid by each edge, and the diagonal and strict
weights inside that factor are respectively one and
two. Induction on the tree shows that $\phi_t$
has degree $q-1$, parity $(-1)^{q-1}$, and
leading coefficient $1/F(t)$.

For odd $n$ the raw output is
$n^{-q}(\mathcal M\phi_t)(n)$, since the last
stage has unscaled weight one. For even $n$ it is
$n^{-q}(\mathcal E\phi_t)(n)$, since
$(\mathcal E Q)(2m)=2\sum_{j=1}^{m}Q(2j-1)$.
In both cases the numerator polynomial has parity
$(-1)^q$, degree $q$, and leading coefficient
$1/t!$. For even $n$ it also vanishes at zero.
Thus the raw reads are polynomials in $1/n^2$;
their degree bounds in the two parity classes are
$$
      \lfloor(q-1)/2\rfloor\quad(n\text{ even}),\qquad
      \lfloor q/2\rfloor\quad(n\text{ odd}).
$$
The constant term in either class is $1/t!$.
All polynomials through $q\le p$ have degree at
most $r-1$ in the selected parity, so interpolation
gives
$t!\,\mathbf b\cdot\boldsymbol{\Phi}_t(A)=1$
for every paid literal tree. The use of $\mathbb Q$
in the proof is harmless: the actual coefficients
are in $U_p\subset\mathbb Q$ and the cleared
polynomial identities pass to every base change.

## The unit next-tall defect

On the scalar equation, put $x=H\lambda$, $s=x/n$,
and $a=\operatorname{artanh}(s)$. The branch stability
functions are
$$
 R_n^{\mathrm{even}}(x)=\exp(na),\qquad
 R_n^{\mathrm{odd}}(x)=(1-s^2)^{-1/2}\exp(na).
$$
A midpoint microstep multiplies by $(1+s)/(1-s)$;
a final implicit Euler halfstep multiplies by $1/(1-s)$,
giving the formulas. The coefficient of $x^q$ is
the literal read of the $q$-vertex tall tree.
For $q=p+1$ the terms of mesh degree below $r$
are still paid by interpolation. The top coefficients are
$$
 \begin{array}{c|c|c}
  p & q & [\,x^q(1/n^2)^r\,]\,R_n(x)\\ \hline
 2r   & 2r+1 & 1/(2r+1)\\
 2r-1 & 2r   & \binom{2r}{r}/4^r.
 \end{array}
$$
For even $p$ the first coefficient comes from the
linear term in the exponential of $na$; for odd
$p$ the second comes solely from the prefactor.
The exact-flow contribution is the constant mesh
coefficient. Lagrange interpolation gives the
uncancelled moment
$$
               \sum_i\lambda_i n_i^{-2r}
                     =(-1)^{r-1}\prod_i n_i^{-2}.
$$
Multiplying the remaining error by $q!$ and using
$\prod_{i=1}^r(2i-1)=(2r)!/(2^r r!)$ yields the
cleared defect
$$
 \begin{cases}
 (-1)^{r-1}\binom{2r}{r}/4^r,&p=2r,\\
 (-1)^{r-1},&p=2r-1.
 \end{cases}
$$
The first is a ratio of paid factorials and powers
of $2$, hence a unit in $U_p$; the second is a
unit outright. These cleared identities computed
over $\mathbb Q$ descend without needing to invert
$(p+1)!$. Conversely the paid $p$-vertex tall
tree already makes $p!$ a unit.

The existing backward Euler extrapolation count
is $p(p+1)/2$. Here the count is $55$ at order
20, compared with $210$ for that baseline and
$101$ for the separately proved explicit midpoint
parity family. This is not a claim about known
optimized tableaux or literature priority.

## Architecture and stage sharing

Within affine combinations of the two displayed
fixed-macrostep branch types, the separate scalar
mesh moments are necessary as well as sufficient.
Indeed, in increasing $k$, degree $2k$ forces
the odd-class moment at $n^{-2k}$ to vanish, since
only the odd prefactor has a nonzero top coefficient.
Degree $2k+1$ then forces the even-class moment
at $n^{-2k}$, from the nonzero coefficient of
$\operatorname{artanh}$; the odd moment already
vanishes. Thus a participating even class requires
at least $1+\lfloor(p-1)/2\rfloor$ levels, and a
participating odd class at least $1+\lfloor p/2\rfloor$
levels, by the same homogeneous Vandermonde test
as in explicit midpoint extrapolation. The least
positive integers of the required parity minimize
the stage cost for that class. Mixing classes
does not improve this count.

There is no shared initial derivative in these
all-unit-diagonal branches. On the scalar test the
stage $j$ on branch $n$ is
$(1+x/n)^{j-1}/(1-x/n)^j$; its pole location
and order distinguish the branch and stage.
For the selected indices $n\le p$ the same
test after a residue specialization distinguishes
all stages: $n_i-n_j$ and $2$ are units where
needed. In particular, for $r>1$ the different
diagonals $1/n_i$ have unit differences in the
coefficient ring and cannot become a common
diagonal by any allowed nonzero base change.

## Optional odd-order explicit-start variant

If one permits a single zero-diagonal origin,
there is a cheaper layout for odd $p=2r-1$.
For $n=2m+1$, take $m$ trapezoidal steps of size
$2H/n$ followed by an explicit Euler step $H/n$.
The endpoint derivative of each trapezoidal step
is already the starting derivative of the next;
all levels also share the initial $f(y)$.
Thus the stage count is $1+r(r-1)/2$.
All noninitial diagonal entries are $1/n$ on their
respective branches; this is not an all-unit-diagonal
DIRK or a genuine SDIRK.

For completeness the parity proof is also literal.
The unscaled stage operator on the even lattice
$X=2j$ satisfies
$$
   \Delta_2(\mathcal T Q)(X)=Q(X+2)+Q(X),\qquad
   (\mathcal T Q)(0)=0 .
$$
It reads zero at the origin and
$Q(0)+2\sum_{k=1}^{j-1}Q(2k)+Q(2j)$ at positive
$j$. The same reflection argument flips parity
and gives the integral leading coefficient.
The unscaled odd-endpoint read of the resulting
stage polynomial $Q$ at $n=2m+1$ is
$Q(0)+2\sum_{k=1}^mQ(2k)$. Its polynomial
extension $G$ satisfies
$\Delta_2G(X)=2Q(X+1)$, $G(1)=Q(0)$.
In the reflection check $G(-1)=-Q(0)$; the
reflected value is still $Q(0)$, since either
$Q$ is even or $Q(0)=0$. This proves the
same odd mesh degree and exact order through $p$.

The scalar odd prefactor is now
$(1-(x/n)^2)^{1/2}$ rather than its inverse.
Its coefficient of $(x/n)^{2r}$ is
$-\binom{2r}{r}/(4^r(2r-1))$; hence the
next cleared tall defect is $(-1)^r/p$, a
unit. For even targets a comparable trapezoidal
layout costs one more stage than the all-implicit
midpoint construction.
