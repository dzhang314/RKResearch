# Exact explicit midpoint extrapolation over the paid coefficient ring

For every $p\ge1$ there is a strict explicit Runge–Kutta tableau
over $U_p\coloneqq\mathbb Z[1/p!]$ with exact cleared rooted order
$p$ and
$$
                  s=1+\left\lfloor\frac{p^2}{4}\right\rfloor
$$
stages. Its cleared tall-tree defect at order $p+1$ is the unit
$-1$. Thus the same claim holds under base change to every
nonzero commutative unital ring with $p!$ invertible. Conversely
the tall tree of order $p$ already forces that unit condition.

## Literal stages and denominators

Fix the macrostep $H$ and starting value $y$. For a positive
integer $n$, take the unsmoothed explicit midpoint sequence
$$
 \begin{split}
 Y_{n,0}&=y,\qquad Y_{n,1}=y+(H/n)f(Y_{n,0}),\\
 Y_{n,j+1}&=Y_{n,j-1}+(2H/n)f(Y_{n,j})\qquad (1\le j<n).
 \end{split}
$$
Use the endpoint $Y_{n,n}$, without evaluating $f(Y_{n,n})$.
The branch has $n$ derivative stages, at indices $0,\ldots,n-1$.
Unrolling the recurrence, the row for $Y_{n,j}$, including the
output when $j=n$, has coefficient $1/n$ at the initial stage
if $j$ is odd and $2/n$ at each positive index $k<j$ with
$k\equiv j-1\pmod2$. All other entries are zero. Thus the branch
is an explicit RK tableau with rational coefficients.

Take $r=\lceil p/2\rceil$ levels of the same parity as $p$:
$$
 n_i=2i\quad(p=2r),\qquad n_i=2i-1\quad(p=2r-1),
 \qquad 1\le i\le r.
$$
Let $z_i=1/n_i^2$. Return
$$
 \sum_{i=1}^r\lambda_i Y_{n_i,n_i},\qquad
 \lambda_i=\prod_{j\ne i}\frac{n_i^2}{n_i^2-n_j^2}.
$$
These are the Lagrange weights for evaluation at zero on
polynomials of degree at most $r-1$ in $z$. In particular
$\sum_i\lambda_i=1$, so the affine combination is one RK
method: share the initial derivative, list the remaining
branch stages without cross-branch edges, and add the
weighted output rows. The stage count is $1+\sum_i(n_i-1)$,
giving $r^2+1$ for even $p$ and $r(r-1)+1$ for odd $p$.

All $n_i$ are at most $p$. The node denominators use
$$
 n_i^2-n_j^2=
 \begin{cases}
  4(i-j)(i+j),&p\text{ even},\\
  4(i-j)(i+j-1),&p\text{ odd}.
 \end{cases}
$$
For distinct $i,j$ the sum factor is at most $p-1$.
Every prime in a denominator is therefore at most $p$.
For $p=1$ there is only the Euler branch and no denominator.
The tableaux and the $\lambda_i$ belong to $U_p$; the
$\lambda_i$ are units there. Formal operator coefficients
used in the proof below need not be computed or inverted
as part of a tableau.

## Even mesh dependence for each parity, with the correct order window

The argument in this section is formal over $\mathbb Q$.
For any polynomial vector field $f$, double the state and
write
$$
 \mathsf A_h(u,v)=(u+h f(v),v),\qquad
 \mathsf B_h(u,v)=(u,v+h f(u)),\qquad
 \mathsf R(u,v)=(v,u).
$$
The first two are the exact shears for the two summands of
$u'=f(v),\ v'=f(u)$. The exact doubled flow from $(y,y)$
stays diagonal and projects to the original flow. Let
$$
 \mathsf M_h=\mathsf A_{h/2}\mathsf R\mathsf A_{h/2},
 \qquad
 \mathsf S_h=\mathsf M_h^2
            =\mathsf A_{h/2}\mathsf B_h\mathsf A_{h/2}.
$$
Products here denote composition. For $h=2H/n$, induction
from the recurrence gives
$$
 \mathsf M_h^j(y,y)
     =(Y_{n,j-1}+(h/2)f(Y_{n,j}),\,Y_{n,j})\qquad(j\ge1).
$$
Indeed the next right half-shear and swap make the new
second coordinate $Y_{n,j-1}+h f(Y_{n,j})$. Projecting
to the second coordinate omits the final left half-shear.

Now work in the associative formal series algebra of
pullbacks on polynomials in $(u,v)$. Write the same symbols
for the pullbacks; the palindromic identities and powers
are unchanged. Since $\mathsf S_0=I$ and
$\mathsf S_{-h}=\mathsf S_h^{-1}$, its formal logarithm
$L(h)\coloneqq\log \mathsf S_h$ is odd:
$$
 L(h)=h(L_A+L_B)+\sum_{k\ge1}h^{2k+1}L_{2k+1},
$$
where $L_A,L_B$ are the directional derivative operators
along the two vector fields. Their sum generates the exact
doubled flow. There is no logarithm taken of $\mathsf M_h$
itself. Instead set
$$
        \Sigma_h\coloneqq\mathsf M_h\exp(-L(h)/2).
$$
As $\mathsf S_h=\mathsf M_h^2$, $\mathsf M_h$ commutes
with $L(h)$. Thus $\Sigma_h^2=I$, $\Sigma_0=\mathsf R$,
and, using $\mathsf M_{-h}=\mathsf M_h^{-1}$,
$\Sigma_{-h}=\Sigma_h^{-1}=\Sigma_h$. In particular
$\Sigma_h$ is an *even* formal series. The exact identity is
$$
 \mathsf M_h^n=\Sigma_h^{\,n\bmod2}
                         \exp\bigl((n/2)L(h)\bigr).
$$
Substitute $h=2H/n$ and $z=1/n^2$. A term of the
exponent with $z$-degree $k$ has $H$-degree $2k+1$;
its $z^0$ term is $H(L_A+L_B)$. Hence for $q\ge1$ the
coefficient of $H^q$ in the exponential is a polynomial
in $z$ of degree at most $\lfloor(q-1)/2\rfloor$:
each contributing nonempty product has $H$-degree
twice its $z$-degree plus its number of factors.
For even $n$ this is the full coefficient bound.
For odd $n$ there is also the even $\Sigma_h$ factor;
its $H^{2k}$ coefficient has $z$-degree $k$. The combined
bound is $\lfloor q/2\rfloor$. The two classes generally
have *different* coefficient polynomials.

In either class, the term at $z=0$, after diagonal
initialization and projection, is the exact formal flow:
the odd class inserts the constant swap, which fixes the
initial diagonal. The selected levels therefore interpolate
every coefficient through $H^p$ exactly. For even $p$ use
the first bound, and for odd $p$ the second. In both cases
the largest degree through $p$ is $r-1$. Using even
levels for an odd target would generally pay the next
even order too; that is not the odd construction above.

## Literal all-tree verification and exact first unpaid tree

No scalar test or unproved independence of elementary
differentials is needed here. For a given rooted tree $t$,
allocate one coordinate $x_v$ for each vertex $v$ and
start at zero. Take the polynomial vector field
$$
                  f_v(x)=\prod_{w\text{ child of }v}x_w,
$$
with empty product one. If $t_v$ is the rooted subtree
at $v$, induction on its children gives, for an RK tableau
$(A,\mathbf b)$,
$$
     f_v(Y_i)=H^{|t_v|-1}\boldsymbol{\Phi}_{t_v}(A)_i,\qquad
     (y_{\rm next})_v=H^{|t_v|}\,
                       \mathbf b\cdot\boldsymbol{\Phi}_{t_v}(A).
$$
The stage induction uses
$Y_i^w=H^{|t_w|}(A\boldsymbol{\Phi}_{t_w}(A))_i$
and then the product at the root. The exact solution is
$x_v(H)=H^{|t_v|}/t_v!$ by the same induction and integration.
Apply the formal flow agreement to the root of this field
for every $|t|\le p$. It gives the literal equations
$$
                  t!\,\mathbf b\cdot\boldsymbol{\Phi}_t(A)=1
$$
over $\mathbb Q$. Since the actual coefficients lie in
$U_p\subset\mathbb Q$, these polynomial identities hold
over $U_p$ and pass to every unital base change. This works
equally with ordered root lists: the products are coordinatewise.

Every directed stage path belongs to a single branch
after leaving the shared initial stage, and has at most
$p$ vertices. Hence $A^p=0$ globally, despite the larger
number of stages. For the first unpaid tall tree,
$$
 (p+1)!\,\mathbf b\cdot\boldsymbol{\Phi}_{\operatorname{tall}(p+1)}(A)-1
             =(p+1)!\,\mathbf b\cdot A^p\mathbf1-1=-1.
$$
This proves exact order $p$ in all the stated rings,
without making $(p+1)!$ invertible. The paid tall tree
also requires a path of length at least $p$ in vertices;
the construction attains that dependency depth.

## Counts and scope

The shared-initial Euler extrapolation baseline has
$1+p(p-1)/2$ stages, compared with the counts here:

| Order $p$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|:---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Midpoint stages | 1 | 2 | 3 | 5 | 7 | 10 | 13 | 17 | 21 | 26 |
| Euler stages | 1 | 2 | 4 | 7 | 11 | 16 | 22 | 29 | 37 | 46 |

| Order $p$ | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|:---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Midpoint stages | 31 | 37 | 43 | 50 | 57 | 65 | 73 | 82 | 91 | 101 |
| Euler stages | 56 | 67 | 79 | 92 | 106 | 121 | 137 | 154 | 172 | 191 |

This is a uniform family, not a stage minimum among all
explicit RK methods. In particular it does not improve
the separate ring tableaux of six, seven, and ten stages
at orders five, six, and seven. The companion
[architecture note](ENDPOINT-ARCHITECTURE.md) proves the
precise optimum for fixed-macrostep linear combinations
of these unsmoothed endpoints and the absence of further
literal stage sharing.

## Prior formulations

[Ketcheson and bin Waheed, §2.1.2, Algorithm 2 and equation (7)](https://doi.org/10.2140/camcos.2014.9.175)
already give the same unsmoothed even sequence and its
$p^2/4+1$ stage count; their §2.1.1 gives the Euler count.
[Hairer, Nørsett and Wanner, §II.9, Theorem 9.3](https://doi.org/10.1007/978-3-540-78862-1)
explicitly distinguishes the odd-index expansion from the
even-index one and attributes the former to Gragg.
[Blanes, Casas and Murua, §9.1.1](https://doi.org/10.1017/S0962492923000077)
explain the doubled-state Strang interpretation for
Gragg's smoothed endpoint, crediting Hairer et al. for
the extended system. Our single-coordinate projection
is the unsmoothed one; smoothing would evaluate the
endpoint derivative too. No literature-priority claim
is made. The result here is an explicit odd/even
all-tree proof with paid denominator support and a
unit certificate of the exact order.
