# Independent multihop Dirichlet unit Gram check

This checks the reference Gram calculation only. Let $h\ge1$ be the
number of commutator hops, $r\ge0$ the total polynomial degree cutoff,
and $P_*=2h+2r+1$. The monomial Gram form of the joint hop
moments through degree $2r$ is perfect over
$\mathbb Z[1/(P_*!)]$. No square roots or real positivity are needed
for this conclusion. Through literal order $p\ge P_*$ it therefore
specializes to any nonzero commutative coefficient ring: the bush
equations make $1,\ldots,p$ units and give the localization map.

## The moment normalization

Write $x_i$ for the $i$th ordered hop and
$\rho_i=1-\sum_{j\le i}x_j$, with $\rho_0=1$. The reference measure on
the $h$-simplex is unnormalized, with density
$\rho_h\prod_{i=1}^h x_i$. Its monomial functional is
$$
 \Lambda(x^\alpha)=
 \frac{\prod_{i=1}^h(\alpha_i+1)!}
 {(2h+|\alpha|+1)!}.
$$
This is the integer simplex beta integral: for exponents
$\kappa_1,\ldots,\kappa_h$ and slack exponent $b$, the numerator is
$b!\prod_i\kappa_i!$ and the denominator is
$(b+\sum_i\kappa_i+h)!$, by conditioning on the first coordinate and
applying the one-variable beta integral.

The literal word grade for the stated hop moment is
$2h+|\alpha|+1$. Expanding the gap powers uses scalar words
$\mathbf b\cdot(C^{k_h}H C^{k_{h-1}}H\cdots H C^{k_0}\mathbf1)$
with $\sum_i k_i=|\alpha|$. In the word model each $H$ is
$J^2$, giving one gap factor on every interval of
$0\le u_0\le\cdots\le u_h\le1$. The gap powers restore the indicated
monomial after expansion, and integrating $u_0$ at fixed gaps
leaves precisely the slack factor $\rho_h$. The integration computes
universal rational coefficients: the words and their model
coefficients use only denominators within the paid grade. Taking
$\alpha$ as the sum of two degree-at-most-$r$ indices pays the entire
Gram form at the announced budget.

## Monic one-variable beta norms

For nonnegative integers $a,b,n$ use weight $t^a(1-t)^b$ on $[0,1]$.
Set
$$
 R_n(t)=\frac{\partial_t^n\!\bigl(t^{n+a}(1-t)^{n+b}\bigr)}
                  {t^a(1-t)^b},\qquad
 L_n=(-1)^n\frac{(2n+a+b)!}{(n+a+b)!},\qquad
 B_n^{(a,b)}=R_n/L_n .
$$
The Leibniz expansion puts $R_n$ in $\mathbb Z[t]$: each term
contains the displayed denominator as a polynomial factor.
Leading terms of the numerator and denominator give $L_n$, so
$B_n^{(a,b)}$ is monic. Repeated integration by parts against any
polynomial of lower degree gives zero; all boundary terms vanish
because derivatives of order less than $n$ of the numerator's
undifferentiated product vanish at both endpoints.

By monicity, the squared norm of $B_n^{(a,b)}$ is its pairing with
$t^n$. Integration by parts in that pairing gives a factor
$(-1)^n n!$ and an integer beta integral. Thus the exact norm is
$$
 D(n,a,b)=
 \frac{n!(n+a)!(n+b)!(n+a+b)!}
      {(2n+a+b)!(2n+a+b+1)!}.
$$
All normalizing factors and both numerator and denominator
factorials are within $2n+a+b+1$.

## Stick-breaking and a unitriangular basis

On the open simplex set $t_i=x_i/\rho_{i-1}$. Then
$$
 x_i=t_i\prod_{j<i}(1-t_j),\qquad
 \rho_i=\prod_{j\le i}(1-t_j),\qquad
 \det\frac{\partial x}{\partial t}=\prod_i\rho_{i-1}.
$$
The reference density times the Jacobian is simply
$\prod_i t_i(1-t_i)^{1+2(h-i)}$, since two copies of
$\rho_{i-1}$ occur, from $x_i$ and the Jacobian, and $\rho_h$
adds one power of every $1-t_i$.

For a multi-index $\nu$ put $N_i(\nu)=\sum_{j>i}\nu_j$ and
$b_i(\nu)=1+2(h-i)+2N_i(\nu)$. Define
$$
 F_\nu(x)=\prod_{i=1}^h
  \rho_{i-1}^{\nu_i} B_{\nu_i}^{(1,b_i(\nu))}
       \bigl(x_i/\rho_{i-1}\bigr).
$$
This formula is polynomial, not a division requirement on any
tableau. Expand each bracket as
$\sum_{k=0}^{\nu_i} c_{ik}x_i^k\rho_{i-1}^{\nu_i-k}$.
It has total degree at most $\nu_i$ and monic leading term
$x_i^{\nu_i}$ in the order that compares
$(\beta_h,\ldots,\beta_1)$ lexicographically. Every nonleading
term decreases the exponent at $i$ while adding variables only
at indices less than $i$. Consequently the leading monomial of
the product is $x^\nu$ with coefficient one, and the degree is
at most $|\nu|$. Thus the $F_\nu$ with $|\nu|\le r$ give an exact
unitriangular basis change among all monomials of that degree range.

In the $t$ variables the brackets factor independently:
$$
 F_\nu(x(t))
   =\prod_i
        (1-t_i)^{N_i(\nu)}
        B_{\nu_i}^{(1,b_i(\nu))}(t_i).
$$
For distinct $\nu,\mu$, choose the largest differing index $i$;
there their tail sums agree and both beta polynomials have the
same weight after including the prefactors. Their degrees differ,
so this one beta integral vanishes in the product pairing. For
$\nu=\mu$, all factors are the exact one-variable norms.

## Exact budget and the ring conclusion

Put $s_i=h-i+1+\sum_{j\ge i}\nu_j$. For $n=\nu_i$, $a=1$ and
$b=b_i(\nu)$, the $i$th norm factor is
$$
 D_i=
 \frac{\nu_i!(\nu_i+1)!(2s_i-\nu_i-1)!(2s_i-\nu_i)!}
      {(2s_i)!(2s_i+1)!}.
$$
The largest factorial index is $2s_i+1$, at most
$2h+2|\nu|+1\le P_*$. The beta leading-coefficient normalization
only needs factors through $2s_i\le P_*-1$. All these bounds hold
for zero degrees too. Hence the basis coefficients already lie in
$\mathbb Z[1/((P_*-1)!)]$, and every diagonal norm
$\Lambda(F_\nu^2)=\prod_i D_i$ is a unit in
$\mathbb Z[1/(P_*!)]$.

Let $G$ be the monomial Gram matrix and $T$ the unitriangular basis
change. The rational identity $T^{\mathsf T}GT=
\operatorname{diag}(\prod_iD_i)$ is an identity in that localization:
all entries are already there, and the localization embeds in
$\mathbb Q$. It therefore specializes to any ring in which $P_*!$
is a unit, including rings with zero divisors or positive
characteristic when the required units exist. In particular
$\det G=\prod_{|\nu|\le r}\prod_iD_i$ is a unit, so all pairings
against the degree-at-most-$r$ space detect its vectors.

Two precise limitations:

- Perfect is not synonymous with anisotropic or orthonormal.
  A nonzero vector can have zero square pairing after scalar
  extension (already over $\mathbb C$ for two diagonal unit
  entries). The ring argument detects a vector paired against
  the whole degree space, not against itself alone.
- $P_*$ is the actual top word budget of this Gram calculation,
  not a claim that every factor in $P_*!$ is arithmetically
  indispensable. If $P_*$ is prime there is a genuine
  one-less-localization obstruction: the Gram entry for
  $x_1^r$ paired with itself is $(2r+1)!/P_*!$, of valuation
  $-1$ at that prime since $h\ge1$. It is not in
  $\mathbb Z[1/((P_*-1)!)]$. If $P_*$ is composite, the two
  localizations coincide. That coincidence does not itself pay
  a missing highest-degree word.

No support consequences, rank cases, tableau constructions or
claim about minimal literal order are part of this check.
