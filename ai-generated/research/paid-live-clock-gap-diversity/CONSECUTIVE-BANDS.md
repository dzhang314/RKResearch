# Order ceilings for consecutive arithmetic bands of net gaps

Use the notation and literal order hypothesis of
[Paid net clock-gap moments and support](NET-GAPS.md), and write $G=G_1$.
Over an ordered field, suppose
$$
  G\subseteq\lambda\{a+1,a+2,\ldots,a+w\},
  \qquad \lambda\ne0,\quad a\ge0,\quad w\in\mathbb Z_{\ge0}.    \tag{1}
$$
The bound is on surviving **net** gaps. It holds in particular if every
clock-changing edge into a nonzero output weight has a gap in (1).
Then
$$
 \begin{array}{c|ccccc}
    w&0&1&2&3&w\ge4\\ \hline
    p\text{ at most}&2&4&4&6&2w-1 .
 \end{array}                                                 \tag{2}
$$
At $w=1,\ p=4$ the sole actual gap must be $1/2$.
At $w=3,\ p=6$ the scale must be $\lambda=1/(2a+4)$.
These are necessary conditions, not constructions or attainability
claims. An independently translated gap set is not covered by (1).

## The full band hull and its leading coefficients

The one-step moments through degree $p-3$ are
$$
  \sum_{\delta\in G}\mu_1(\delta)\delta^q
     =\frac{1}{(q+2)(q+3)}
     =\int_0^1 x^q x(1-x)\,dx .
$$
All integrals in the ordered-field argument can be read as formal
polynomial antiderivative evaluations. With $u=2x-1$, the functional
becomes $1/8$ times the polynomial moments of the weight $1-u^2$ on
$[-1,1]$. Thus the full allowed hull
$$
  P(u)=\prod_{j=1}^{w}\bigl(u-(2\lambda(a+j)-1)\bigr)
$$
is orthogonal for $1-u^2$ to every polynomial of degree at most
$p-3-w$. Its product with any such polynomial is paid and vanishes
at every actual gap. This argument uses the full band even when an
allowed root does not occur or its net mass is zero.

For the unscaled weight, let $\Lambda$ be its moment functional and
let $Q_n$ be its monic degree-$n$ orthogonal polynomial. The odd
moments are zero and
$$
    \Lambda(u^k)=\frac{4}{(k+1)(k+3)}\qquad(k\text{ even}).
$$
The finite Gram matrices are positive definite over the reals; their
rational elimination pivots are positive and give the same
nondegeneracy over every ordered field. Symmetry gives parity $n$
for $Q_n$. Omitting terms with negative exponents,
$$
 \begin{aligned}
 Q_n(u)&=u^n+\alpha_nu^{n-2}+\gamma_nu^{n-4}+\cdots,\\
 \alpha_n&=-\frac{n(n-1)}{2(2n+1)},\\
 \gamma_n&=\frac{n(n-1)(n-2)(n-3)}{8(2n+1)(2n-1)} .
 \end{aligned}                                               \tag{3}
$$
Indeed $L=(1-u^2)\partial_u^2-4u\partial_u$ is self-adjoint for this
weight, since $(1-u^2)Lf=((1-u^2)^2f')'$ with zero boundary terms.
It preserves the degree filtration. Self-adjointness makes $LQ_n$
orthogonal to all lower-degree tests, since applying $L$ to any such
test does not raise its degree. The leading coefficient then gives
$LQ_n=-n(n+3)Q_n$. On $u^k$ its two terms are
$k(k-1)u^{k-2}-k(k+3)u^k$. Comparing degrees $n-2,n-4$ gives
the denominators $4n+2$ and $8n-4$, respectively, which gives (3).

## Excluding $2w+1$

Take $w\ge2$. Let $M=a+(w+1)/2$ and $V=(w^2-1)/12$, the mean and
variance of the permitted strides under uniform counting, not under the
signed gap masses. Put
$$
   \eta=\frac{V}{(w-1)M^2}\le\frac{1}{3(w+1)},\qquad
   m=2\lambda M-1 .
$$
The hull roots have mean $m$ and variance
$\sigma^2=(w-1)\eta(m+1)^2$. If $p\ge2w+1$, orthogonality gives
$P=Q_w+\xi Q_{w-1}$. The coefficient of $u^{w-2}$ equals
$\alpha_w$ by parity. Equating it to the sum of pair products of roots
gives
$$
   \binom w2 m^2-\frac w2\,\sigma^2=\alpha_w
   \quad\Longleftrightarrow\quad
   \eta(m+1)^2-m^2=\frac{1}{2w+1}.
$$
Completing the square bounds the left side by $\eta/(1-\eta)$.
But $\eta\le1/(3(w+1))<1/(2w+2)$, making this bound strictly
less than $1/(2w+1)$. Hence $p\le2w$ for $w\ge2$, in particular
$p\le4$ when $w=2$.

## The even endpoint

Suppose $p\ge2w$ and $w\ge3$. Now
$P=Q_w+\xi Q_{w-1}+\zeta Q_{w-2}$ with $\xi=-wm$.
The root deviations from $m$ are symmetric. The uncentered roots
therefore have the third elementary symmetric sum
$$
    e_3=\binom w3 m^3-\frac{w(w-2)}2m\sigma^2.
$$
In the orthogonal expansion the coefficient of $u^{w-3}$ is
$\xi\alpha_{w-1}$. Comparing it to $-e_3$, if $m\ne0$, gives
$$
     \eta(m+1)^2-\frac{m^2}{3}=\frac{1}{2w-1}.
$$
The left side is bounded by
$\eta/(1-3\eta)\le1/(3w)<1/(2w-1)$. Thus $m=0$, so
$\lambda=1/(2M)$. For $w=3$ this is the required scale at $p=6$.
The centered odd cubic then passes the hull test against constants,
but this does not assert realizability or survival of every allowed gap.

For $w\ge4$, put $s_0=(w+1)/(2M)$ and $T=s_0^2\in(0,1]$.
The centered roots are $s_0$ times the nodes $2j/(w+1)-1$.
The coefficients in degrees $w-2,w-4$ are
$a_*T,g_*T^2$, with
$$
 a_*=-\frac{w(w-1)}{6(w+1)},\qquad
 g_*=\frac{w(w-1)(w-2)(w-3)(5w+7)}{360(w+1)^3}.
$$
For the unscaled nodes the sums of squares and fourth powers are
$S_2=w(w-1)/(3(w+1))$ and
$S_4=w(w^2-1)(3w^2-7)/(15(w+1)^4)$. These follow by expanding powers
of $j-(w+1)/2$ and summing over $1\le j\le w$. The coefficients
follow from $-S_2/2$ and $(S_2^2-2S_4)/8$, respectively.
Since $\xi=0$, the second coefficient fixes
$\zeta=a_*T-\alpha_w$. The fourth coefficient would require
$$
  E(T):=g_*T^2-\gamma_w-(a_*T-\alpha_w)\alpha_{w-2}=0.
$$
Writing $D_w=w(w-1)(w-2)(w-3)$, substitution of (3) gives
$$
 \begin{aligned}
 E(1)&=\frac{D_w(w+2)(5w^2+23w+48)}
              {360(w+1)^3(2w-3)(2w-1)}>0,\\
 2g_*-a_*\alpha_{w-2}
     &=-\frac{D_w(5w^2+31w+36)}{180(w+1)^3(2w-3)}<0 .
 \end{aligned}
$$
Indeed $E(1)/D_w$ first simplifies to
$(5w+7)/(360(w+1)^3)+(5-w)/(24(w+1)(2w-3)(2w-1))$.
Now
$$
 E(T)-E(1)=(T-1)\bigl(g_*(T+1)-a_*\alpha_{w-2}\bigr)\ge0
$$
because $T\le1$ and $g_*>0$. This contradicts the required
quartic coefficient. It excludes $p=2w$ for $w\ge4$.

For $w=0,1$ the generic support theorem gives the first two entries
in (2). At the single-gap endpoint $p=4$, the nonzero mass is $1/6$
and its first moment is $1/12$, forcing the gap $1/2$.

## Physical stride, lag, and multiplicity

Let $c_i=c_0+\lambda k_i$ be a forward ladder with integer levels.
Assume the actual surviving nonzero net gaps use positive level
increments and let $w$ be their largest level increment. For
$p\ge5$ the support is nonempty. Applying (2) to the full initial
window $\lambda\{1,\ldots,w\}$ forces an actual surviving increment
of at least
$$
  J(p)=
    \begin{cases}
      3,&p=5,6,\\
      \lceil(p+1)/2\rceil,&p\ge7 .
    \end{cases}
$$
A nonzero net mass supplies at least one literal $A_{ij}\ne0$ into
a stage with $b_i\ne0$ at that increment. It counts a difference of
level labels, not automatically an occupied-level count or a
physical-index lag.

If the physical stage indices are in **increasing integer level
order**, and each intermediate lattice level between the endpoints
is occupied by at least $m_0$ stages, a $k$-level jump has signed
lag $i-j\ge1+m_0(k-1)$. Thus the maximum live-receiver lag in
that chronology is at least $1+m_0(J(p)-1)$. Merely making each
level contiguous in an arbitrary order does not suffice. If the
endpoints and every intermediate level are all at least $m_0$-fold,
the total number of stages is at least $m_0(J(p)+1)$; this last
count needs occupancy, not a stage ordering. Empty levels and
repeated same-level stages must not be confused with distinct
nonzero gaps. These are conditional physical consequences, not
unconditional stage floors for ERK or DIRK.

The same ordered-field bounds apply to a selected additive-tableau
word only with the mixed colored payment and common endpoint clock
specified in the [net-gap proof](NET-GAPS.md). No assumption of
positive physical weights is used.

## Separate initial-band statement over rings

Over a nonzero commutative ring with the literal paid units one can
still prove the weaker $p\le2w+1$ for the **initial** band
$\lambda\{1,\ldots,w\}$, $w\ge2$. If $p\ge2w+2$, the full
degree-$w$ monic hull is orthogonal to degrees $<w$.
The degree-$<w$ Gram determinant is a unit by the net Hankel theorem
and the invertible centering $u=2x-1$. Uniqueness and symmetry
give parity (2 is a unit). Its sum of roots is zero, whence
$\lambda(w+1)=1$ by cancellation of the paid unit $w$.

The same eigen-equation for this hull can be checked without any
unpaid integration denominator. For monomial exponents $i,j$
with $s=i+j\ge2$, the self-adjoint difference is proportional to
$(s-1)\Lambda(u^{s-2})-(s+3)\Lambda(u^s)$, which is zero by the
paid moment formula. The largest even $s$ with $i\le w,\ j<w$
is $2w-2$, so the needed denominators are at most $2w+1$;
odd moments vanish and $s=0,1$ are direct. Orthogonality and the
unit Gram matrix now give the eigen-equation by the degree
filtration. Its second coefficient is $\alpha_w$ in (3), whereas
the centered initial band has $a_*=-w(w-1)/(6(w+1))$, also for
$w=2,3$. Their difference
$$
    a_*-\alpha_w
       =\frac{w(w-1)(w+2)}{6(w+1)(2w+1)}
$$
is a unit, so cannot vanish. This contradiction proves the stated
initial-band ring result, not the stronger ordered-field ceilings.
