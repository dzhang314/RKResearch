# A polynomial-size common-diagonal variable-prefix family

**Separate mathematical construction.** This produces a repeatable
order family at a prescribed common diagonal, with no additional
coefficient field, but not a competitive unrestricted stage count.
See the [exact bounded-block classification](PREFIX-BLOCK-ORDER.md); this is a smaller constructive route than its general
tensor grid, not a change to that proof.

Fix a characteristic-zero field K, γ∈K, and a formal step h.
For a polynomial vector field f write g(y)=f(y+γ h g(y)) and
E_τ(y)=y+τ h g(y), with T_τ its pullback on functions.
A history of these Euler moves is an actual strict prefix RK
branch with diagonal γ: the i-th physical stage solves
Y_i=z_(i−1)+γ h f(Y_i) and its update is
z_i=z_(i−1)+τ_i h f(Y_i). Thus its strict coefficients are
B_(i,j)=τ_j for j<i. A signed affine mixture of branch
endpoints is a literal RK tableau with arbitrary signed
b_i, by taking the same signed factors times its increments.

## 1. Virtual midpoint from two same-diagonal moves

Since E_γ^−1=id−γ h f, for any scalar s

    E_(γ±s/2) ∘ E_γ^−1 = id ± s h f/2.

The actual implicit midpoint map for f at step s h is
(id+s h f/2)∘(id−s h f/2)^−1. Therefore it equals

    M_s = E_(γ+s/2) ∘ E_(γ−s/2)^−1,

and its pullback is T_(γ−s/2)^−1 T_(γ+s/2). The inverse here
is only a virtual series operator; it is not a physical
negative number of copies of the map. The physical increment τ_- itself may be negative.

For n≥1 put s=1/n, τ_±=γ±1/(2n). Consider the actual word

    P_n(m) = [ T_-^m T_+ ]^n,     m=0,1,...,p.

At m≥0 this is the prefix pattern of m increments τ_-
and one τ_+, repeated n times. In the h-jet through
degree d, T_-^m can be expanded via the finite generalized
binomial formula in T_-−I; each term `binom(m,j)(T_-−I)^j`
starts at h^j. Thus every h^d coefficient of P_n(m)
is polynomial in m of degree at most d. This uses the
total number of positive-grade factors across all n
copies, not a separate degree-p loss at each copy.
At m=−1 generalized binomial gives the exact formal
inverse. Therefore the one scalar interpolation

    β_m = (−1)^m binom(p+1,m+1),        m=0,...,p,
    Σ β_m P_n(m) = (M_(1/n)^*)^n       modulo h^(p+1)

holds as an operator on all finite jets. In particular
the whole signed combination uses one common physical γ
even though it behaves, to the paid order, like iterated
midpoint with a different step-dependent implicit scale.

## 2. The outer even-power extrapolation

Put q=ceil(p/2), ξ_n=1/n² for n=1,...,q, and let w_n
be the rational Lagrange weights evaluating a polynomial
at 0 from those ξ_n nodes. Denote pullback by a star.
The exact midpoint inverse relation M_(-s)=M_s^−1
makes log(M_s^*) odd in s h. Its leading term is
s h D_f, and the remaining coefficients are operators
independent of s. Hence

    log[(M_(1/n)^*)^n]
      = h D_f + Σ_(j≥1) h^(2j+1) ξ_n^j L_(2j+1).

This identity is formal in the filtered associative algebra;
log and exp are only power series in a single element when
taking the nth power, so noncommutation of the L_j is harmless.
The h^d coefficient after exponentiation is polynomial in
ξ_n of degree at most floor((d−1)/2) for d≥1, with value
at ξ=0 the exact-flow coefficient. Indeed in any product of
r≥1 factors of grades 2j+1 the ξ power is (d−r)/2.
For d≤p the degree fits the q samples. Thus

    Σ_(n=1)^q Σ_(m=0)^p w_n β_m P_n(m) id

gives exact flow through order p for every polynomial
vector field, and therefore pays every literal rooted
tree. The separation by monomial-coordinate vector
fields or the exact prefix-moment basis proves this last
implication without a tree census. The combined branch
weights sum to 1, so this is an ordinary RK output, not
a composition of affine mixtures at intermediate stages.

The raw number of stages is

    Σ n(m+1) = q(q+1)(p+1)(p+2)/4.

Within each fixed n the initial τ_- prefixes can be
shared literally, saving q p(p−1)/2 stages if desired.
All τ and b lie in Q(γ); no root search or field extension
is needed. For m≥1 each nonconstant branch uses just
two increments, in at most 2n chronological blocks.
This does not contradict the earlier obstacle for
individually self-adjoint, consistent, same-γ branches:
the physical words here are not midpoint themselves.
Only their *signed combination* implements its virtual
inverse to paid order.

## 3. Exact order, not just at least

For every prescribed γ one can target p+1 in Sections
1–2 and add the operator correction
(T_1−I)^(p+1) id. This is a signed combination of the
endpoints of a single unit-increment prefix of length
p+1 (the coefficients sum to zero), and corresponds to
ordinary extra output weights on those common-diagonal
stages. It vanishes through order p and has leading
term h^(p+1) D_f^(p+1) id, nonzero on the linear test
f(y)=y. Thus exact order p is achieved in the same
coefficient field, even at prescribed exceptional γ.
There is no depth-optimality claim.

For freely chosen sufficiently small nonzero rational γ,
the original degree-p prescription already has exact
order p without this correction. Here is an algebraic
check, rather than an assumption about generic order.
On the linear test, for r=p+1 the z^r coefficient of
the physical branch

    (1+τ_- z/(1−γz))^(mn) (1+τ_+ z/(1−γz))^n

is polynomial in m of degree ≤r with leading coefficient
n^r τ_-^r/r!. The inner interpolation remainder at
−1 is this leading coefficient times
∏_(m=0)^p(−1−m). After both extrapolations, the actual
z^r coefficient minus the corresponding virtual-midpoint
coefficient is therefore

    (−1)^(p+2) Σ_n w_n (nγ−1/2)^(p+1).

At γ=0 this difference is −2^(−p−1). If p is odd, the
virtual-midpoint formula pays order p+1 already. If
p=2q, its z^(2q+1) error is
Σ_n w_n ξ_n^q/[(2q+1)4^q]: that top ξ power comes only
from the one log term. The magnitude is at most
1/[(2q+1)4^q], strictly smaller than 2^(−p−1).
So the physical first-unpaid tall defect at γ=0 is
nonzero in both parities. It is a polynomial in γ,
since all physical increments and output weights above
are affine in γ with rational coefficients. Therefore
for all sufficiently small nonzero rational γ the same
stage count is of exact order p. This parameter check
does not confuse the γ=0 tableau with a strict SDIRK.

This is an actual degree-controlled algebraic family across
orders, not a numerical special-order search; it does not
improve any verified unrestricted stage-count entry.

An individual history need not be a midpoint history. It can be one in a degenerate case: if γ=1/(2n), the minus increment vanishes, so all shared-length variants at that n realize the same repeated midpoint map. In particular, the at-least-order-one construction with γ=1/2 need not have exact order one.
