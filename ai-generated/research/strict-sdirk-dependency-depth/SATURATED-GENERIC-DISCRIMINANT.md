# A generic square-class obstruction for saturated paid hulls

**Separate mathematical supplement.** The diagonal is an
indeterminate t in this note. Its statements about a function
field cannot be used as necessity at any fixed algebraic diagonal. At t=0 the tests below are the specialization of this full rational-function family; the actual zero-diagonal ancestor test span can have smaller dimension.

Let V be integration from 0, and let H_(m,n)(t;y) be the unique
monic degree-n polynomial orthogonal on [0,1] to the n tests

    (V−t id)^m (y^j/j!),       j=0,...,n−1.

Here m≥0, n≥1. This is the actual saturated paid hull when the
available ancestor test dimension equals the number of nodes.

## 1. Two regular endpoint specializations

The tests are polynomial in t. At t=0 they are y^(m+j)/(m+j)!;
the moment pairing is nonsingular by positive definiteness for
weight y^m. Normalizing each test by (−t)^m gives a polynomial in
1/t whose specialization at infinity is y^j/j!, also nonsingular.
The monic solution over Q(t) is therefore regular at both places.
Writing J_n^(α,β) for the monic shifted Jacobi hull of weight
(1−y)^α y^β, the two specializations are

    H_(m,n)(0;y) = J_n^(0,m)(y),
    H_(m,n)(∞;y) = J_n^(0,0)(y).

Both have simple real roots by the sign-change argument for positive
weights. Their discriminants are nonzero.

If H_(m,n) splits over a constant algebraic extension C(t), then
both specialized hulls split over C: its roots are integral at
each of the integrally closed local rings C[t]_(t) and
C[1/t]_(1/t) by the monic regular coefficient equation, and so
have values in C there.

There is a weaker but sometimes easier obstruction, which also
combines across multiple cuts. For all their discriminants δ_i(t)
define rational square classes

    a_i = [δ_i(0)/δ_i(∞)] in Q*/Q*².

If a product of the δ_i(t) is square over any algebraic constant
extension C(t), it is a rational constant times a square over Q(t):
factor it over Q; every zero and pole has even multiplicity over
the algebraic closure, hence so does every irreducible factor over
Q. The rational-square factor has neither zero nor pole at 0 or
∞ because the product's two values are finite and nonzero.
Thus the corresponding product of the a_i is a rational square.
Consequently dim span{a_i}=d implies a relative degree divisor
2^d for the generic simultaneous splitting field over C(t), by
the independent Vandermonde quadratic subextensions. In
particular one nontrivial endpoint ratio rules out generic
preservation over any fixed Gaussian splitting field enlarged
only by the indeterminate diagonal.

## 2. An exact discriminant-ratio ledger

For nonnegative integers α,β, put D_n^(α,β)=disc J_n^(α,β).
An elementary recurrence is

    D_n^(α,β) =
       n^n /(n+α+β+1)^(n−1)
       · [ binom(n+α,n−1) binom(n+β,n−1)
           / binom(2n+α+β,n−1)^2 ]
       · D_(n−1)^(α+1,β+1),                             (1)

with D_1=1. To check it, put P=J_n, a=y(1−y), and Q=P'/n.
Integration by parts against a(1−y)^α y^β identifies Q with
J_(n−1)^(α+1,β+1). The symmetric Sturm–Liouville operator
a∂²+[(β+1)−(α+β+2)y]∂ preserves degree and has leading term
−n(n+α+β+1) on y^n. By orthogonality it thus acts on P by
that scalar. In particular at each root z of Q,

    P(z) = −a(z) Q'(z)/(n+α+β+1).

Now |Res(P,P')|=n^n |Res(Q,P)|. Multiplying the last identity
over the roots of Q gives (1), because
prod a(z)=(-1)^(n−1) Q(0)Q(1) and prod |Q'(z)|=disc Q.
For the endpoints, Rodrigues' polynomial is obtained from
∂^k[y^(k+β)(1−y)^(k+α)] by dividing by the weight. Integrating
by parts proves its orthogonality. Its leading coefficient
is (−1)^k k! binom(2k+α+β,k), and its endpoint terms come from
the lowest power at each end. Thus the monic degree-k values
are (−1)^k binom(k+β,k)/binom(2k+α+β,k) at zero and
binom(k+α,k)/binom(2k+α+β,k) at one. Substituting the shifted
parameters of Q supplies exactly the binomial factors in (1).

Modulo rational squares, when n=2a+1 the ratio from (1) is

    [D_n^(0,m)/D_n^(0,0)]
      = [ prod_(j=1)^a (2j)(m+2j)
                         (2n−2j+1)(m+2n−2j+1) ].       (2)

For verification unroll (1) using k=n,n−1,...,2 and the
parameters shifted by n−k. On dividing the m case by the
zero case, the powers in the rational denominators contribute
only when k−1 is odd, i.e. k=2j; their factors become
(2n−2j+1)(m+2n−2j+1) modulo squares. The remaining binomial
ratio is prod_(i=1)^(n−1) binom(n+m,i)/binom(n,i).
The n! and (n+m)! powers have exponent n−1 even, and the
factorial factors remaining modulo squares are
prod_(i=1)^(n−1) i! (m+i)!. Since n−1 is even, only the
even indexed factors 2j and m+2j occur to odd exponent.
This proves (2).

## 3. An infinite saturated family with a genuine generic obstruction

For m=1 and odd n≥3, the product in (2) simplifies to

    [ (2n)!/(n+1) ].

The factors (2j)(2j+1) cover 2,...,n and the other consecutive
pairs cover n+2,...,2n. Bertrand's prime between n and 2n
has valuation one in this quotient: it cannot be n+1 because
n+1 is even and >2. Thus the class is nonsquare. The discriminant
of H_(1,n)(t;y) is nonsquare over even the algebraic constants
with t adjoined, forcing a generic relative degree divisible
by two.

These are actual saturated ancestor cuts, not a freely varying
monic model: for b≥1 take p=4b+3, s=3b+2, d=b+1, and
r=n=2b+1<q=ceil(p/2). The error budget s−1−r is b, and its
adjoint power is d−b=1 with exactly 2b+1 paid tests. This
gives a generic obstruction at that family of cuts without
asserting an irreducible degree-n Galois group, and without
calculating any special-order hull.

At a prescribed algebraic γ the square class can change.
Neither (2) nor the generic degree shows any particular
real-split specialization needs extension of its old field
Q(γ)G. That is subject to the literal discriminant, group
or local inclusion tests in the separate fixed-field note.

For m=1 the endpoint discriminant quotient simplifies to the n-th Catalan number times ((n+1)/(2n+1))^(2n−2), by telescoping the consecutive Jacobi factors. Its square class is therefore [(2n)!/(n+1)].
