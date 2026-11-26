# Sharp positive threshold for all shifted-Volterra Chebyshev prefixes

For m≥1 and real γ>0
let V be integration from 0 to y and T=V−γ id. Let a_m be the
smallest zero of the ordinary Laguerre polynomial L_m^(0), and
τ_m=1/a_m. Then the following are equivalent:

1. For every r≥1, the r-dimensional space T^m R[y]_<r is a strict
   Chebyshev space on (0,1): no nonzero member has r distinct zeros
   in that interval.
2. γ≥τ_m.

The threshold includes equality on the **open** interval. This is a
statement about all prefixes starting with r=1. Its failure does not
say that an individual moment matrix or a particular split-hull
problem is singular. The statements at γ=0 or negative γ are
separate and are not modified here.

## 1. Factorial jets as positive-exponential orthogonality

Use the factorial coefficient bijection B sending y^j/j! to z^j.
Then B(VP)=z B(P) and B(T^mP)=(z−γ)^m B(P). Thus P of degree
≤r+m−1 belongs to T^m R[y]_<r exactly when B(P) has a zero at z=γ
of multiplicity at least m. For s>0 one has the finite identity

    F_P(s) = ∫₀∞ e^(−s u) P(u) du = B(P)(1/s)/s.

The factor 1/s is nonzero and the change z=1/s has nonzero derivative
at s=1/γ. Consequently the jet condition is equivalent to

    ∫₀∞ e^(−u/γ) P(u) u^j du = 0,   j=0,...,m−1.           (1)

This follows by differentiating the finite explicit terms j!s^(−j−1)
for each monomial, so no delicate interchange is needed.

If P had r distinct prescribed interior roots, write P=R S with R
the degree-r monic polynomial of those roots and deg S<m. All
coefficients are real. By (1) taking the test polynomial S would give

    ∫₀∞ e^(−u/γ) R(u) S(u)^2 du = 0.                         (2)

We prove that the latter signed form is positive for every nonzero S
of degree <m and every R with r roots in (0,1), once γ≥τ_m. The
weight outside the unit interval is only a proof of the jet property,
not a change to the RK moment functional.

## 2. Classical Laguerre facts used, and the r=1 and r=2 cases

For nonnegative integer a use

    L_j^(a)(v)=Σ_(k=0)^j (−1)^k binom(j+a,j−k) v^k/k!.

For weight v^a e^(−v) on (0,∞) these are orthogonal, with squared
norm (j+a)!/j!. Indeed the Rodrigues identity followed by j
integrations by parts proves zero pairing against lower degrees;
all boundary terms vanish, since derivatives of e^(−v)v^(j+a)
of order below j vanish at zero and infinity. On L_j^(a) its j-th
derivative is (−1)^j, giving the stated norm. The usual sign-change
argument for a positive weight implies j simple interior roots:
if fewer, multiply by the polynomial of the actual sign changes and
orthogonality gives a contradiction.

For a=0 let λ_i be the reciprocals of the m positive roots. The first
two elementary symmetric sums, from the displayed coefficients, are
m and m(m−1)/4. In particular

    Σ λ_i² = m(m+1)/2,   τ_m=max λ_i ≥ (m+1)/2.              (3)

We will also use the upper bound τ_m≤sqrt(m(m+1)/2).

For r=1 and R(u)=u−a, a∈(0,1), use the m Gaussian nodes for
exp(−u/γ), namely γ times the roots of L_m^(0). These are all ≥1
when γ≥τ_m. To recall exactness, divide any polynomial of degree
≤2m−1 by the degree-m orthogonal polynomial. The quotient part
integrates to zero and vanishes at the nodes. The remainder is
interpolated and integrated using its cardinal weights. The weights
are strictly positive because the already exact rule on a cardinal
square gives its nonzero positive integral. Applying the rule to
(u−a)S² gives a strictly positive sum: `u_i−a>0`, and a nonzero
polynomial of degree <m cannot vanish at all m nodes. The same test
with a=1 is **nonnegative** even when the smallest Gaussian node is
exactly 1.

For r=2 fix S and set

    B(a,b)=∫₀∞ e^(−u/γ)(u−a)(u−b)S² du.

It is affine in each endpoint separately and hence a convex
combination of its four corner values for (a,b)∈[0,1]². At (0,0)
and (1,1) it integrates respectively u² S² and (u−1)² S², both
strictly positive. At (1,0) and (0,1) use

    u(u−1)=(u−1)²+(u−1).

The first term has strictly positive integral and the second is
nonnegative by the a=1 Gaussian test. So all four corner values
are strictly positive. This proves r=2 at the same threshold,
including equality; it does not assume both endpoint factors have
one fixed sign on (0,1).

## 3. Uniform tail dominance for r≥3

Let R have all its r roots in (0,1) as above. For u≥1,
`R(u)≥(u−1)^r`. For 0≤u≤1,
`|R(u)|≤max(u,1−u)^r`, whose integral on that interval is
`2(1−2^(−r−1))/(r+1) < 2/(r+1)`.

Put `Q(v)=S(1+γ v)` and
`N=∫₀∞ v^r exp(−v) Q(v)^2 dv > 0`. The positive tail satisfies

    I_+ = ∫₁∞ e^(−u/γ) R(u) S(u)^2 du
          ≥ γ^(r+1) exp(−1/γ) N.                            (4)

For u∈[0,1], v=(u−1)/γ lies in [−1/γ,0]. Expand Q in the first m
associated Laguerre polynomials with parameter r and apply ordinary
Cauchy–Schwarz using their above norms. This gives

    |Q(v)|² ≤ N Σ_(j=0)^(m−1) [j!/(j+r)!] (L_j^(r)(v))².

For t≥0, each coefficient in L_j^(r)(−t) is nonnegative, and

    L_j^(r)(−t) ≤ binom(j+r,r) exp(j t/(r+1)).

In fact the ratio of its k-th binomial coefficient to its constant
binomial coefficient is `j! r!/((j−k)!(r+k)!)≤(j/(r+1))^k`,
and the remaining term is t^k/k!. Since t≤1/γ here, use the norm
factor and the hockey-stick sum to obtain the explicit kernel bound

    |Q(v)|² ≤ N exp(2(m−1)/(γ(r+1))) / r! · binom(m+r,r+1).   (5)

Combining (4), (5), `e^(−u/γ)≤1` below u=1, and the integral of
max(u,1−u)^r, bounds the potentially negative mass divided by the
positive tail by

    [2/((r+1)r!)] [binom(m+r,r+1)/γ^(r+1)]
       · exp((1+2(m−1)/(r+1))/γ).

Two elementary estimates are uniform in r,m. For r≥3 and
γ≥(m+1)/2 the exponent is ≤1, since
`1+2(m−1)/(r+1)≤(m+1)/2`. Also

    binom(m+r,r+1)/γ^(r+1)
      ≤ [2^(r+1)/(r+1)!] [m/(m+1)] ∏_(j=1)^r [(m+j)/(m+1)]
      ≤ 2,

because `(m+j)/(m+1)≤(j+1)/2` for m,j≥1. The ratio is therefore at
most `4e/((r+1)r!)≤e/6<1`. This makes the full integral in (2)
strictly positive. No estimates of the individual roots of R or of
L_m need to be made. By (3) this argument applies whenever γ≥τ_m.
Together with r=1 and r=2 it proves sufficiency of the threshold.

## 4. Sharpness, open boundary, and what can be transported

On the first prefix,
`T^m 1 = (−γ)^m L_m^(0)(y/γ)`. If 0<γ<τ_m its smallest positive
root y=γ a_m lies in (0,1), so this first prefix is not Chebyshev.
At equality it is at y=1, not in the open interval. The positive
forms above prove the same strict *interior* determinant bounds for
all r at equality, despite possible vanishing at that endpoint.

For any r, all initial prefix determinants then have one nonzero
sign on each sorted chamber. Therefore pairing r tests
`T^m(y^j/j!)`, 0≤j<r, against degrees <r on the **unit interval**
is invertible by the ordinary sign-change argument: border the
first k+1 tests at the k actual sign changes of a nonzero P with
an evaluation row at y. The resulting test has the corresponding
alternating signs and P times that test has nonzero integral.
The same argument forces the unique monic degree-r orthogonal
polynomial against those r tests to have r simple interior roots.
For real-algebraic γ its coefficients are in Q(γ), and its roots
can be adjoined as a finite real-algebraic extension.

Thus a layer of the existing all-tree ancestor-hull method with
adjoint exponent m can use this as a split certificate provided its
paid test count ν+1 fits its r nodes **and** γ≥τ_m. A coarse explicit
sufficient check is γ²≥m(m+1)/2. Neither the test-count budget nor
whether the roots already belong to a prescribed small field is
settled by the Chebyshev theorem. It does not buy width below the
terminal moment rank, arbitrary positivity, new tableau topology,
or nonexistence below τ_m for particular degrees or particular
hull moments. The exceptional-width consequence is recorded in a
separate audit candidate.
