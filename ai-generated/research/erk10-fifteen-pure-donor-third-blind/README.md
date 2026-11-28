# Asymmetric pure-donor signed triple: exact third-blind exclusion

This closes the pure-\(r\) case of the rational canonical six-opening
signed-triple order-ten chart, **without a reflection assumption**,
when the first, second and first-composed reverse defects are
opposed on the triple. Individual shares can be signed or zero,
and the second duplicate's tap is not fixed. The generic nonpure
case is already excluded over \(\mathbb Q\) by the
[strong cubic adapter](../erk10-fifteen-signed-triple-cubic-pressure/ACTUAL-ORDER-ADAPTER.md).
These are chart obstructions, not a general 15-stage ERK10 bound.
A reverse chart with genuine singleton leakage of the composed
defect is not covered here.

Keep the canonical opening, actual cubic decoder \(EJ\Pi-BE\Pi\),
eight distinct scalar sites, and physical reverse order
\[
           1,A,A,T,A,D,E,F,G
\]
of the [literal adapter](../erk10-fifteen-signed-triple-cubic-pressure/ACTUAL-ORDER-ADAPTER.md).
In reverse coordinates \(Y=1-X\), write \(a,t,d,e\) for the
ordinates of \(A,T,D,E\), and \(R=1-r\). The opening donor \(r\)
is pure through size five. Assume that
\[
 \boldsymbol u=L\boldsymbol y-\boldsymbol y^{\odot2}/2,\quad
 \boldsymbol g=L\boldsymbol y^{\odot2}-\boldsymbol y^{\odot3}/3,\quad
 \boldsymbol h=L\boldsymbol u
\]
are supported on the physical triple and have zero weighted
aggregate. The reverse row sums are \(L\boldsymbol 1=\boldsymbol y\).
No further reverse exactness is assumed; the pressure tests below
are supplied by literal rooted order ten.

Over \(\mathbb Q\) all six grouped interior masses are nonzero:
an interior zero could be deleted from the possible support,
contradicting the [anchored degree-nine scalar floor](../rational-endpoint-moment-nine/README.md).
The pure-donor obstruction itself is algebraic in any field with
\(10!\ne0\), provided the grouped masses at \(A,T\) are nonzero.
The helper sees only 0 and \(a\), so paid first and second moments
give \(t^3/3=a t^2/2\), i.e. \(t=3a/2\).
No other division by an individual share is used.

## Three tests blind to the last two physical rows

Write
\[
 H(Y)=Y(Y-a)(Y-t)(Y-d),\qquad
 \kappa(Y)=-Y^4/4+(a+t)Y^3/3-atY^2/2 ,
\]
\(\rho(Y)=-\kappa(Y)/Y\),
\(\boldsymbol k=L\boldsymbol y^{\odot3}-\boldsymbol y^{\odot4}/4\),
\(\boldsymbol m=L\boldsymbol y^{\odot4}-\boldsymbol y^{\odot5}/5\),
and \(\boldsymbol v=\boldsymbol g/2+\boldsymbol h\),
\(\boldsymbol P=L\boldsymbol v\).
The [short outer-word derivation](../erk10-fifteen-pure-donor-mirror/ASYMMETRIC-PRESSURES.md)
implies that \(\boldsymbol k,\boldsymbol P\) annihilate
\(X(X-r)\mathcal P_3\) and
\(\boldsymbol m,L\boldsymbol k,L\boldsymbol P\) annihilate
\(U=X(X-r)\mathcal P_2\). It also supplies
\(L\boldsymbol g,L\boldsymbol u\) on \(U\).
Only the necessity part is used.

Take the actual blind test \(f=X(X-r)(X-F)(X-G)\) in \(U\).
The [quartic gate](../erk10-fifteen-pure-donor-mirror/README.md)
is \(\int f(X)(J_YH)(1-X)=0\). A second gate follows similarly:
through the row at \(D\), every actual predecessor has reverse
clock \(0,a,t\). Thus those rows' *physical* entries satisfy
\[
   k_j=\kappa(y_j)+(a+t)g_j-at u_j .
\]
Through the row at \(E\), every predecessor of \(L\boldsymbol k\)
is one of these rows. The last two rows are killed by \(f\).
The already paid \(L\boldsymbol g,L\boldsymbol u\) actions and
the paid raw integrals through \(\boldsymbol y^{\odot4}\)
therefore give
\[
                     \int_0^1 f(X)(J_Y\kappa)(1-X)\,dX=0 .
\]

For the third gate, the first two physical occurrences at \(a\)
have the same \(v=-a^3/6\), independently of the second's tap
\(q_0\) on the first: at that second occurrence
\(g=q_0a^2-a^3/3\) and \(h=-q_0 a^2/2\).
At the helper \(T\), \(v=0\). Hence at any of the three \(A\)
rows, \(L\boldsymbol v\) is \(-a^3/6\) times the total prior
tap on clock \(a\). The prior taps have clocks \(0,a,t\), so
that total is
\[
  \big[t(L\boldsymbol y)_i-(L\boldsymbol y^{\odot2})_i\big]/
       \big[a(t-a)\big].
\]
Taking weighted means and using the paid first and second
primitive moments gives the exact mean
\(\Gamma_a=-5a^4/36\). At \(T\) the corresponding mean is
\(\Gamma_t=(-a^3/6)t^2/(2a)=-3a^4/16\).
The second duplicate tap \(q_0\ne0\): otherwise both predecessor
\(u\)'s are \(-a^2/2\), so the nonzero total tap \(t^2/(2a)\)
makes \(h_T\ne0\). Consequently \(\boldsymbol u,\boldsymbol v\)
are independent on the triple: \(\boldsymbol v\) has the same
nonzero first two entries, whereas the first two \(u\)'s differ.
They span the weighted-null two-dimensional triple space.

Let \(\Gamma_d=P_D\), and let \(\sigma(Y)\) be the cubic
interpolating \(0,\Gamma_a,\Gamma_t,\Gamma_d\) at \(0,a,t,d\).
Up through \(D\), the difference of \(\boldsymbol P\) from this
scalar profile is supported on the triple and has weighted mean
zero. It is thus a linear combination of the two independent
triple vectors, extended by zero. Through \(E\) every predecessor
is in this initial part; the remaining outputs are blind.
The tests of \(L\boldsymbol u,L\boldsymbol v,L\boldsymbol P\)
on \(f\) now pay \(L\sigma(\boldsymbol y)\). The lower raw
primitive tests for \(\sigma\) make this exactly
\[
                     \int_0^1 f(X)(J_Y\sigma)(1-X)\,dX=0 .
\]
All integrands above have degree at most nine.

## Four cofactor variables

Put \(P_4(Y)=(Y-a)(Y-t)(Y-d)(Y-e)\). At a scalar site \(z\)
let \(\mu_z\) be the integral of the eight-site monic
nodal polynomial with its factor \(Y-z\) removed.
Set \(\theta_z=(z-R)\mu_z/P_4'(z)\) for \(z=a,t,d,e\).
Lagrange's formula cancels the two final clock factors in
the blind test: the scalar mass times \(f(1-z)\) at one
of these four sites is \(\theta_z/z\).
The remaining site with \(Y=0\) has primitive value zero;
the other three sites are roots of the blind test.
Thus the two first blind tests are
\[
  \sum_z \theta_z\, (J_YH)(z)/z=0,\qquad
  \sum_z \theta_z\, (J_Y\kappa)(z)/z=0 .
\]

The cubic and \(L\boldsymbol v\) tests on
\(X(X-r)\mathcal P_3\) give another cofactor rule. For any such
raw defect, multiply its six grouped weights by
\(x(x-r)\) in forward ordinates. Annihilation of degree at most
three makes those weights a linear combination of the two
cofactor vectors \(1/H_{\rm off}'(x),x/H_{\rm off}'(x)\),
where \(H_{\rm off}\) is the six-site hull without endpoints.
On substituting Lagrange masses, the reverse data
\((z-R)\mu_z\) times the grouped defect's mean divided by \(z\)
are therefore *affine* in \(z\). This remains true if \(R=z\):
there is no division by \(z-R\).

Apply the rule to \(\boldsymbol k\) at \(a,t,d\), where the
means are \(\kappa(a),\kappa(t),\kappa(d)\). It gives the row
\[
 (d-t)\rho(a)P_4'(a)\theta_a
 +(a-d)\rho(t)P_4'(t)\theta_t
 +(t-a)\rho(d)P_4'(d)\theta_d=0 .
\]
Together with the two first blind rows this is a \(3\)-by-\(4\)
matrix. The [symbolic receipt](exact-audit.txt) computes its
alternating minors. Their common factor is
\[
             a^5(a-d)(3a-2d)(d-e)/3 ,
\]
nonzero by distinctness. After removing it, write the cofactor
vector as \(\boldsymbol Z\); two of its entries are
\[
\begin{aligned}
 Z_d &=-3a^3e(a-e)(3a-2e)(15a-11e)/40960,\\
 Z_e &= 3a^3d(a-d)(3a-2d)(15a-11d)/40960.
\end{aligned}
\]
These cannot both vanish. In characteristic 11 the last
factors are \(15a\ne0\); in other paid characteristics,
their common vanishing would give \(d=e\).
So the rank is three and \(\boldsymbol\theta\) is a
nonzero multiple of \(\boldsymbol Z\), the nonzero claim
following already from \(\mu_a,\mu_t\ne0\) and \(a\ne t\).

## Fraction-free third gate and contradiction

Define the base cubic
\(\sigma_0(Y)=aY^3/9-a^2Y^2/4\), satisfying the required
values at 0, \(a\) and \(t\). Write
\[
   \sigma(Y)=\sigma_0(Y)
   +\frac{\Gamma_d-\sigma_0(d)}{d(d-a)(d-t)}
                       Y(Y-a)(Y-t).
\]
The \(\boldsymbol P\) cofactor rule, used with \(\boldsymbol Z\),
is
\[
\begin{aligned}
 G_{\rm den}&=(t-a)Z_dP_4'(d),\\
 G_{\rm num}&=d\big[(t-d)Z_aP_4'(a)\Gamma_a/a+
                 (d-a)Z_tP_4'(t)\Gamma_t/t\big],\\
 G_{\rm den}\Gamma_d&=G_{\rm num}.
\end{aligned}
\]
Multiply the third blind gate by \(d(d-a)(d-t)G_{\rm den}\)
and use this equation. The resulting numerator contains no
\(\Gamma_d\) and never divides by \(G_{\rm den}\).
The exact factor is
\[
 -\frac{9}{53687091200}\, a^8d^2e^2(a-d)^3(a-e)^2
 (3a-2d)^3(3a-2e)^2(15a-11e)(d-e)^2.
\]
All the visible collision factors are nonzero. Thus
\(15a-11e=0\), so \(\theta_d=0\).
The cubic row and the \(\boldsymbol P\) affine cofactor rule,
now at \(a,t,d\) with zero \(d\)-coefficient, are independent
on \(\theta_a,\theta_t\):
\[
 \frac{\Gamma_a/a}{\rho(a)}=-5/6,\qquad
 \frac{\Gamma_t/t}{\rho(t)}=-4/3.
\]
They force \(\theta_a=\theta_t=0\). Since \(\mu_a,\mu_t\ne0\),
this would make \(R=a=t\), a contradiction. The same proof
permits a zero individual weight at any physical triple row.

## Reproduce

    python3 -B audit.py
    sha256sum -c sha256.txt

The replay uses exact symbolic integration, determinant expansion and
polynomial factorization. The stand-alone Lean ring receipt checks
the integer-scaled cofactor and scalar numerator identities. The
rooted chronology, weighted-null reduction and final tableau
exclusion are mathematical, not a native HasOrder theorem.

The two ring identities and the scalar endpoint
thirdGateNoTwoMasses were replayed on Lean 4.36.0 with standard
axioms; see [the local audit](lean-4.36.0-audit.txt). The latter
consumes the explicit cleared cofactor equations and nonzero masses,
not a literal HasOrder input.
