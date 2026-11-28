# The canonical pure-donor triple cannot use singleton leakage

This closes the pure-\(r\) chart of
[the canonical signed triple](../erk10-fifteen-signed-triple-cubic-pressure/ACTUAL-ORDER-ADAPTER.md)
over \(\mathbb Q\), including genuine leakage of the composed
reverse defect \(L\boldsymbol u\) at singleton clocks. Only grouped
exactness of the raw first and second reverse defects is assumed.
The result uses the actual physical reverse chronology
\(1,A,A,T,A,D,E,F,G\) and cubic decoder of that chart, with eight
distinct scalar sites and only the origin weighted in the opening.
It is not a general obstruction at fifteen stages.

Over \(\mathbb Q\) the grouped interior masses are nonzero by
[the anchored degree-nine floor](../rational-endpoint-moment-nine/README.md).
For the **pure-donor** chart the proof below also works over an
arbitrary field with \(10!\ne0\), \(19\ne0\), no square root of
\(-2\), and nonzero grouped masses at \(A,T,D\).
No ordered structure is necessary except as one possible way
to exclude that square root. The generic **nonpure** branch has
the separate [19-adic obstruction](../erk10-fifteen-signed-triple-cubic-pressure/README.md)
and does not inherit this field scope.

## Exact grade ledger and the blind moment matrix

Use \(Y=1-X\), reverse ordinates \(a,t,d,e\) at \(A,T,D,E\),
and \(R=1-r\). The high block and its weighted transpose obey
the literal decoder and reverse row sums in the linked chart.
Write \(\boldsymbol u,\boldsymbol g,\boldsymbol h,\boldsymbol k,
\boldsymbol m\) as in the [third-blind proof](../erk10-fifteen-pure-donor-third-blind/README.md),
with \(\boldsymbol h=L\boldsymbol u\),
\(\boldsymbol v=\boldsymbol g/2+\boldsymbol h\); here do not
assume singleton entries of \(\boldsymbol h\) vanish.
The grouped raw \(\boldsymbol u,\boldsymbol g\) tests at \(T\)
force literal exact first and second primitives there (its mass
is nonzero). It only sees \(0,a\), so \(t=3a/2\).
The weighted-null identities for \(\boldsymbol u,\boldsymbol g\)
on the triple itself are also assumed; the same grouping condition
at \(D\) has nonzero singleton mass.

The real source space \(U=X(X-r)\mathcal P_2\) consists of
actual rooted combinations through size five with opening
profile zero, by the
[early-null proof](../erk10-fifteen-pure-donor-mirror/README.md).
A mark \(X^j\) costs \(j\) additional leaves and keeps that
early-null property. A reverse primitive \(L\) or reverse clock
mark costs one order; nominal operations are \(J_Y\) and
multiplication by \(Y\). Thus any zero-nominal reverse word
difference of grade \(m\le5\) annihilates
\(\sum_{j=0}^{5-m}X^jU\). This follows by actual rooted orders
through ten and integration by parts (total scalar degree
at most nine); no word simplification assuming \(L\boldsymbol u\)
has one-clock support is used.

| Grade | Actual zero-nominal profiles used | Exact test space |
| --- | --- | --- |
| 3 | \(\boldsymbol h=L\boldsymbol u\) | \(X(X-r)\mathcal P_4\) |
| 4 | \(\boldsymbol k,L\boldsymbol g,L\boldsymbol h,L\boldsymbol v\) | \(X(X-r)\mathcal P_3\) |
| 5 | \(\boldsymbol m,L\boldsymbol k,L^2\boldsymbol h,L^2\boldsymbol v\) | \(U\) |

Take \(f=X(X-r)(X-F)(X-G)\in U\), which kills the last two
physical reverse rows. The first two gates
\(\int f (J_Y H)(1-X)=\int f (J_Y\kappa)(1-X)=0\) of the
[opposed proof](../erk10-fifteen-pure-donor-third-blind/README.md)
use only the actual grades listed above and the grouped first two
raw tests, so remain valid. Here \(H=Y(Y-a)(Y-t)(Y-d)\) and
\(\kappa=-Y^4/4+(a+t)Y^3/3-atY^2/2\).
The cubic cofactor collinearity for \(\boldsymbol k\) is also
unchanged. Use the same four blind variables
\[
 \theta_z=(z-R)\mu_z/P_4'(z),\qquad
 P_4(Y)=(Y-a)(Y-t)(Y-d)(Y-e),\quad z=a,t,d,e .
\]
They are a nonzero multiple of the verified rank-three cofactor
vector \(\boldsymbol Z\); the two relevant leading minors have
factors \(Z_d\propto15a-11e\), \(Z_e\propto15a-11d\), which
cannot both vanish. Write
\(\mathcal T_z=Z_zP_4'(z)\). Since \(\boldsymbol h\) kills
\(X(X-r)\mathcal P_4\), there is a single scalar \(\eta\) with
\[
   \mathcal T_z h_z/z=\eta
\]
at the four blind-node labels, where \(h_z\) is its weighted
site mean or physical singleton value. The same statement
holds in terms of \((z-R)\mu_z\) at all six offsites, up to
rescaling \(\eta\). This is the degree-four six-site cofactor
line for weights multiplied by \(X(X-r)\). It includes
coincidence \(R=z\) without division.

## Composed means and their common third gate

Let \(q_0=L_{A_2,A_1}\) be the second duplicate tap (not assumed
nonzero). The first two \(u\)-values are
\(-a^2/2,\ q_0a-a^2/2\), and the first two \(g\)-values are
\(-a^3/3,\ q_0a^2-a^3/3\). The determinant of these two
read directions is \(-q_0a^4/6\).
If \(q_0\ne0\), the two weighted-opposed profiles
\(\boldsymbol u,\boldsymbol g\) span every mean-zero triple
vector. If \(q_0=0\), they have the same first two entries;
any mean-zero triple vector also having equal first two entries
lies in a line, spanned by \(\boldsymbol u\) (its first entry
is nonzero and the total triple mass is nonzero).
In this degenerate case each of
\(L\boldsymbol v,L\boldsymbol h,\boldsymbol h\) has equal
first two entries at the triple. Thus subtracting the common
weighted mean at the triple can always be expressed by
\(\boldsymbol u,\boldsymbol g\) for these three profiles.

Put \(s=h_t\), the actual leakage at \(T\), and call the early
means of \(\boldsymbol P=L\boldsymbol v\) and
\(\boldsymbol Q=L\boldsymbol h\) respectively
\(\Gamma_a,\Gamma_t\) and \(\Lambda_a,\Lambda_t\).
The means of an \(A\)-row's total tap on \(a\) and total tap on
\(t\) are, respectively, \(5a/6\) and \(-2a/9\), by the
two grouped primitive equations and \(t=3a/2\).
At \(T\), the total tap on \(a\) is \(t^2/(2a)=9a/8\).
The first two \(v\)-values both equal \(-a^3/6\), while
\(v_t=s\). The first two \(h\)-values are
\(0,-q_0a^2/2=-a(u_{A_2}+a^2/2)/2\), and \(u_t=0\).
These actual earlier-tap relations give, with no division
by an individual share or by \(q_0\),
\[
\begin{aligned}
 \Gamma_a&=-5a^4/36-2as/9,&\Gamma_t&=-3a^4/16,\\
 \Lambda_a&=-a h_a/2-5a^4/24-2as/9,&
 \Lambda_t&=-as/2-9a^4/32 .
\end{aligned}
\]

For \(W=\boldsymbol P\) or \(\boldsymbol Q\), denote its early
means by \(w_a,w_t,w_d\) and let the cubic \(\sigma\) interpolate
those at \(a,t,d\) and zero at 0. Through \(D\), subtracting
\(\sigma\) leaves only a mean-zero triple profile in the span
just proved. Through \(E\), the actual \(LW\) sees only that
initial input; the last two rows are blind. The paid actions of
\(L\boldsymbol u,L\boldsymbol g\) and \(LW\) therefore give
\(\int f (J_Y\sigma)(1-X)=0\). The raw \(L\)-actions on scalar
polynomials of degree at most three are exact tested on \(f\).
This earns the third gate for both profiles, even with leakage.

Let \(\sigma_z(Y)=Y\prod_{u\in\{a,t,d\},u\ne z}(Y-u)/
[z\prod_{u\ne z}(z-u)]\), and
\(J_z=\sum_\xi Z_\xi (J_Y\sigma_z)(\xi)/\xi\).
Since \(W\) annihilates \(X(X-r)\mathcal P_3\), the
\(\mathcal T_z w_z/z\) are affine in \(z\) at these sites.
Eliminate \(w_d\) from that affine rule and the third blind
equation \(\sum J_z w_z=0\), **without** dividing by
\(\mathcal T_d\). The resulting coefficients of \(w_a,w_t\)
are
\[
 \left((t-a)\mathcal T_d J_a+\frac{d(t-d)\mathcal T_a J_d}{a},
       (t-a)\mathcal T_d J_t+\frac{d(d-a)\mathcal T_t J_d}{t}\right).
\]
The two verified exact expressions are
\((-6561/1342177280,\ 243/41943040)\) times a common
factor whose only possible zero under the physical distinctness
guards is \(15a-11e\).

## Exhausting the exceptional and generic branches

If \(15a-11e=0\), then \(Z_d=0\) and hence \(R=d\), because
\(\mu_d\ne0\). The \(\boldsymbol h\) cofactor constant \(\eta\)
is zero by its \(d\) term, so \(s=0\) at \(t\), where
\(\mathcal T_t\ne0\). Now the cubic and \(\boldsymbol P\)
cofactor equations on the \(a,t\) coefficients are independent:
the two ratios \((\Gamma_a/a)/\rho(a)=-5/6\) and
\((\Gamma_t/t)/\rho(t)=-4/3\) are different, where
\(\rho=-\kappa/Y\). They force \(\theta_a=\theta_t=0\),
contradicting the two nonzero masses.

Otherwise the common factor is nonzero, and both third gates
give \(w_a=32w_t/27\). Applying them to the two displayed
pairs yields
\[
                        s=3a^3/8,\qquad h_a=19a^3/36 .
\]
These are nonzero in the advertised domain. The \(\boldsymbol h\)
cofactor constant cannot vanish: that would force both
\(\mathcal T_a,\mathcal T_t=0\) and hence \(R=a=t\).
All the \(\mathcal T_z\) are therefore nonzero. Its \(a,t\)
equations give \(\mathcal T_t/\mathcal T_a=19/9\).
The factor identity in the replay now gives
\[
                 110a^2-87a(d+e)+60de=0 .
\]

A further blind test directly on \(L\boldsymbol h\) is
available at grade four. Interpolate the initial
\(\boldsymbol h\) means by the same cardinal cubics,
subtract the mean-zero triple part (the span argument above),
and test on \(f\) as for \(L W\). This gives exactly
\(\sum J_z h_z=0\).
Use \(h_z=\eta z/\mathcal T_z\). The symbolic sum is
\[
 \sum_{z=a,t,d}\frac{z J_z}{\mathcal T_z}
  =\frac{18(17a^2-15a(d+e)+11de)}
   {(42a^2-27a(d+e)+16de)(117a^2-63a(d+e)+31de)} .
\]
The denominator factors are the remaining factors of \(Z_a,Z_t\)
and cannot vanish in this branch. Hence the numerator vanishes.
The two exact equations imply \(3(d+e)=10a,\ de=3a^2\)
by the two elimination combinations in the replay (19 is the
only additional prime involved). Thus
\[
                           (3d-5a)^2=-2a^2 .
\]
Since \(a\ne0\), this contradicts nonsquareness of \(-2\).
This exhausts the pure-donor chart without restricting signs,
individual splits, reflection, or singleton leakage.

## Reproduce

    python3 -B audit.py
    sha256sum -c sha256.txt

The symbolic audit reconstructs the two leading minors, generic
third row, exceptional guard, and final two polynomial identities.
The rooted grade ledger and chronology argument are mathematical.
The preceding opposed-case module contains a native cofactor
proof and scalar conclusion on its own explicit hypotheses.

The separate native module ERK10FifteenPureDonorLeakageScalars.lean
proves forced_sums_and_square and requires_sqrt_neg_two from the
two exact final scalar equations over any field with the required
nonzero casts. Both replayed with standard axioms on Lean 4.36.0.
