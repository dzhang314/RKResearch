# A literal two-row moment excludes the degree-815 regular plateau alias

**Scope.** Continue the [explicit regular sparse plateau-alias projection](ERK11-NONZERO-TEN-TWELVE-SPARSE-PLATEAU-ALIAS-ELIMINANT.md): ERK11 at seventeen rows in the all-live half-clock, both-new, two-carrier chart, with ten nonzero-first-pool labels, twelve active rows, both plateau pairs, and \(\zeta=d\) at physical 9. This excludes its irreducible degree-815 **regular** width factor. Reflection gives the same exclusion for \(\zeta=a\). It does not exclude any of the other regular factors or the six rank/affine-pivot masks by itself. The ordered guards used to obtain the sparse width equations remain explicit; the new two-row argument and number-field lift require no additional order. No unrestricted stage interval changes.

## 1. Recover the common paid pool scale

Let \(D_s\) be the monic hull of the eight true active singleton labels. With the live regular pivots, those labels are the two calibrated nonplateau triples and the measured outer middle clocks \(x=c_8,z=c_{10}\). Thus \(D_s\) is the product of the two sparse cubic flank hulls (reflect the second to the physical clock), times \((X-x)(X-z)\), with the leading sign adjusted to be monic. No ordering of the two extras needs to be chosen, and no root of \(D_s\) is extracted in the arithmetic.

Let \(\widehat P,\widehat Q\) be the nonzero polynomial directions for the actual first and second response interpolants, fixed by the sparse profile formulas of the regular chart. Their degrees are at most one and four. The singleton half-clock \(h=a/2\) has actual response \(f_L(h)=a^2/8\). Its exact response sample gives the live relative normalization
\[
 P_*=\widehat P,\qquad
 Q_*=\frac{f_L(h)\widehat P(h)}{\widehat Q(h)}\,\widehat Q,\qquad
 P=\alpha P_*,\quad Q=\alpha Q_* .
\]
Here \(P,Q\) are the actual first and second interpolants, and \(\alpha\ne0\) is not the reflected response ratio. Both evaluations in the relative normalization are live because \(P(h),Q(h)=P(h)f_L(h)\) are singleton reads.

Set \(\Omega=X(X-1)(X-a)(X-d)\). Since the dormant center is already at \(d\), there is no need for an extra copy of its factor. The [exact divided-difference remainder proof](ERK11-NONZERO-TEN-TWELVE-ACTIVE-TWO-PAIR-GATES.md#2-a-ghost-remainder-without-a-simple-root-or-live-weight-condition) applies with this smaller hull. At each singleton the scalar term \(b_i\Omega(c_i)Q(c_i)\) is \(P(c_i)^2 c_i(c_i-1)/D_s'(c_i)\), while every other term vanishes or cancels by the opposite carrier shares at one clock. Thus, with
\[
 M_R(Z)=\int_0^1 [R(Y)-R(Z)]/(Y-Z)\,dY,\qquad R=\Omega Q_*,
\]
the two polynomial remainders
\[
 V_0=D_s M_R\bmod Q_*,
 \qquad V_1=P_*^2X(X-1)\bmod Q_*
\]
must satisfy \(V_0+\alpha V_1=0\). This just divides the original exact identity by the live common scale \(\alpha\); the model \(M_{\Omega Q}\) is linear in \(Q\). No zero or sign condition on a ghost mass or \(Q_*\) root is needed. At the selected good place the constant coefficient of \(V_1\) is live, so \(\alpha=-V_0(0)/V_1(0)\), where these are constant coefficients of the remainders. In particular the true scalar \(\alpha\) belongs to the algebraic width field and is integral at that place. We use this remainder equation to **fit the scale**, not as a claimed independent width exclusion.

The third-response interpolant \(B_\tau\) is determined too. The exact two-pair polynomial is \(P B_\tau-Q^2=\lambda D_s\). At the selected live place \(P_*\) retains degree one; hence the true \(P\) has degree one. With its root \(\xi\),
\[
 \lambda=-Q(\xi)^2/D_s(\xi),\qquad
 B_\tau=(Q^2+\lambda D_s)/P .
\]
The first denominator is live by the actual singleton distinction and is checked again in the residue. The last division is exact; the leading coefficient of \(P\) is a unit, so polynomial quotient arithmetic commutes with the reduction.

## 2. The unaliased left pair supplies a new paid mark

The width factor has degree 815 and is irreducible, so \(a\) is not the rational endpoint 1; \(a\ne0,d\) are inherited. The only dormant internal row is at \(d\), not at \(a\). Thus after carrier cancellation the ordinary scalar pool at \(a\) is exactly \(B_a=b_4+b_5\), for the two physical plateau rows. This is not the potentially aliased right ordinary pool.

Compute \(B_a\) from the true scalar quadrature without splitting its singleton hull. Let
\[
 \ell_a(X)=\frac{\Omega(X)}{(X-a)\Omega'(a)}
\]
be its degree-three Lagrange polynomial over the four residual labels. The actual singleton weight at \(x\) is \(\alpha P_*^2(x)/[D'(x) Q_*(x)]\), where \(D=(X-a)(X-d)D_s\). Therefore
\[
 B_a=\int_0^1\ell_a(X)\,dX
     -\frac{\alpha}{\Omega'(a)}
          [X^7]\operatorname{rem}_{D_s}
                 \left(P_*^2 X(X-1)\,[(X-a)Q_*]^{-1}\right).
\]
Indeed multiplying the singleton weight by \(\ell_a(x)\) cancels its \(x-d\) and leaves exactly the indicated numerator and denominator, with the factor \(D_s'(x)\). The leading coefficient of the degree-below-eight remainder gives the weighted barycentric sum. All exact singleton denominators are live; the inverse is taken modulo the monic \(D_s\) and is separately checked to exist after reduction. A collision of reduced singleton roots would not invalidate this computation; the barycentric argument happens in characteristic zero, while reduction just tests a polynomial inverse and remainder.

The paid first, second, and third response moments at \(a\) are
\[
 \nu=P(a)/D'(a),\qquad \mu=Q(a)/D'(a),\qquad \tau=B_\tau(a)/D'(a),
 \qquad D'(a)=(a-d)D_s(a) .
\]
The physical row-4 response is the already calibrated \(f=-a^2/2\). If row 5 has response \(g\), then
\[
 \nu-fB_a=b_5(g-f),\qquad
 \mu-f\nu=b_5 g(g-f),\qquad
 \tau-f\mu=b_5 g^2(g-f).
\]
Consequently the true two-row mark
\[
 \boxed{(\mu-f\nu)^2-(\nu-f B_a)(\tau-f\mu)=0}
\]
must hold, without dividing by any weight or second response. This uses the actual left pair mass reconstructed from scalar ordinary payment and the paid response moments through third power, rather than a rank or annihilator inference about an uncharged ghost.

## 3. One good place excludes every conjugate of the factor

The frozen sparse width replay factors its exact degree-1060 projection over \(\mathbb Q\); the sole degree-815 factor is irreducible, with full coefficient checkpoint. The deterministic companion takes that exact checkpoint, and its optional full run recomputes and matches the monic factor. At prime 29 this factor keeps degree 815 and has a **simple** root \(a=6\bmod29\). Any actual algebraic \(a\) on this irreducible factor can be embedded in \(\overline{\mathbb Q}_{29}\) so as to reduce to 6: Hensel's lemma supplies the desired simple-place root and irreducibility identifies its rational field with \(\mathbb Q(a)\). Extend the embedding to the algebraic width \(d\). This does **not** require every mod-29 factor to be tested; all exact degree-815 roots are conjugate, and we are free to choose a good place for any one of them.

At \(a=6\bmod29\) the genuine width polynomial \(\mathcal D\) retains full degree 13 in \(d\); thus \(d\) is integral. The **full gcd** of \(\mathcal D\) and the independent sparse first-pool numerator \(\Pi\) at that residue is \(d-9\). This covers every possible alternative reduction of \(d\) at that place and forces \(d=9\bmod29\), not a selected favorite width root. Every actual regular candidate must obey both exact polynomial equations before the reduction.

In this forced width residue the replay checks every denominator used in the ordered width formulas, all six sparse guards, both affine slope divisions, the nonzero relative \(Q/P\) calibration at \(h\), full degrees of \(P_*,Q_*\), the ghost-scale coefficient, \(D_s(\xi)\), \(D'(a)\), \(\Omega'(a)\), and the polynomial inverse of \((X-a)Q_*\) modulo \(D_s\). The two outer clocks reduce to \(x=17,z=24\), and the fitted scale to \(\alpha=3\). The scalar reconstruction gives
\[
 (B_a,\nu,\mu,\tau,f)=(5,2,28,16,11)\pmod{29},
\]
so the denominator-free two-row mark is **17**, nonzero. This contradicts its exact vanishing in the coefficient field. No unknown tableau entries were reduced. All reduced quantities were the algebraic consequences of \(a,d\) and the one paid scale equation, with the relevant degree and inverse explicitly retained.

The core Lean companion proves the two-row identity over a commutative ring and checks that this finite tuple evaluates to 17. The exact width/clock arithmetic and the field-place lift are mathematical and are not claimed as a native full-tableau Lean proof.

The two replay scripts in [the companion directory](erk11-plateau-alias-regular-exit) take the [archived exact regular width factors](erk11-sparse-plateau-alias-eliminant/optional-exact-factor-data/exact-regular-width-factors-d.json) as their positional input. The degree-815 script also accepts `--full` to recompute and match the factor exactly. The [Lean scalar gate](../lean/RKCert/ReviewedNative/ERK11PlateauAliasPaidPairGate.lean) checked on all four targeted versions.
