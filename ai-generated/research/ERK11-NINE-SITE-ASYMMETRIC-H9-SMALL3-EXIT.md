# Canonical asymmetric half-at-9: eliminate the bidegree-(3,6) width component

**Scope.** Continue the [finite canonical h-at-9 edge](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H9-PIVOTS.md):
left extras \(\{e,t\}\), right extras \(\{t,s\}\), dormant
physical 8 followed by \(h,s\). This rules out one entire
irreducible width component over characteristic zero, not
all of the remaining regular width tuples.

Write \(R_0,R_1\) for the true right derivative row in the
symmetric shifted coefficients, and use the cubic left
kernels \(K_0,K_1\). The actual dormant contact is
\[
                        G=R_0K_0(z)+R_1K_1(z)=0.
\]
Write \(r_j\) for the two right derivative basis functionals
and \(\rho_j=\langle\ell_a,r_j\rangle_N\). The
[physical-9 weighted half mark](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H9-PIVOTS.md)
is another equation on the same right row:
\[
  R_0 W_0+R_1 W_1=0,\qquad
  W_j=a(C_2-zH)K_j(h)+30h(a-h)(h-z)J_0\rho_j .
\]
These are paid equations at genuine dormant row 8
and genuine active half row 9. No optional intermediate
primitive amplitude is divided away. Their coefficient
determinant
\[
                       M=K_0(z)W_1-K_1(z)W_0=0
\]
is necessary because the right row is nonzero.
At the formal test \(z=h\) the two rows are proportional;
hence \(z-h\) divides \(M\) exactly. This factor,
and any calibration factors removed by the replay, are
known live for an actual tuple. The normalized
\(M\) has tridegrees \((3,5,8)\) in \((z,b,a)\).

There is a second division-free compatibility test.
The right-only label \(s\) at physical 10 has zero
reverse primitive, yielding
\(m_0 L_0+m_1 L_1=0\) for \(m_j=K_j^R(s)\)
by the literal repeated-pair difference. The first
derivative contact and \(G=0\), together with that
left coefficient row, give
\[
 K=m_1K_1(z)-T_4(a)m_0K_1(z)
               -T_4(b)m_1K_0(z)+U_{4,4}(a,b)m_0K_0(z)=0 .
\]
Indeed multiply the first bilinear contact by
\(m_0K_0(z)\), use the two actual homogeneous rows,
and cancel only \(L_1R_1\), a product of live clock
differences. This is the
[scalar kernel compatibility](ERK11-NINE-SITE-ASYMMETRIC-CENTER-ATLAS.md)
and works when individual kernel coefficients vanish.
In \(K\) the exact affine \(s=N/E\) is used and its
live homogeneous factor is cleared.

## Exact component split and exit

Let \(W_{MX}\) denote the \(z\)-resultant of \(M\)
with \(X\), with only independently live factors
removed. The exact width polynomial \(W_{MG}\) has
bidegree \((46,59)\) in \((b,a)\). Its factorization
over \(\mathbf Q\) has one component of each of
bidegrees \((3,6),(9,12),(31,35)\), with multiplicities
\(2,1,1\), respectively. Any actual width belongs to
at least one component, even if some specialized \(z\)
degrees drop.

Take the unique bidegree-\((3,6)\) factor \(C_3\).
The exact \(b\)-resultants of \(C_3\) with the
necessary width polynomials \(W_{MQ},W_{MF},W_{MS},W_{MK}\)
have \(a\)-degrees \(516,660,699,702\).
The running common gcd degrees are \(516,99,87,63\).
Thus it is *not* sufficient to test only those
projections sharing the \(M\) anchor. The independent
[original dormant anchor](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H9-FINITE.md)
gives \(W_{GQ},W_{GF}\). Their \(b\)-resultants with
\(C_3\) have exact \(a\)-degrees \(660,780\);
the first of these already makes the full common
gcd a unit. Consequently no finite width can lie on
\(C_3=0\).

The receipt is exact rational arithmetic, including
the factorization and all degree-drop projections.
The two other width components are not excluded by
this calculation. Existing Lean gates cover the
cleared scalar compatibility, not the full resultant.

The [standalone exact source and independent replay log](erk11-nine-site-asymmetric-h9-small3-exit/) are included.
