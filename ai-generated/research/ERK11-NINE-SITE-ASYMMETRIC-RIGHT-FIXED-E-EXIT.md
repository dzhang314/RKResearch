# Asymmetric nine-site ERK11: no right-choosing fixed-half dormant edge

**Scope.** Continue the genuinely distinct nine-site six-pair
chart with four distinct calibrations. Here the **right** front
chooses the opposing half: the actual left extras are \(\{t,s\}\)
and the right extras \(\{h,t\}\). The physical order is
\(c_8=z\) dormant, \(c_9=s,c_{10}=e\).
This excludes that entire edge order and its actual reflection
over characteristic zero. It is not a consequence of reflecting
the earlier [left-choosing half-at-10 edge](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H10-EXIT.md):
reflection also changes the dormant row, and these are two
distinct canonical edge geometries. The half-at-9 edges and
opposite central asymmetric branch are separate.

## 1. Literal two-moment and contact data

Use \(a,h=a/2,d=1-b,e=1-b/2\) as usual. For the actual
genuine shifted pair \(t,s\) let
\(\Delta,\Sigma,\Pi,\Omega\) be the signed Cramer and
unshifted Hankel quantities of the
[opposite-half finite atlas](ERK11-NINE-SITE-OPPOSITE-HALVES-FINITE.md).
Then \(\Delta,\Omega\) are live, \(\Delta(t+s)=\Sigma\),
and \(\Delta ts=\Pi\); set \(Y=\Delta t\).

The left derivative coefficients use the symmetric pair,
and the right coefficients are affine in the chosen \(t\):
\[
 \begin{aligned}
 L_0&=a^2\Delta-a\Sigma+\Pi,& L_1&=-\Pi,\\
 R_0&=(h-d)(Y-d\Delta),& R_1&=-(1-h)(\Delta-Y).
 \end{aligned}
\]
Both rows have been scaled by the independently live
\(\Delta\). The true first Gram contact
\(L_0R_0+T_4(a)L_1R_0+T_4(b)L_0R_1+U_{4,4}L_1R_1=0\)
therefore gives an affine row \(u_0Y+v_0=0\).

Here \(e\) is the **right-only** repeated half and its inner
occurrence is physical 10. The earlier actual right half
calibration has zero reverse primitive. The later right
primitive is also zero by literal strictness through reflected
row eight. Thus the true same-clock repeated row difference
pairs to zero with \(\Phi_L\) (physical 7), giving
\(\langle\Phi_L,D_e^R\rangle_N=0\).
With the known live \(b(1-e)(e-d)\) removed, the width/dormant
gate is
\[
                       G=L_0K^R_0(e)+L_1K^R_1(e)=0 .
\]
This gate depends on the shifted symmetric coefficients, not
on the assignment of \(t,s\) to the two shifted roots.

The actual forward dormant row at physical 8 has literal
zero primitive, so it gives the separate port
\(R_0K_0(z)+R_1K_1(z)=0\) against \(\Phi_R\). This is
a second affine row \(u_1Y+v_1=0\).
Write \(\operatorname{N}(u,v)=v^2+\Sigma uv+\Delta\Pi u^2\);
the shifted free-root equation validates its norm.
The two rows give
\[
 F=\operatorname{N}(u_0,v_0)=0,\qquad
 P=u_0 v_1-u_1 v_0=0,\qquad
 N_{\rm port}=\operatorname{N}(u_1,v_1)=0 .
\]
There is no division by either row's slope. All contact
tests use only the paid mixed grade-five Gram and literal
chronology, not an ordinary reverse order eleven.

## 2. The middle slope and support gate

The literal middle product equation is \(B(z,e)=0\):
\[
                  E z=N,\qquad E=A_0e+B_0,\quad
                  N=-(C_0e+D_0).
\]
If \(E=0\) then both \(E,N=0\); use the original
three-variable polynomials, without a \(z\) substitution.
The rational replay computes the \(b\)-resultant of
\(E,N\) of \(a\)-degree 18, along with the \(z\)-resultants
of \(G\) with \(F,P,N_{\rm port}\), projected further against
\(E\) by \(b\)-resultants. Those three \(a\)-degrees are
266, 277, 484. Their common gcd with the degree-18
projection is 1. All removed factors are actual nonzero
clock or moment guards, never \(E\). Thus the whole affine
dropout is impossible in this geometry.

Now use \(z=N/E\). The crossing labels are \(h,t\); the
actual inner active clocks are \(s,e\). As in the
[dormant support](ERK11-NINE-SITE-ASYMMETRIC-DORMANT-SUPPORT.md)
proof, their masked square-clock product and the
true degree-eight Lagrange weight give
\[
                         I(s,e)(z-h)(z-t)=q_0 z(1-z)(z-a)(z-d),
                         \qquad \Delta q_0=\Omega .
\]
Put \(p=I_2-eI_1,\ q=eI_0-I_1\). The paid affine support
has coefficients
\[
 \begin{aligned}
 u_S&=-(z-h)(p+qz),\\
 v_S&=(z-h)\bigl[pz\Delta+qz\Sigma-q\Pi\bigr]
                  -\Omega z(1-z)(z-a)(z-d).
 \end{aligned}
\]
Use its compatibility \(S=u_0v_S-u_Sv_0=0\) and its
norm \(T=\operatorname{N}(u_S,v_S)=0\).
The support gate is equivalent to the two-crossing equality,
and is counted once.

## 3. Exact width projection and all coefficient fibers

After clearing the live \(E\) and removing only live factors,
the first four normalized width polynomials
\((G,P,F,N_{\rm port})\) have bidegrees in \((b,a)\)
\((13,15),(22,26),(36,44),(34,36)\).
Their exact \(b\)-resultants, anchored at \(G\), have
degrees \(630,1036,954\) in \(a\). The monic common
gcd is of degree 312 and, up to a rational unit, is
\[
                              a^{36}F_{108}F_6^{10}F_9^{12},
\]
with exact irreducible rational factors of the indicated
degrees. The first factor is a forbidden calibration.

Over each of \(\mathbf Q[a]/F_6,\mathbf Q[a]/F_9\), the
exact monic gcd of the affine \(E,N\) is \(b^2\) times
a monic linear polynomial. That linear polynomial divides
\(G\) to order at least 2 and each of \(F,P,N_{\rm port},S,T\)
to order at least 3, checked by exact division. Its root
is impossible since \(E\) is live. The six quotients have
unit gcd at degree-preserving residue places modulo 103.

For \(F_{108}\) use the degree-one \(b\)-subresultant of
\(\Omega\) and the homogenized \(\Delta\).
Its coefficient in \(b\) is a unit in the complete
rational coefficient field. At its exact algebraic root
the homogeneous evaluations of \(\Omega,\Delta,\Pi,
\Delta-\Sigma+\Pi\) are all zero, hence so are
\(\Omega,\Delta,\Sigma,\Pi\). This is independently
forbidden by the true signed moment rank.
The width calibrations and \(E\) are live at that
algebraic point, checked by nonzero reductions at the
degree-48 place modulo 107.

The six normalized width polynomials have this exact
forbidden linear factor. Indeed \(L_0,L_1\) vanish at the
Hankel degeneration. If \(g_1Y+\Delta g_0\) and
\(p_1Y+\Delta p_0\) are the raw first and port rows,
then \(g_0,g_1\) both vanish there, because they are linear
in \(L_0,L_1\). The replay verifies that \(F,P,N_{\rm port}\)
remove exactly one whole \(\Delta\) before affine substitution:
after removal their shapes are respectively
\[
  \Delta g_0^2+\Sigma g_0g_1+\Pi g_1^2,\quad
  g_1p_0-p_1g_0,\quad
  \Delta p_0^2+\Sigma p_0p_1+\Pi p_1^2,
\]
apart from live clock factors. They still vanish.
The gates \(G,S,T\) do not remove any Hankel factor;
\(L_0,L_1,v_S\) all vanish at the same exact field point.
Any other factor removed before substitution is one of
the independently checked width/calibration factors, and
after substitution only powers of \(a,b\) are removed.
Thus all six width polynomials still have the exact linear
factor. At the degree-48 place modulo 107, quotient by it.
The degrees are preserved and the quotient gcd is one.

In each local step a retained leading coefficient makes
the monic quotient finite free over the local coefficient
ring. A unit gcd in its residue field gives a unit spanning
minor, hence unit gcd over the rational coefficient field.
This is the one-place argument of the left-choosing edge,
and excludes every actual characteristic-zero embedding;
it is not a modular assumption about a tableau.
The standalone replay reconstructs the exact global
resultants and all local guard factorizations.

Thus both zero and live slope cases are impossible in the
stated right-choosing fixed-half edge. Actual reflection
covers its physical-10 dormant counterpart, using only the
paid mixed ledger. The large resultant calculation is exact
Python; existing Lean gates check the scalar algebra.

The [standalone exact replay, factor checkpoint, and full independent log](erk11-nine-site-asymmetric-right-fixed-e-exit/) are included.
