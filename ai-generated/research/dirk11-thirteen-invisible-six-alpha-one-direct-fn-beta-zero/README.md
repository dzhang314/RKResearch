# No direct Fn beta-zero carrier for the normalized DIRK11/13 chart

**Result.** Over a characteristic-zero field, the normalized
no-late invisible-six DIRK11/13 live reciprocal chart with
\((\alpha,\beta,\gamma)=(1,0,5)\) and the direct noncontact old \(F_n\)
fit has no candidate. The earlier
[fifth-pivot proof](../dirk11-thirteen-invisible-six-alpha-one-live-fn-beta-zero-fifth-pivot/README.md)
excluded \(D_B=0\) and forced \(d_B=0\), with a separate exact
Jacobi exclusion of its \(r^2=3s\) contact. The present proof
closes the remaining zero fifth diagonal. It does not import any
middle-ghost leader or assume \(V\ne z\) or \(r^2\ne3s\).
The alternate old-fit profiles, other normalization charts, and the
unrestricted real DIRK11 interval **13–14** are not settled here.

## 1. Two literal primitive reads without a middle ghost

Use \(Y=1-c\), the actual reverse prefix \(T,v,u,w,z,V,B\),
and the rooted spaces and matched column from the fifth-pivot
source. Keep the notation \(R=(Y-v)(Y-u)(Y-w)\), \(P=Ym\),
\(P_0=YR\), \(W(f)=b_{\rm wt}f(Y)\), and \(I\) for the
zero-constant primitive. Let \(n\) be a live common scale of the
old inverse fits. Thus hats denote \(n\) times the underlying
polynomial quotient, in particular
\(\widehat M=n(J_4/m\bmod R)\) and
\(\widehat W=n(IP_0/P\bmod R)\). Write
\(U=\widehat M+tR=nU_r\), absorbing its live old scale into \(t\).
The actual reciprocal is \(G_C/b_C=n C J_4(C)/U(C)\) at the five
regular rows.

In the direct noncontact clock chart the old \(F_n\) ratio has
live \(c_2\) and \(c_1+6s\). It is represented by the monic
degree-three equation for \(s(12c_2)\) over the rank-four algebra
of the other ordinary clock \(B\). The base variable is
\(V_{\rm unscaled}\), with the ordinary quotient deflated from
\(J_4(V_{\rm unscaled})J_5(Y)-J_5(V_{\rm unscaled})J_4(Y)\).
The live horizontal change \(L=132J_4(V_{\rm unscaled})\)
scales all reverse clocks and diagonals, and changes the forward
origin endpoint in the reverse coordinate to \(L\). This gives
the rank-12 clock tower used in **proof.py**. In the formulas below
\(V,B,R,J_4,U\) are on the same scaled horizontal coordinate.
The arbitrary live factor on \(m\) is a gauge, with
\((P,G,K_*)\) scaled together and \(U_r\) scaled inversely;
it does not change the zero equations.

Put \(z=p/q\), \(q\ne0\), \(Z=qY-p\) from the old literal
root fit, and use
\[
 \begin{aligned}
 c_q&=P_0(V)U(V),\
 k_q&=Z(V)\big(nVJ_4(V)-P(V)U(V)\big),\
 Q^\#&=c_q ZP+k_qP_0,\
 L^\#&=c_q(Z\widehat\ell-q\widehat\rho)+k_q\widehat W .
 \end{aligned}
\]
The true matched quartic and defect read satisfy
\(Q^\#=c_q q Q_4\), \(L^\#=c_q q n L_{\rm match}\)
with
\(K_*=(V-z)(G_V/b_V-P(V))/P_0(V)\) and
\(L_{\rm match}=(Y-z)\ell-\rho+K_*W_0\).
Here \(c_q\ne0\); if \(V=z\), the numerator \(k_q\) is exactly
zero and no step divides by that clock difference.

The known literal identity is
\(ND=G L_{\rm match}-W(I Q_4)\).
At \(V\), \(ND\) is zero by triangularity and the matched
prefix. At the immediately following \(B\) there is no middle
ghost, all preceding entries of \(D\) vanish, and
\(d_B=0\) makes \((ND)_B=0\) even though \(D_B\ne0\).
Consequently at each \(C\in\{V,B\}\) the genuinely paid
primitive row gives, after scaling,
\[
 H_C(t)=U(C)(I Q^\#)(C)-C J_4(C)L^\#(C)=0.
\]
Each is at most quadratic in \(t\). In particular no condition
on the first ghost after \(B\) is being borrowed from beta one.

## 2. The affine first-clean row and its exact projection

In forward coordinates \(b=L-B\) is the first nonorigin clean
stage. The true grade-five equation for \(A(C\phi)\), with
\(\phi=U_f(c)-g\), where \(U_f(X)=U(L-X)\), is its scalar primitive on clean
rows (the grade-five error is \(g\mathcal P_2\)).
At \(b\) the origin, preceding ghosts, and own diagonal give
zero: the origin is killed by \(C\), the ghosts by \(\phi\),
and \(d_B=0\). Reflecting the primitive therefore gives
\[
 J_b(t)=\int_B^L(L-Y)U(Y)\,dY=j_0+j_1t=0 .
\]
The upper limit and the factor are both \(L\), in the scaled
reverse coordinate. In particular this is literal order payment,
not an additional assumed simplifying stage order.

For \(H_C=h_0+h_1t+h_2t^2\), a common root forces
\[
 \operatorname{pin}(H_C)=j_1^2h_0-j_0j_1h_1+j_0^2h_2=0 .
\]
This follows by multiplying the quadratic at the true \(t\) by
\(j_1^2\) and substituting \(j_1t=-j_0\); it needs **no**
division by \(j_1\). The two actual pins give exact clock norms.
The only removed base content is on
\(V(V-1)J_4 E_+E_-E_{\rm rep}\), known nonzero on the
ordinary pencil, or nonzero rational constants. The exact norm
raw/squarefree degrees are **1116/408** and **1188/432**,
respectively. Their exact squarefree gcd has degree **84**,
with only the three factors below. The independent
projection of \(j_1\) in the lower rank-four clock algebra
has squarefree degree 24 and constant coefficient 123476771;
it is coprime to that gcd. Hence even the affine-leader-loss
chart is covered without being discarded.

As an auxiliary audit, the candidate extra first-two-forward-clean
grade-six diagonal equation has identically zero affine determinant
with \(J_b\) in this ordinary clock tower. It is not used for
closure. The independent conditions here are from the two
actual reverse primitive rows, not two forward rows with an omitted
terminal correction.

## 3. Exact common-factor exclusion

In each exact residue field \(F=\mathbb Q[V]/f\) let \(S\)
be the rank-12 clock algebra. The two pins are checked in the
**same** \(S\). The joint column spaces are multiplied by the
12th power of the indicated live mask.

| Irreducible factor (degree, constant) | Live mask | Exact rank cap | Residue degree at 103 | Joint rank |
|---|---|---:|---:|---:|
| 12, 16227 | old ratio denominator | 11 | 12 | 11 |
| 12, 54123 | lower-clock \(c_2\) | 9 | 4 | 9 |
| 60, −1461941766456 | old inverse scale \(n\) | 11 | 1 | 11 |

**proof.py** verifies the exact singular rank-12 multiplication
norms for the first and third masks modulo their stated factors.
For \(c_2\) the norm is already singular in rank four, hence its
rank is at most three there and at most nine after the monic
rank-three extension. Powers cannot raise rank. Every residue
coefficient denominator and leading coefficient used to reduce
the exact \(F\) basis is a 103-unit. The joint masked ranks
are lower bounds on the exact ranks; the program explicitly checks
all extended-gcd inverses. Thus the exact joint image equals
the image of the live mask power. As it contains that power,
a true field evaluation killing both pins gives a contradiction.
No actual tableau or clock coefficient is reduced.

Run `bash verify.sh` with SymPy and python-flint 0.9. This
regenerates the exact factor lists, gcd and leader check, caps,
and ranks. **audit-beta0.py** independently compares the
forward primitive reflection, both reverse clears, and the pins
at four exact QQ probes, including \(V=z\) and \(r^2=3s\).
The earlier fifth-pivot packet includes the checked native Lean
literal diagonal and Jacobi contact certificates. The present
affine-pin and rank argument is exact written and executable source
arithmetic, not an end-to-end native tableau exclusion.

**Remaining scope.** The old-slope-minus-one proof already covers
direct \(F_1\) and its collapse, and direct \(F_2\) with live
old affine-profile coefficient is impossible by the old fit
census. The argument here now closes direct noncontact \(F_n\)
also for beta zero, complementing the beta-one and beta-two
packets. It does not decide the alternate \(A_0=A_1=0\) old
profiles or the beta-zero finite contacts left out by the older
beta-one/two finite-profile certificate.
