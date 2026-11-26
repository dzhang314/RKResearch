# The nonzero-paid-top extra-stage rectangle has a centered rank-one defect

Mathematical proof, not kernel-checked. Let \(A=\gamma I+B\) be a
common-diagonal triangular RK tableau over a characteristic-zero field,
\(B\) strictly lower triangular, with \(s=p+1\) physical stages and \(p\ge5\),
passing rooted order through \(p\). Assume the physical full-chain
product \(L=b_s\prod_{i=2}^s B_{i,i-1}\ne0\), and separately the
paid \(B_0=\lambda_{p-1}\ne0\), where \(\lambda_j=b^TB^je\) for
\(j\le p-1\). No value is assigned to the unpaid full product.
Let \(n=p-2=s-3,\ x_i=c_i-\gamma,\ g_i=x_{i+1}-x_i\), with actual
clocks \(c=Ae\).

The central identity is that the three-hole rectangle, after subtracting
a product of two paid first-moment deficits, is exactly a rank-one
product of centered actual cut weights. Its rank envelope is a
homogeneous pairing in dimension three, not the earlier zero-top
constant rank-two ansatz. In the nondegenerate scalar chart it gives
a joint arithmetic prefix through \(s-4\), or a joint prefix and
affine tail with three intervening clocks. In general it still
states precisely what degenerates.

## 1. Actual path algebra, including the remaining cubic term

An omitted set of physical stages determines the corresponding
strict path, with weight \(w_H\) the product of its actual strict
entries times its last output weight. After dividing by \(L\),
the weights multiply over separated contiguous omitted intervals,
including leading and trailing ones. This follows by replacing
the disjoint adjacent edge blocks, possibly sharing a retained
vertex. Individual replacement weights may vanish.

Let \(\omega_k=w_{\{k\}}\), \(\Omega_{ij}=w_{\{i,j\}}\), and put
\[
 U_i=\sum_{k\le i}\omega_k,\quad W_i=\sum_{k>i}\omega_k=B_0-U_i,
 \quad \sigma_i=g_i U_i/L,\quad \tau_i=g_i W_i/L .
\]
In particular \(\sigma_i+\tau_i=B_0 g_i/L\).
The two-hole total is \(M=\lambda_{p-2}\).
Let \(G^-_k\) be the two-hole weight with both holes at
most \(k\), and \(G^+_k\) that with both holes greater than \(k\).
In the two-hole band the offset-one weight at occupied slot \(k\)
is \(U_k W_{k+1}/L\). Indeed it has one hole at or before \(k\)
and one strictly after \(k+1\), so they are separated.

Write \(K=\lambda_{p-3},R=\lambda_{p-4},S=\lambda_{p-5}\).
The paid shifted first clock at two-hole slot \(k\) is
\[
     A'_k=B_0+(k-1)\kappa,\qquad \kappa=B_0+2\gamma M+\gamma^2 K.
\]
This is the formal clock-word identity: \(B,C\) model
\(T=J-\gamma I,X\), where \(J\) is integration from zero and
\(X\) multiplies by the variable, with output \(\ell=\int_0^1\).
The factor \(X\) adjoins a leaf at the current root,
and \(A\) adds a unary root in the exact stage model
\((|t|/\rho(t))x^{|t|-1}\). A word of \(d\) strict hops and
\(j\) marks pays \(d+j+1\) tree vertices.
There are \(p-2\) strict hops in the two-hole band, so
one mark is paid. Subtracting its extreme possible clock
values gives
\[
 \begin{aligned}
 (g_i+g_{i+1})G^-_{i+1}
      &=A'_i-Mx_i-\sigma_i W_{i+1},\\
 (g_{j+1}+g_{j+2})G^+_{j+1}
      &=Mx_{j+3}-A'_{j+1}-\tau_{j+2}U_{j+1}.
 \end{aligned}                                               \tag{1}
\]
These identities do not require distinct clocks.

In the three-hole band let \(Z_i\) be the shifted clock at
occupied position \(i\) and consider
\(R_{ij}=\langle(Z_i-x_i)(Z_j-x_{j+3})\rangle\) for
\(1\le i\le j\le n\). This uses \(p-3\) strict hops and
two marks, so it too is paid through \(p\).
The only potentially surviving offset pairs are
\((1,1),(1,2),(2,2)\). For hole indices \(r_1<r_2<r_3\),
their weights are respectively
\[
   U_iG^+_{j+1}/L,\qquad
   U_i(U_{j+1}-U_{i+1})W_{j+2}/L^2,\qquad
   G^-_{i+1}W_{j+2}/L .
\]
Indeed the first case has \(r_1\le i,\ r_2>j+1\); the
second has \(r_1\le i,\ i+2\le r_2\le j+1,\ r_3>j+2\);
the third has \(r_2\le i+1,\ r_3>j+2\).
These conditions come from the thresholds \(r_h-(h-1)\)
for passing the \(h\)-th hole. The indicated isolated
holes are always separated, and no factorization of an
internal adjacent hole pair was used.

The clock factors in this order are
\(-g_i(g_{j+1}+g_{j+2})\), \(-g_i g_{j+2}\),
and \(-(g_i+g_{i+1})g_{j+2}\). Substitute (1).
The cubic seed correction combines into
\(\sigma_i\tau_{j+2}(U_{i+1}+W_{i+1})=
B_0\sigma_i\tau_{j+2}\). Thus exactly
\[
 R_{ij}=\sigma_i(A'_{j+1}-Mx_{j+3})
        -\tau_{j+2}(A'_i-Mx_i)+B_0\sigma_i\tau_{j+2}.
 \tag{2}
\]
In particular the true nonzero-top centered residual is
\[
 \boxed{\quad
 R_{ij}-\frac{(A'_i-Mx_i)(A'_{j+1}-Mx_{j+3})}{B_0}
   =B_0\left(\sigma_i-\frac{A'_i-Mx_i}{B_0}\right)
          \left(\tau_{j+2}+
                       \frac{A'_{j+1}-Mx_{j+3}}{B_0}\right).
 \quad}                                                     \tag{3}
\]
Equation (2) is valid also when \(B_0=0\) but the completion
(3) is not. This is the structural distinction between
the two charts. Division in (3) is only by the nonzero
paid scalar, never by a clock gap or unpaid scalar formula.

## 2. Paid scalar envelope

Set
\[
 \eta=M+2\gamma K+\gamma^2 R,\quad
 V_3=B_0+3\gamma M+3\gamma^2K+\gamma^3R,\quad
 V_4=B_0+4\gamma M+6\gamma^2K+4\gamma^3R+\gamma^4S.
\]
For \(a=i-1,b=j-1\), the three-hole shifted one marks
are \(M+a\eta,M+b\eta\); their shifted product is
\(B_0+(b+1)\kappa+a(2V_3+\kappa-V_4)+abV_4\).
Indeed the unshifted two-mark formal polynomial is
\(2J^2T^{p-3}+(b+3a)J^3T^{p-4}+a(b-1)J^4T^{p-5}\)
applied to 1, from the commutator \([X,J]=J^2\).
Shifting both clock factors gives the displayed formula
and uses no formal tall index beyond \(p-1\).

Define
\[
  D=B_0 K-M^2,\quad E=M\kappa-B_0\eta,\quad
  F=B_0V_4-\kappa^2,\quad H=M\kappa,\quad
  G=B_0(2V_3-V_4)-\kappa^2,\quad \Delta=DF-E^2 .
\]
The paid evaluation of
\(B_0 R_{ij}-(A'_i-Mx_i)(A'_{j+1}-Mx_{j+3})\)
is
\[
         (D x_i+aE)x_{j+3}+(E x_i+aF)b+H x_i+aG.
\]
This is obtained by expanding the two one-mark subtractions
and canceling \(B_0[B_0+(b+1)\kappa]\).
For \(i\ge2\) let
\[
 u_i=x_i/(i-1),\quad
 z_i=\left(\sigma_i-(A'_i-Mx_i)/B_0\right)/(i-1),\quad
 q_j=\tau_{j+2}+(A'_{j+1}-Mx_{j+3})/B_0 .
\]
It follows from (3) that for \(2\le i\le j\le n\)
\[
      u_i Y_j+Z_j=B_0^2 z_i q_j,\qquad
      Y_j=D x_{j+3}+E(j-1)+H,\quad
      Z_j=E x_{j+3}+F(j-1)+G .                              \tag{4}
\]
This is a homogeneous triangular pairing between
source vectors \((u_i,1,z_i)\) and target vectors
\((Y_j,Z_j,-B_0^2 q_j)\).
It is not the earlier canceled-top equality of a
two-coordinate pairing to a fixed nonzero cubic.
For example, even without nondegeneracy, if three
sources span dimension three before a given target,
that and all later target vectors must vanish.

## 3. Literal clock and weight runs when Delta is nonzero

Suppose \(\Delta\ne0\). If all source pairs \((u_i,z_i)\)
coincide for \(2\le i\le n-1\), the literal prefix through
\(n-1=s-4\) is arithmetic with step \(x_2=B_{21}\ne0\).
Moreover \(\sigma_i=1+(i-1)(\kappa/B_0-Mu_i/B_0+z_i)\)
is affine on that prefix; at index 1 the same formula
holds because \(\omega_1=L/B_{21}\) and \(\sigma_1=1\).
On adjacent gaps wholly inside the prefix, \(g_i\)
is the nonzero step, so \(U_i/L=\sigma_i/g_i\) is
affine and the normalized singleton weights are constant
on all strictly interior stages of the prefix.

Otherwise let \(i_0\le n-1\) be the first different pair,
so the same joint arithmetic prefix reaches \(i_0-1\).
For all \(j\ge i_0\) there are the two rows of (4) at
\(i=2,i_0\), and there are at least two such targets
since \(j\) includes \(n\). If the two \(u\)'s are the
same and the \(z\)'s differ, \(q_j=0\).
Then the affine equation \(uY_j+Z_j=0\) has nonzero
coefficient of \(x_{j+3}\): if it were zero, its
coefficient of \(j-1\) would be nonzero by \(\Delta\ne0\),
so at most one target could satisfy it.
If the two \(u\)'s differ, write their line as
\(z=m u+b_0\). Equation (4) gives
\(Y_j=B_0^2 m q_j,\ Z_j=B_0^2 b_0 q_j\).
The pair \((m,b_0)\) is not zero, because otherwise
the nonsingular affine map \((x,j-1)\mapsto(Y,Z)\)
would permit at most one target. Eliminating \(q_j\)
gives \(b_0Y_j-mZ_j=0\); again its coefficient of
\(x_{j+3}\) cannot vanish, or the coefficient of
\(j-1\) would be nonzero. Thus in either case
\(x_{j+3}\) is affine in \(j\) and \(q_j\) is affine
as well.

This is a literal affine tail from physical stage
\(i_0+3\) through \(s\), with no restriction on the
three middle clocks \(i_0,i_0+1,i_0+2\).
If the tail step is nonzero, \(\tau_{j+2}\) is affine
by definition of \(q_j\), and then so is \(\sigma_{j+2}\)
on internal tail gaps since
\(\sigma_i+\tau_i=B_0 g_i/L\) with constant \(g_i\).
Thus the normalized singleton weights are constant
strictly inside this run as well. There is no assumption
that the two steps agree, and no assertion of the
canceled-chart terminal clock \(1-\gamma\) in this branch.

## 4. A constant-clock run cannot be long

Independently of the determinant, a literal run of at
least five equal clocks is impossible at \(s=p+1\).
On the two-hole band place a marked link in a constant
window of length four. All possible endpoints of the
link stay in that window, and its difference is zero.
The paid \([C,B]\) word would give
\(\kappa=\ell(J^2T^{p-3}1)=0\).
On the three-hole band, one squared difference link
in a length-five constant window similarly gives
\(2V_3=2\ell(J^3T^{p-4}1)=0\).
For \(\gamma=0\) already \(\kappa=B_0\ne0\).
For \(\gamma\ne0\) the two identities contradict
\[
 V_3=\kappa-\frac{\gamma}{p-3}\frac{d\kappa}{d\gamma},
 \qquad
 \kappa=\frac{(p-3)!}{p!}(-\gamma)^{p-3}
                           L_{p-3}^{(3)}(1/\gamma).
\]
The first follows by differentiation of \(J^2T^{p-3}\).
The second follows by expanding \(T=J-\gamma I\).
The associated Laguerre polynomial in this formula has no
multiple nonzero root, over any characteristic-zero field:
its coefficient equation
\(xP''+(4-x)P'+(p-3)P=0\), differentiated successively,
would make all derivatives vanish at such a root, since
that root is nonzero. The polynomial is not zero.
Thus a constant run in a split chart has at most four
clocks (at most three if \(\gamma=0\)).

This local argument and (3)--(4) do not imply that the
degenerate scalar chart must have either affine shape.
In particular, when \(\Delta=0\) the eliminated affine
equation may vanish identically; one must keep the exact
rank constraint rather than infer nondegenerate clock
rigidity. The companion uses precisely the nondegenerate
shape, not a claim about that unresolved chart.
