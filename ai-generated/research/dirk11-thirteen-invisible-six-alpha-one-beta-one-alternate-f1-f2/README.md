# Alternate F1 and F2 are impossible in live beta-one DIRK11/13

**Result.** For normalized no-late invisible-six DIRK11/13 over
a characteristic-zero field with cubic carrier, live reciprocal
multiplier, and \((\alpha,\beta,\gamma)=(1,1,4)\), neither
alternate old \(F_1\) nor alternate old \(F_2\) is possible.
These are the nonmonomial old fits with the generic noncontact
guards and the old affine pivot \(A_1=0\).
The proof covers nonzero fifth diagonal and in fact assumes
**neither** a value of \(d_B\) or \(d_V\), nor \(V\ne z\).
No unrestricted stage bound follows; real DIRK11 remains **13–14**.

## 1. Exact old ingress is independent of the middle count

Use the true [old-profile census](../dirk11-thirteen-invisible-six-early-profile-census/README.md)
and [old slope bridge](../dirk11-thirteen-invisible-six-alpha-one-slope-minus-one-bridge/README.md).
The earlier alternate [F1](../dirk11-thirteen-invisible-six-alpha-one-beta-zero-alternate-f1/README.md)
and [F2](../dirk11-thirteen-invisible-six-alpha-one-beta-zero-alternate-f2/README.md)
factor calculations begin from the actual \(IP=\ell P+\delta P_0\),
the old adjugate fit and \(A_1=A_0=0\). Their coefficient
identities and closed Jacobi projections use no later diagonal,
no forward primitive at \(B\), and no middle-ghost count.

For \(F_1\) the direct affinity root would give \(\ell_1=-1\);
for \(F_2\) the direct affinity root would make \(m\mid R\).
The latter is impossible by the actual live old \(m\) values.
The possible last factor in the alternate \(F_2\) coefficient
remainder also gives \(\ell_1=-1\). For beta one the correct
slope exclusion is the [first-gap bridge](../dirk11-thirteen-invisible-six-alpha-one-slope-minus-one-bridge/README.md)
combined with the
[beta-one/two direct-ratio slope proof](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-minus-one/README.md),
not the beta-zero five-prefix proof. Thus the same finite old
models apply, including their exact guards:
* \(F_1\): degree-48 ordinary field, both exact linear lifts
  (\(B\) and \(a=c_0/s\)), and the exact transposition \(B(B(V))=V\).
* \(F_2\): degree-24 singled old clock field and exact linear
  \(s\)-lift, then a monic complementary quadratic retaining
  both assignments of the two physical \(V,B\) labels.

No beta-zero pin is evaluated here. **replay.py** verifies the
hash of each corresponding exact old model and truncates before
its carrier rows. It uses its checked exact field and selected
local residue reconstruction only.

## 2. Three actual beta-one rows in one carrier variable

Use reverse \(Y=1-c\), literal \(N=A^{\mathsf T}\) in reverse
order, \(R=(Y-v)(Y-u)(Y-w)\), \(P=Ym\), \(P_0=YR\),
\(P_5=(Y-V)P_0\). The actual reverse prefix now contains
\(T,v,u,w,z,V,x,B\) with exactly one distinct middle ghost
\(x\). In particular before the second nonorigin forward
ordinary \(a=1-V\), there are the four initial forward
ghosts, \(b=1-B\), and \(x\). The live reciprocal is
\(G/b_{\rm wt}=YJ_4/U_r\). In a common old adjugate
scale \(n\ne0\), use \(U=nU_r=\widehat M+tR\), with
\(\widehat M=n(J_4/m\bmod R)\). All polynomials in the
replay use unscaled clock units. Below \(j=J_4(V)\),
\(h=Vj\), \(u_V=U(V)\), and the old ghost is \(z=p/q\)
with live \(q\).

**The quartic and marked cubic at \(V\).**
Write
\[
 L_0=IP_0/Y,\quad L_1=I(YP_0)/Y,\quad
 C_V=D_4(V)+tL_0(V),\quad
 D_4=(L_0\widehat M-\widehat W_0J_4)/R.
\]
The only weighted nonzero quartic donor through \(V\)
is its own diagonal, so \(d_V u_V=C_V\). The actual
marked-cubic adjacent read is, for the literal tap
\(T=N_{Vz}G_z/b_V\) and \(k=G_V/b_V\),
\[
 T=\ell(V)k-IP(V)+d_V(P(V)-k),\qquad
 (z-V)T=I^2P(V)-\rho(V)k .
\]
The marked identity follows from \(P_1=YP-\kappa P_0\)
and the true reverse
\(IP_1=YIP-I^2P-\kappa IP_0\); it is the paid identity
of the [live old-profile calculus](../dirk11-thirteen-invisible-six-alpha-one-live-cubic/README.md#1-common-old-fit-and-adjacent-marked-quadratic).
All three reads are through \(V\), not through \(B\).
Using \(u_V k=nh\) gives the undivided quadratic
\[
 A(t)=(p-qV)\{(\widehat\ell(V)h-IP(V)u_V)u_V+
                        C_V(P(V)u_V-nh)\}
        -q(I^2P(V)u_V-\widehat\rho(V)h)u_V=0 .
\]
There is no division by \(z-V\), by a diagonal, or
by the leading coefficient of this quadratic.

**The forward grade-six corrected primitive.**
Let \(U_f(X)=U(1-X)\), \(\phi=U_f(c)-g\) in its
common gauge, \(H=XJ_4(X)\), \(F_b=I_X[X(X-b)U_f]\),
and \(K_b=H(b)F_b-F_b(b)H\).
Before all five forward ghosts preceding \(a\), the
actual input \(C(C-b)\phi\) vanishes on every preceding
and own donor: it kills \(O\) and \(b\) by clock factors
and all ghosts by \(\phi\). This is true even with
nonzero \(d_B\). The actual grade-six error has the
terminal-profile direction as in the
[forward mask proof](../dirk11-thirteen-invisible-six-prefix/README.md).
Its coefficient is fixed by the same zero read at \(b\);
using live \(H(b)\) is exactly why the corrected primitive
is \(K_b\), not bare \(F_b\).
The remaining grade-six ghost polynomial multiplies \(U_f\);
\(K_b+U_f Q_3\) is the hull of those five ghosts times an
affine polynomial, possibly zero.

The six-ghost hull is proportional, modulo \(U_f\), to the
six nonterminal ordinary hull by the actual \(E_6\) shape.
The proportionality factor is live because \(U_f\) is
nonconstant and does not vanish at any of those six clean
roots. The only omitted ghost from the preceding five
is \(z\) in reverse. Reflect and cancel the exact
\((Y-1)(Y-B)\) factors, units modulo the live carrier.
With \(D_R=(Y-V)R\), the resulting polynomial
\[
 P_6=(qY-p)K_b(1-Y)/[(Y-1)(Y-B)]
\]
lies in \(\operatorname{span}(D_R,YD_R)\) modulo \(U\).
Since the actual \(U\) is cubic, the coefficient
relation uses \(U,YU,Y^2U,D_R,YD_R,P_6\) in degrees
at most five. Reduce modulo the monic \(D_R\), replacing
\(YU,Y^2U\) by the two equivalent columns
\((Y-V)\widehat M,Y(Y-V)\widehat M\).
The resulting four-column determinant \(E_6\) vanishes.
Only \(U,P_6\) vary with \(t\), so \(\deg_t E_6\le2\).
No linear independence from \(A(t)\) is asserted.

**Beta-one first-middle root and forward grade-five mark.**
The true weighted quintic \(P_5\) has zero weighted
inputs through \(x\). Its ordinary fit gives an exact
cubic error polynomial with roots \(z,x\). Define
\[
 \begin{aligned}
 D_5&=(L_1\widehat M-\widehat Q_0J_4)/R,\
 B_5^\#&=j(\widehat Q_0-V\widehat W_0)+
                (D_5(V)+tL_1(V)-VC_V)R,\
 Q_5^\#&=q^3[U(z)B_5^\#-B_5^\#(z)U].
 \end{aligned}
\]
Here \(\widehat Q_0=n(L_1/m\bmod R)\). This is a live
common scale of the actual weighted primitive error's
\(G\) polynomial (the input \(P_5\) is quintic).
The crossed old fit and the true weighted zero sample
at \(V\) give the formula, as in the
[beta-one derivation](../dirk11-thirteen-invisible-six-alpha-one-live-cubic/README.md#3-undivided-reconstruction-and-separate-middle-tests).
The two \(t^2\) terms cancel since their columns are
multiples of the same \(R\), so \(Q_5^\#\) is affine
in \(t\), with no hypothesis on its degree in \(Y\)
other than at most three. Clearing the divided difference
at \(z=p/q\) gives coefficients \(d_0,d_1,d_2\)
of a polynomial vanishing at the distinct actual \(x\).

Now use only the **four** initial forward ghosts, not
the ordinary first clean row: the genuine grade-five
\(A(C\phi)=J+g Q_2\), \(J=I_X[XU_f]\), vanishes
at those four inclusive prefixes. The resulting ghost
quartic hull times an affine polynomial, multiplied by
the missing two factors \(Y-z,Y-x\), is proportional
to the full ordinary hull modulo \(U\) up to an affine
factor. Cancel the exact live \(Y-1\) factor. With
\(D_R'=(Y-B)D_R\) this gives
\[
 (qY-p)(Y-x)J(1-Y)/(Y-1)
       \in\operatorname{span}(D_R',YD_R') \pmod U.
\]
Use the cubic-multiple columns \(U,YU,Y^2U,Y^3U\)
and reduce modulo monic \(D_R'\), replacing the last
two by \((Y-V)(Y-B)\widehat M\) and its \(Y\)-multiple.
The coefficient determinant is \(g_0-xg_1=0\),
each \(g_i\) of \(t\)-degree at most three.
Thus the exact homogeneous gate
\[
          B_1(t)= d_0g_1^2+d_1g_0g_1+d_2g_0^2=0
\]
has degree at most seven. Neither \(g_1\) nor a
quintic leader is inverted. Even an identically zero
formal column is retained in the degree-bounded test.

## 3. Fixed-cap exact exclusion

In each exact finite old algebra over its number field, use
the single polynomial variable \(t\) and cap **9**.
Multiply \(A,E_6,B_1\) by every basis element and by
\(t^j\) with \(j\le9-d\) for fixed bounds **2,2,7**.
The caps do not change when a residue or formal column
loses degree. Full rank in \(\mathcal P_9\) proves that
1 is an exact linear combination, contradicting any
actual evaluation killing the three paid rows.

| Alternate old chart | Exact base degree / rank above it | Selected residue at 103 | A and E6 | All three / required |
|---|---:|---|---:|---:|
| \(F_1\) | 48 / 1 | \(V+25\) | 8 | 10 / 10 |
| \(F_2\) | 24 / 2 | \(X+21\) | 16 | 20 / 20 |

Each checked residue minor lifts to a nonzero exact minor
using the same verified old coefficient denominators.
Neither unknown actual \(t\), its clocks, nor the tableau
is reduced or assumed integral. In particular this is not
a cofactor division at a specialized t-leader and requires
no separate nonzero \(d_V\), \(d_B\), \(V-z\), or \(B-x\)
guard. The actual cubic carrier and its live clean/ghost
values are stipulated by the normalized scope and used in
the degree and root-factor arguments.

Replay with `bash verify.sh` using SymPy and python-flint 0.9;
an explicit path to the research root may be given as the
first argument. The local Lean module checks the homogeneous
divided difference and the no-leader clock pin on Lean 4.36.0
with standard axioms. This does not claim an end-to-end
native tableau theorem.
