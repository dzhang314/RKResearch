# The direct Fn beta-one carrier chart is empty

**Result.** A characteristic-zero field has no thirteen-stage order-eleven
DIRK candidate in the remaining normalized no-late invisible-six,
live reciprocal, \(\alpha=\beta=1\), direct noncontact \(F_n\) chart with
nonzero fourth and fifth ordinary diagonals. Together with the earlier
[zero-fourth](../dirk11-thirteen-invisible-six-alpha-one-live-zero-fourth/README.md)
and [zero-fifth](../dirk11-thirteen-invisible-six-alpha-one-live-fn-zero-fifth/README.md)
exclusions, this closes the direct noncontact \(F_n\) case for \(\beta=1\).
It does not close alternate old profiles, \(\beta=0\), arbitrary
thirteen-stage tableaux, or alter the unrestricted real interval **13–14**.
No ordering of the field is used in the argument below.

## 1. Actual equations, not a freely chosen scalar ansatz

In the reverse coordinate \(Y=1-c\), the literal prefix is
\(T,v,u,w,z,V,x,B,y\). The actual normalized hypotheses and true
rooted marked identities are those of
[gap diagonals](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md),
[carrier slices](../dirk11-thirteen-invisible-six-alpha-one-live-fn-carrier-slices/README.md),
and [fifth compensator](../dirk11-thirteen-invisible-six-alpha-one-live-fn-fifth-compensator/README.md).
Use \(R=(Y-v)(Y-u)(Y-w)\), \(P_0=YR\), \(P=Ym\),
\(P_5=(Y-V)P_0\), and let \(I\) denote zero-constant primitive.
The old fits are
\(\ell=IP/P\bmod R,\ \rho=I^2P/P\bmod R,\ W_0=IP_0/P\bmod R\),
with a live common inverse denominator \(n\) and
\(\widehat M=n(J_4/m\bmod R)\).
In homogeneous coordinates \(q\ne0,\ p=qz,\ Z=qY-p,\ E=qK_*\), define
\[
 Q=ZP+EP_0,\qquad L^\#=Z\widehat\ell-q\widehat\rho+E\widehat W_0 .
\]
Thus \(Q=qQ_4\) and \(L^\#=nq\lambda(Y-z)(Y-x)\).
The exact paid adjacent primitive is
\(IQ_4=\lambda(Y-x)Q_4+\eta P_5\).
With \(a=[Y^2]L^\#\), \(x_n=-q[Y]L^\#-pa\), \(x_d=qa\), and
\(\eta_N=(nq/5-a)[Y^4]Q\), the coefficient of \(Y\) gives
\[
 A(E)=q\eta_N Vc_0+x_n[Y]Q=0,\qquad c_0=R(0).
\]
Its \(E^2\) coefficient \(a_2\) is live by the
[adjacent-separable proof](../dirk11-thirteen-invisible-six-alpha-one-live-fn-adjacent-separable/README.md).
The selected tableau ingress uses the same live first-middle conditions
\(x_d\ne0, x\ne z, W_0(x)\ne0\) as the earlier first-middle/contact
and adjacent packets. No additional exclusion of a ghost/clean collision is
assumed.

We use three further actual rows:
1. The true four-ordinary quintic read yields \(Q_5(x)=Q_5(z)=0\);
   the exact crossed fit, synthetic division at \(z\), and evaluation at
   \(x=x_n/x_d\) give \(Q_{\rm pin}(E)=0\) of degree at most three.
2. With the actual \(d_x=0\), the first-middle \(P_0\) commutator gives
   \[
     (x-V-d_V)W_0(x)-\frac{d_V^2 V}{k}
       \left(R(x)-R(z)\frac{U_r(x)}{U_r(z)}\right)=0,
     \qquad k=G_V/b_V.
   \]
   This is the true commutator proved in the
   [late-affine packet](../dirk11-thirteen-invisible-six-alpha-one-live-fn-late-affine/README.md).
   In **joint.py**, \(D_{\rm num}/D_{\rm den}=d_V\),
   \(S=nR(V)Q(V)U_r\) and \(S_z=q^3 S(z)\).
   The old cross \(CM=q^3 n[U_r(z)R-R(z)U_r]\) divided by
   \(Y-z\) (with factor \(q^2\)) implements the second term.
   The first uses \(W_1=q\widehat W_0/(Y-z)\).
   Indeed \(D_{\rm den}U_r(z)/S(z)=V/k\), so their common
   cleared quadratic evaluated at \((x_n,x_d)\) is exactly the
   necessary row \({\rm Mid}(E)=0\), degree at most four.
3. The fifth ordinary diagonal satisfies
   \(d_B\nu=(B-x)(\nu+\omega_B)\).
   Using the independently checked \(B_z=(D_{\rm pol}/P_5)(B)\),
   \(b=L-B\), \(S_B=S(B)\), \(J_b=\int_B^L(L-Y)S(Y)\,dY\),
   \(b_x=Bx_d-x_n\), \(\omega_N=b_xB_z\),
   \(\omega_D=x_dqS_B\), \(\eta_D=nq^2\),
   \[
      \nu_N=\eta_N\omega_D-q(nq+a)\omega_N,
      \qquad
      B_g=J_b x_d\nu_N-bS_B b_x(\nu_N+\eta_D\omega_N)=0 .
   \]
   These are exactly the scales of the
   [fifth-compensator derivation](../dirk11-thirteen-invisible-six-alpha-one-live-fn-fifth-compensator/README.md):
   \(\nu=\nu_N/(\eta_D\omega_D)\), \(d_B=J_b/(bS_B)\).
   The polynomial row has degree at most six. No division by \(\nu_N\)
   or by a derivative of the quintic is used here.

Neither the rational formula for \(y\) nor its extra late commutator is
needed: the three rows above suffice jointly. Their prior literal order
payments are used without adding any higher-stage-order assumption.

The horizontal chart scale \(L=132J_4(V_{\rm unscaled})\) is live.
Replacing \(Y\) by \(LY\) scales ordinary nodes and diagonals by \(L\),
uses monic \(R\) in the new coordinate, scales \(J_4\) by \(L^4\), and
changes the endpoint in the reflected primitive to \(L\). In particular,
\(I'[a f(Y'/L)]=aL(If)(Y'/L)\); this is why the fifth ordinary
integral has upper limit and linear factor \(L\). Multiplying the old
quadratic \(m\) by a live constant amounts to the simultaneous gauge
\((P,G,K_*)\mapsto a(P,G,K_*)\), \(U_r\mapsto U_r/a\).
Then \(\ell,\rho,x,\lambda\) are unchanged, \(W_0\mapsto W_0/a\),
\(Q_4,\eta,\omega_B,\nu\) scale by \(a\), and the three zero rows
remain necessary. This justifies the cleared numerical \(m\) scale.

## 2. A compact exact seed in the first middle clock

The base variable is \(V_{\rm unscaled}\). Its ordinary pencil fixes
the monic quotient for the other four regular clocks by dividing
\(J_4(V_{\rm unscaled})J_5(Y)-J_5(V_{\rm unscaled})J_4(Y)\) at
\(Y=V_{\rm unscaled}\), then changing to horizontal units \(L\).
Adjoin \(B\) in this rank-four algebra. Adjoin the direct \(F_n\)
parameter \(s(12c_2)\) by its monic rank-three cubic. This gives the
rank-12 clock algebra \(S\).

The seed uses a compact affine representation of \(E\) in \(X=x\).
Put \(C=Z\widehat\ell-q\widehat\rho\), \(w_i=[Y^i]\widehat W_0\),
\(c_i'=[Y^i]C\). Since \(C(z)=\widehat W_0(z)=0\), define
\[
 N(X)=-q c_1'-p c_2'-q c_2'X,\qquad
 D(X)=q w_1+p w_2+q w_2X.
\]
At the actual \(x\ne z\), \(D(x)=q\widehat W_0(x)/(x-z)\ne0\),
and \(L^\#(x)=0\) gives \(E=N(x)/D(x)\). No division by either leading
coefficient of these two affine polynomials is made. Write
\(A_*=c_2'D+Nw_2\), constant in \(X\), and
\(Q_X=D ZP+N P_0\).
Then the compact quadratic
\[
 \widetilde A(X)=(nqD/5-A_*)[Y^4]Q_X\,V c_0
                          +X A_*[Y]Q_X
\]
evaluates at \(x\) to \(D(x)^2 A(E)/q\).

For a compact cubic from the same true quintic, set
\[
 C_z(f,g)=q^2\frac{f(z)g(Y)-g(z)f(Y)}{Y-z}.
\]
For degree-at-most-three inputs this is a polynomial in the input and
clock coefficients. The term from the pair \(i<j\) of coefficients is
\((f_i g_j-f_jg_i)\sum_{k=0}^{j-i-1}p^{i+k}q^{2-i-k}Y^{j-1-k}\),
with nonnegative exponents. Put \(R_v=R(V)\),
\(D_0=(I(YP_0)-V I(P_0))/Y\),
\(\widehat D_0=n(D_0/m\bmod R)\),
\(S_M=R_v\widehat M-\widehat M(V)R\),
\(S_D=R_v\widehat D_0-\widehat D_0(V)R\).
The exterior-square identity
\[
 ({\rm adj}(A)u)\times({\rm adj}(A)v)
   =\det(A) A^{\mathsf T}(u\times v)
\]
for the old three-dimensional multiplication matrix \(A\) gives
\(\Delta=C_z(S_M,S_D)/(nR_v)\) without a rational-function
coefficient divide. Indeed, writing \(T_i=R_vY^i-V^iR\),
\[
 \frac{C_z(T_i,T_j)}{R_v}
   =R_v C_z(Y^i,Y^j)-V^j C_z(Y^i,R)+V^i C_z(Y^j,R).
\]
The crossed fit, after the common-\(Q(V)\) cancellation,
is thus represented by the cubic
\[
 \left[ Q_X(V)\Delta+(qV-p)VD
      \big(D_0(V)C_z(\widehat M,R)-J_4(V)C_z(\widehat D_0,R)\big)
 \right]_{Y=X}.
\]
It is \(D(x)/(q nR_v(x-z))\) times the previous crossed
quintic numerator at \(x\). Every removed scale at a candidate
is live. The fully exact independent QQ probes in **audit-x.py**
verify the old exterior-square, primitive coefficient, and compact
quintic identities in four distinct horizontal and carrier scales.

Take the degree-two/degree-three homogeneous resultant in \(X\) of
these two polynomials, then the two relative clock norms.
The exact resultant formula uses the quadratic power sums, or
equivalently the padded Sylvester resultant. It stays necessary for a
shared finite root when either leader drops. The clock norms are
multiplication determinants in the monic tower and stay necessary on
every vertical fiber. Common base coefficient content is removed only
when supported on \(V(V-1)J_4 E_+E_-E_{\mathrm{rep}}\), all live
by the established ordinary-chart guards; nonzero rational constants
only change normalization.

**verify-product.py** rebuilds this nonzero QQ norm and checks the
**exact primitive integral polynomial equality** with the factors and
multiplicities stored in **factors/**. Modular reconstruction was only
a discovery tool: no reconstructed coefficient is trusted without the
integer product equality. The raw degree is **14,580**; its complete
non-forbidden squarefree support has degree **672**, exactly the ten
irreducible base factors below. No raw large intermediate file is stored.

## 3. One common rank-two carrier, then exact guarded caps

For each base factor \(f\), take \(F=\mathbb Q[V]/f\), with
\(S\) its rank-12 clock algebra. Write
\(A(E)=a_0+a_1E+a_2E^2\).
In the same algebra for *all* rows use
\[
 \mathcal H=S[e]/(e^2+a_1e+a_2a_0),\qquad e=a_2E .
\]
This has rank 24 over \(F\) even when a vertical fiber is nonreduced.
**joint.py** reduces the three rows with the *fixed* homogeneous
degrees \(3,4,6\): if a row has coefficients \(g_i\), its image
is \(\sum_{i=0}^d g_i a_2^{d-i}e^i\) in this same algebra.
No residue-specific leading-coefficient decrease changes a scale.
The actual \(a_2\) is live, and a true tableau sends all three
homogeneous rows to zero there.

The column space of the three multiplication maps, each first
multiplied by the 24th power of the indicated mask, lies inside the
exact multiplication image of that same mask power. The table gives
the upper bounds on the latter image and the successive *joint*
ranks lower-bounding the former. The lower bounds come from one
field residue of each exact factor, with leading coefficient and all
formula denominators units at the indicated prime.

| Factor degree and constant | Live mask | Exact cap | Prime / residue degree | Quintic; +middle; +fifth |
|---|---|---:|---|---|
| 12, 16227 | old ratio denominator | 22 | 103 / 12 | 22; 22; 22 |
| 12, 54123 | \(c_2\) | 18 | 103 / 4 | 18; 18; 18 |
| 24, 72 | \(n\) | 20 | 103 / 1 | 20; 20; 20 |
| 36, −7295157 | 1 | 24 | 103 / 4 | 24; 24; 24 |
| 48, 1865429207937 | \(q\) | 22 | 103 / 1 | 22; 22; 22 |
| 60, −10517167453750047 | \(a_2\) | 22 | 103 / 6 | 22; 22; 22 |
| 60, −1461941766456 | \(n\) | 22 | 103 / 1 | 22; 22; 22 |
| 60, 17286671927043 | 1 | 24 | 103 / 3 | 22; 22; 24 |
| 108, −1072276807957297777154175020668413 | 1 | 24 | 101 / 1 | 23; 24; 24 |
| 252, −1900844749533457989857434584838495093232550922764288 | 1 | 24 | 103 / 2 | 23; 23; 24 |

**certify-caps.py** computes exact norm zero of the masks with cap 22
in the rank-12 algebra, yielding rank at most 11 there, doubled by
the monic carrier extension. For \(c_2\) the exact singular norm is
already in the degree-four clock algebra, so free extensions by three
and two give cap \(3\cdot3\cdot2=18\).
For \(f_{24}\), it performs Gaussian elimination over the exact
number field \(F\): the old determinant has rank 10 (two exact
zero rows), so the doubled cap is 20. All inverses in this elimination
and in the residue replays are directly checked.

Each nonzero residue minor is a nonzero minor over the exact base
field. No unknown tableau or clock is reduced. Rank equality then
makes the joint column space the entire exact mask image. It contains
the mask power itself, and evaluation at any true candidate would
kill that power because it kills each row. The mask is live, so this
is impossible. Notice that the middle row is genuinely needed on
the degree-108 factor, and the fifth row on the positive-constant
degree-60 and degree-252 factors. This is not an argument from
separate vanishing determinants for the three rows.

## Replay and native boundary

Run `bash verify.sh` with Python, SymPy, and python-flint 0.9.
The exact norm is the longest step (about two minutes in the
recorded replay); single process is recommended. No raw large
polynomial file is created. The Mathlib module
`RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneLiveCarrier`
checks the local monic and homogeneous transfers, both scaled
collision equivalences, and the live-mask contradiction, with Lean
4.36.0 and the standard axiom set. The exact factor and rank replays
are separately executable **source** arithmetic, not a fully
kernel-generated tableau exclusion.

As a regression check on the earlier special cases, all 13 residue
fibers in the carrier-slices and old-quadratic packets have intrinsic
quintic pin degree three. They retain exactly the same checked ranks
after forcing this cubic weight explicitly, so those earlier
statements do not require an erratum.
