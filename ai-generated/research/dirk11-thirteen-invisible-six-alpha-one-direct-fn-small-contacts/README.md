# Three small contact exclusions for the live direct Fn profile

**Scope.** In the normalized no-late invisible-six DIRK11/13
profile with live reciprocal multiplier, \(\alpha=1\),
and \(\beta=1\) or 2, assume the direct noncontact
\(F_n\) old fit. Then \(r^2=3s\), \(2r=c_2\), and a
first middle clock \(x=0\) are all impossible over
characteristic-zero fields. There is no extra assumption
on the fourth or fifth clean diagonal. The full direct
\(F_n\) profile is not excluded here, and the unrestricted
real stage interval remains **13–14**.

The [gap-diagonal proof](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md)
supplies \(d_x=0\), a true matched column
\(D=(Y-z)G-W(Q_4)\) with \(Q_4=(Y-z)P+K_*P_0\),
and exact \(L=(Y-z)\ell-\rho+K_*W_0=\lambda(Y-z)(Y-x)\)
with \(\lambda\ne0\). Use the notation of that proof:
\(R=Y^3+c_2Y^2+c_1Y+c_0\), \(P=Ym\), \(P_0=YR\),
\(P_5=(Y-V)P_0\), \(W(f)=b_{\rm wt}f(Y)\),
\(m=Y^2+rY+s\). Here direct noncontact means
\(rs(c_2s-c_0)(c_1+6s)\ne0\),
\(r=6c_2 s/(c_1+6s)\), and the known old affinity
and literal first-gap equations, including \(q\ne0\)
in \(z=p/q\), \(p=r c_0,\ q=3s c_2-4rs-3c_0\).
The old \(m\) values are all live. The separate chart
leader \(c_2\) is live since \(r,s,c_1+6s\) are live.

## 1. The ordinary contact \(r^2=3s\)

The direct formula gives \(c_1=6s(c_2-r)/r\).
Substitute it into the true old affinity equation to obtain
\(c_0(r^2-3s)=s^2(3c_2-4r)\). Under \(r^2=3s\) this
gives \(c_2=4r/3\), so
\[
 r=3c_2/4,\quad s=3c_2^2/16,\quad 8c_1=3c_2^2 .
\]

The ordinary pencil is \(T_5=(J_5+\mu J_4)/132\) with
five different nonendpoint roots. Recover \(\mu\)
from the fourth clock \(V\) by Jacobi coprimality,
and deflate at \(V\) then at \(B\). The quartic in \(B\)
has leader \(L_B=132J_4(V)\), and the corresponding
cleared old coefficients are \(C_j=L_B c_j\).
**clock.py** computes the exact \(B\)-resultant with
\(8C_1 L_B-3C_2^2\); the primitive content removed
from the contact gate is the constant \(144\).
The resultant is a nonzero rational times \(J_4(V)^4\)
times a single degree-24 irreducible factor \(f\), whose
primitive integer constant term is \(482450985\).
The penultimate subresultant is linear. Its coefficient
of \(B\) becomes a unit in the full residue algebra of
\(f\) at 101 and 103, so it is a unit in the exact
rational algebra as well. In particular the forced
\(B\) lift is not an extra assumption.

## 2. Three simultaneous necessary gates

The variable in the rank certificate is \(E=qK_*\).
Put \(Z=qY-p\), \(\zeta=Z(V)\), \(Q^\#=ZP+EP_0\),
and \(Q_V=Q^\#(V)\). Let \(n\) be the determinant
of multiplication by \(m\) in the old cubic algebra,
which is live; write \(\widehat F=nF\) for any old
division fit. In particular \(M=J_4/m\bmod R\),
\(L^\#=Z\widehat\ell-q\widehat\rho+E\widehat W_0\)
and \(L^\#=qnL\). Let
\[
 x_d=q[Y^2]L^\#,\qquad
 x_n=-q[Y]L^\#-p[Y^2]L^\#.
\]
Then \(x_d\ne0,\ x=x_n/x_d\), with no leader loss
by the gap-diagonal proof.

1. At \(V\), the exact \(ND=0\) prefix gives
   \(L(V)k=IQ_4(V)\) with \(k=G_V/b_V\). The exact
   scalar numerator is \((L^\# Q^\#-n ZI Q^\#)(V)\).
   The polynomial numerator is divisible by \(YR\)
   by the four old samples including polynomial zero,
   and \(P_0(V)\ne0\). Dividing this *polynomial* factor
   leaves the gate of degree at most two in \(E\).

2. For the true weighted \(P_5\) primitive there are
   literal distinct roots \(z,x\) of its cubic error
   polynomial \(Q_5\). Write \(D_0=L_1-V L_0\), where
   \(L_0=IP_0/Y\), \(L_1=I(YP_0)/Y\), and
   \(\widehat D_0=n(D_0/m\bmod R)\).
   Set \(R_v=R(V)\), \(j_v=J_4(V)\), \(h_v=V j_v\),
   \(M_*=R_v\widehat M-\widehat M(V)R\), and
   \(D_*=R_v\widehat D_0-\widehat D_0(V)R\).
   The reciprocal scaled carrier is
   \(S=Q_V M_*+n\zeta h_v R\).
   The same scaling of the effective cubic whose old
   and \(V\) samples give the primitive error is
   \(B_*=Q_V D_*+n\zeta V D_0(V)R\).
   Thus after the true read at \(z\), the cubic
   is a scalar multiple of the crossed polynomial
   \(S(z)B_*-B_*(z)S\). On expansion its common factor
   \(Q_V\) cancels, producing the affine-in-\(E\)
   cubic used in **rank.py**. If \(Q_V=0\), then
   \(\zeta=0\) by \(Q_V=\zeta k\) and live \(k\);
   the resulting expression is then itself zero,
   so no candidate is lost in the cancellation.
   Take its exact divided difference at \(z\), clear
   \(q^2\), and homogenize at \((x_n,x_d)\). The
   resulting gate has degree at most three in \(E\).

3. The literal commutator on \(W(P_0)\) has the true
   first-middle formula
   \((x-V-d_V)W_0(x)+Q_c(x)=0\), since \(d_x=0\).
   Here \(Q_c=-d_V^2(V/k)(R-R(z)U_r/U_r(z))\).
   Use \(d_{\rm den}=n\zeta P_0(V)\),
   \(d_{\rm num}=n\zeta IP_0(V)-Q_V\widehat W_0(V)\).
   An undivided polynomial numerator at \(Y=x\) is
   \[
    S(z)[(Y-V)d_{\rm den}-d_{\rm num}]\widehat W_0(Y)
      -d_{\rm num}^2[\widehat M(z)R(Y)-R(z)\widehat M(Y)].
   \]
   When \(\zeta=0\) both terms vanish directly.
   The common polynomial factor \(Y-z\) is cancelled
   (live \(x-z\)); clear evaluations at \(p/q\) and
   homogenize at \((x_n,x_d)\). This results in a gate
   of degree at most four in \(E\).

**coordinate-audit.py** independently evaluates these three scales
and the reflected primitive with exact rational numbers on four
generic direct-\(F_n\) clock coordinates. It does not assume those
sample coordinates satisfy the order-eleven quadrature pencil.

## 3. Exact finite-free exclusion

In the full monic degree-24 rational algebra for \(V\),
the three preceding polynomials have fixed degree caps
2, 3 and 4. Multiply each by every basis element
\(1,V,\ldots,V^{23}\) and by every \(E^j\) still within
cap 5. The target is free of dimension \(6\cdot24=144\).
**rank.py** checks the denominator and clock pivots and
that the resulting matrix has full row rank at both
101 and 103. Hence the exact rational matrix has full
row rank and its image contains 1. An exact candidate
killing the three gates would kill 1. This argument
does not reduce the candidate coefficients, assume that
\(E\) is integral, or rely on its degree being preserved.

## 4. The remaining two small contacts have symbolic proofs

Outside \(r^2=3s\), put
\[
 D_*=-c_2r^2+6c_2s+r^3-7rs.
\]
The exact old identities give
\[
 c_0=\frac{s^2(3c_2-4r)}{r^2-3s},\qquad
 z=\frac{rs}{r^2-6s},\qquad
 \det(m\bmod R)=
 -\frac{s^2(2r^2-9s)D_*^2}{r^2(r^2-3s)^2}.
\]
Here the determinant is multiplication by \(m\), equal
to the resultant with the monic \(R\). It is live by
the distinct old roots and nonzero \(m\) values.
Also \(r^2-6s\ne0\) by the true \(q\ne0\), and
\(3c_2-4r\ne0\) by \(c_0\ne0\).
**old-fits.py** verifies these identities and the literal
old derivatives \(\rho'(z),W_0'(z)\); each has a factor
\(2r-c_2\) and only the just-guarded denominators.
If \(2r=c_2\), then \(L'(z)=\ell(z)-\rho'(z)+K_*W_0'(z)=0\).
But \(L'(z)=\lambda(z-x)\ne0\), contradiction.
The \(r^2=3s\) fiber is already handled in §3.

If \(x=0\), the exact primitive identity in the gap-diagonal
proof forces \(\eta=0\), hence \(IQ_4=\lambda YQ_4\).
For nonzero \(Q_4\) this implies \(Q_4\) is a monomial:
each live coefficient would require its own primitive
denominator. Apply this to \(Q_4/Y=(Y-z)m+K_*R\).
If the monomial is constant, compare the cubic leader
to get \(K_*=-1\). At that value the verified linear
and quadratic coefficients are
\(6sD_*/[r(r^2-6s)]\) and \(D_* /(r^2-6s)\), both live.
If the monomial is nonconstant, its constant coefficient
forces \(K_*=zs/c_0\). At that value all of its degree
1, 2 and 3 coefficients are nonzero multiples
\(6s,4r,3\) of the same live value
\(D_* /[(4r-3c_2)(r^2-6s)]\). This is also impossible.

## Replay and native scope

Run **python3 clock.py**, **python3 rank.py --prime 103**
(or **101**), **python3 coordinate-audit.py**, and
**python3 old-fits.py** with SymPy and python-flint 0.9.
The exact argument is a source-only receipt. The native
gap-diagonal adapter is separate; no end-to-end Lean
theorem from \(\mathrm{HasOrder}\) is claimed here.
