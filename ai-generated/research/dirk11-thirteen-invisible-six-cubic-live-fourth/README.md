# The fourth clean stage is explicit in the live cubic DIRK11/13 chart

**Result.** In the normalized invisible-six, no-late-ghost chart
with \(\deg U=3,\ \tau\ne0,\ \alpha=0\), the fourth ordinary reverse
diagonal is zero. The normalized reverse fit is
\(m(Y)=Y^2+rY+s\) with both \(r,s\ne0\). For fixed ordinary clocks,
the necessary weighted read equations restrict \(s,r\)
to at most 18 pairs over any characteristic-zero field. On the
special affine-slope-\(-1\) chart, the fifth ordinary reverse clock
is in a separate exact degree-60 projection, which excludes that
entire slope subcase. These are not unrestricted exclusions; the real DIRK11 stage interval is **13–14**.

Use the signed normalized tableau, genuine rooted spaces,
and \(\tau\ne0\) conditions of the
[live monomial packet](../dirk11-thirteen-invisible-six-cubic-live-monomial/README.md).
In particular it already excludes the monomial fits and proves
the displayed normalization with \(s\ne0\). Write \(Y\) for the
reflected clock, \(W(P)=bP(Y)\), \(N=A^{\mathsf T}\), \(I\) for
the zero-constant primitive, \(V=1-a\) for the fourth ordinary
reverse clock, and \(B=1-b\) for the fifth. There is no ghost
before \(V\). The old three ordinary clocks are distinct
nonzero roots of \(R_3=Y^3+c_2Y^2+c_1Y+c_0\), disjoint from \(V\).
Here \(c_0\ne0\). Use a common scale of \(G\) so \(G_i/b_i=Ym(Y)\)
on the old three; write \(q=G_V/b_V\ne0\).
All assumed shapes are actual rooted-order payments; none is imposed
on a different tableau.

## 1. A genuine, undivided double primitive

Set \(P=Ym\), \(P_0=YR_3\), and \(P_1=Y(Ym\bmod R_3)=YP-P_0\).
The old affine quotient \(\ell=IP/P\bmod R_3=\ell_0+\ell_1Y\)
comes from the true \(Z_4\) shapes at the old prefix.
Consequently as literal polynomials
\[
 IP=\ell P+\delta P_0,\qquad \delta=1/4-\ell_1 .
\]
Indeed the difference vanishes at the old triple and zero,
and has degree at most four. Moreover \(\delta\ne0\):
otherwise \(IP=\ell P\) and comparison after dividing the
polynomial factor \(Y\) gives \(\ell_0=0\) from \(s\ne0\);
the quadratic-monomial leading read gives \(\ell_1=1/4\)
whereas the coefficient at \(Y\) would force \(\ell_1=1/2\).

Let \(w=IP_0/P\bmod R_3\), \(t=I^2P/P\bmod R_3\), and
\(r_1=IP_1/P\bmod R_3\), all at most quadratic.
Integration by parts gives \(IP_1=Y IP-I^2P-IP_0\)
and hence \(r_1=Y\ell-t-w\) as polynomials of degree at most two.
The two genuine cubic marks and one genuine quartic mark at
the physical \(V\), from the live monomial packet, give
\[
\begin{split}
 IP(V)-d(P(V)-q)&=\ell(V)q,\\
 IP_1(V)-d(P_1(V)-Vq)&=r_1(V)q,\\
 IP_0(V)-dP_0(V)&=w(V)q,
\end{split}
\]
where \(d=A_{aa}\). Subtract \(V\) times the first cubic mark
from the second, and use \(P_1=YP-P_0\) and the quartic mark.
It yields the actual independent double primitive
\[
 I^2P(V)=t(V)q.
\]
This cancellation is independent of \(1+\ell_1\).

Integrating \(IP=\ell P+\delta P_0\), once more by parts,
gives \((1+\ell_1) I^2P=\ell IP+\delta IP_0\).
After dividing the polynomial values by \(P\) only at the
three old live sites, the degree bounds give
\((1+\ell_1)t=\ell^2+\delta w\).
Multiply the double primitive by \(1+\ell_1\) and substitute
both identities and the paid first/quartic reads. One obtains
\[
 d[\ell(V)(P(V)-q)+\delta P_0(V)]=0.
\]
But the first cubic mark and polynomial identity give the
bracket as \(d(P(V)-q)\). Since
\((\ell(V)-d)(P(V)-q)=-\delta P_0(V)\ne0\), the first factor
\(P(V)-q\) is live and **\(d=0\)**. This argument does not
divide by \(1+\ell_1\), any diagonal, or any ghost clock.
It also proves \(\ell(V)\ne0\) and \(IP(V)=\ell(V)q\ne0\).

## 2. Exact finite profile census at fixed ordinary clocks

The normalized affinity determinant is
\[
 \mathcal D=c_0r^2-(2s^2+c_1s)r+3c_2s^2-3c_0s=0.
\]
Let \(n\ne0\) be the multiplication determinant of \(m\) in
the old cubic algebra. The old roots are simple, and \(m\)
is live at each, so this determinant really is nonzero.
Use the adjugate of multiplication by \(m\) to compute the
quadratic polynomials \(\widetilde\ell=n\ell,\widetilde w=nw,
\widetilde t=nt\) without inverting a coefficient.
Since \(d=0\), the two independent scalar conditions are
\[
 \widetilde\ell(V) IP_0(V)-\widetilde w(V)IP(V)=0,\qquad
 \widetilde\ell(V) I^2P(V)-\widetilde t(V)IP(V)=0 .
\]
Each polynomial left side has factors \(V^2 R_3(V)\):
all primitives contain \(V^2\) and the two products agree
modulo \(R_3\) by their construction. These factors are
live at the fourth clean site. Denote the quotients by
\(\mathcal J,\mathcal J_2\).

If \(r=0\), affinity and \(s\ne0\) give \(s=c_0/c_2\),
with \(c_2\ne0\). The exact coefficient identity then is
\[
 \mathcal J_2=-V c_0^2(c_0-c_1c_2)/(60c_2^3).
\]
If \(c_0=c_1c_2\), \(R_3=(Y+c_2)(Y^2+c_1)\) and
\(m=Y^2+c_1\) vanishes on old roots, impossible. All remaining
factors are live and \(\mathcal J_2\) cannot be zero.
This excludes the entire zero-middle branch.

Let \(\mathcal A=\mathcal J\bmod\mathcal D\) in \(r\)
using its live leader \(c_0\). Exact elimination gives
\[
 \operatorname{Res}_{r}(\mathcal D,\mathcal A)
 =-\frac{F_1(s)F_2(s)F_3(s)}{14400\,c_0},
\]
where
\[
 F_1=96s^3-80c_1s^2+75c_0c_2s-75c_0^2,\qquad
 F_2=s^3-c_1s^2+c_0c_2s-c_0^2,
\]
and
\[
\begin{split}
F_3={}& V^2(-3c_0^2-6c_0c_2s+2c_1^2s+8c_1s^2-3c_2^2s^2+8s^3)\\
 &+V(-3c_0c_1s-6c_0s^2+c_1c_2s^2+2c_2s^3)
   +c_0^2s-c_0c_2s^2 .
\end{split}
\]
No linear pivot in \(\mathcal A\) is inverted. In particular
simultaneously zero constant and linear coefficients are retained.
\(F_3\) is never identically zero under the live hypotheses:
its constant coefficient is \(-3V^2c_0^2\ne0\).
Thus there are at most nine possible \(s\) values and at most
two \(r\)'s for each, without assuming the factors are squarefree.

For explicit future reconstruction, \(q=IP(V)/\ell(V)\)
has a live denominator. In this scale,
\(U(1-Y)\) is proportional to the cubic determined by
\(J_4/m\bmod R_3\) on the old three and \(h(V)/q\) at \(V\).
The free scale does not create extra shape choices. These
18 pairs are not realizations of a tableau.

## 3. Separate exact clock projection at affine slope minus one

Keep this as a **subcase assumption**, not a converse assertion
about the entire \(F_1=0\) divisor. If \(\ell_1=-1\), comparing
\(IP=\ell P+\delta P_0\) modulo \(R_3\) in powers of \(Y\)
gives
\[
 r=15(c_2s-c_0)/(16s).
\]
Since \(r,s\ne0\), the affinity determinant is then equivalent
to \(F_1(s)=0\). Substituting this \(r\) into
\(\mathcal J_2=0\) and taking the exact resultant in \(s\)
produces only \(c_0^{10}\) and a further polynomial cubic in
\(V\). The former is live; the latter is a necessary relation,
and uses the **uncanceled** double primitive rather than an
equation divided by \(1+\ell_1=0\).

The reflected ordinary Jacobi pencil can be written as
\(J_5(Y)J_4(B)-J_5(B)J_4(Y)\), with its nonzero fixed
normalizing leader, since \(B\) is a genuine ordinary root.
Deflate it first at \(B\), then at \(V\) to express the old
coefficients \(c_i\) in terms of \(B,V\). Substitute in the
cubic clock relation, clear the leading factors, and
pseudo-reduce by the four-site hull before taking the
resultant in \(V\). The exact primitive factors are
\(J_4(B)^4\) and one irreducible factor of degree sixty.
The quartic guard \(J_4(B)\) is already live by Jacobi
coprimality. This finite projection covers every branch with
the genuine affine slope \(-1\), even vanishing leading
coefficients of intermediate read polynomials.

Run `python3 project.py` with SymPy. All coefficient tests
here are over the rationals; no modular count is used as a
characteristic-zero exclusion. The fourth-diagonal result, the
zero-middle exclusion, the 18-profile census and the degree-60
conditional clock gate are distinct conclusions. In particular
the fourth-diagonal scalar identity alone should not be counted
again as an independent constraint against the same paid reads.


## 4. The genuine slope-minus-one chart is excluded

The degree-60 clock projection can be replayed on the entire
localized algebra, with no arbitrary tableau assumed integral.
The \(\mathcal J_2\) numerator after the slope substitution
clears only powers of the live \(s\) (and a rational scalar).
The coefficient content removed after the ordinary pair
pseudo-reduction has exactly the nonconstant factor \(J_4(B)^6\).
These and the \(c_0\) factor in the projection are checked exactly.

First recover \(V\) from the linear cofactor relation for
the ordinary quartic in \(V\) and the projected cubic.
Then recover \(s\) from the linear cofactor of \(F_1\) and
the reduced \(\mathcal J_2\) numerator. The relation is
obtained in each step by taking shifted polynomial rows
and combining the cofactors of all columns above linear.
It is necessary at a common root even at a degree drop.
Both leading pivots are units in the whole degree-60
algebra modulo 101. The resulting \(r\) is the explicit
slope formula in Section 3. Reconstruct \(q=IP(V)/\ell(V)\)
and the reverse carrier \(U_{\rm rev}\) by the old cubic
deflation and the sample \(h(V)/q\) at \(V\).
All denominators used to do this are checked as full
residue-algebra units before use.

For five initial forward ghosts, the actual \(A(C\phi)\)
cut again makes \(I(XU)+UQ_2\) a nonzero scalar times
that prefix hull. The full six-ghost hull is proportional
to \(S_6\) modulo \(U\), by the proved \(\tau\ne0\) live
cut of the [monomial packet](../dirk11-thirteen-invisible-six-cubic-live-monomial/README.md).
There is now no assumption about the remaining ghost's
clock. Multiplying by its linear factor imposes the
determinant of \(I(XU),X I(XU),S_6\) modulo \(U\).
It is a unit throughout the degree-60 base clock algebra.

For at least two ghosts in the reverse gap after \(V\),
use degree-four polynomials exactly matching the genuine
\(G/b,YG/b\) on all four regular sites through \(V\).
Start with \(P,P_1\), add the unique multiples of
\(P_0=YR_3\) needed to correct their two values at \(V\),
and retain the true zero at \(T\). Call the resulting polynomials
\(P_j^*\), and set \(r_j^*=I(P_j^*)/(Ym)\bmod R_3\).
Primitive/marked payments give, on that ghost block,
\(N_D(Y^jG)=G r_j^*(Y)\), exactly as in the earlier
[two-gap proof](../dirk11-thirteen-invisible-six-cubic-zero-two/README.md).
The commutator images of \(W(P_j^*)-Y^jG\) lie in \(Z_6\)
and vanish through \(V\). Here \(G_V\ne0\); instead of
the zero-multiplier proof, four live clean zeros kill
the effective cubic and make each row a scalar times
\(gG\), by the reciprocal identity. At the first ghost
\(z\) the two scalars have ratio \(z\), in the undivided
sense, because both are calibrated by \(d_z^2G_z\)
and \(g_zG_z\ne0\). Their difference with multiplier \(z\)
therefore vanishes globally. At the second ghost \(w\)
the first donor cancels and the remaining diagonal
satisfies \((w-z)d_w^2G_w=0\), so \(d_w=0\).
There is no requirement that \(d_z\ne0\).

Hence \(r_1^*(Y)-z r_0^*(Y)\) has the two roots \(z,w\).
Adjoin \(z\) using the monic cubic from its first-root
equation, with cubic leader verified as a unit.
The quadratic leader for the two-root equation is a unit
in the resulting rank 180, so its second root is
\(w=-c_1/c_2-z\), with \(c_1,c_2\) here denoting its
linear and quadratic coefficients.

An independent primitive is that of \(P_5=(Y-V)P_0\).
Its weighted tap is zero through the two ghosts, including
the weighted row at \(V\). Its \(Z_6\) decomposition is
\(GQ+eH_{\rm bary}\), the effective clean cubic
\(Q_{\rm eff}=Q+eU/\tau\) being reconstructed from the
four clean reads \(IP_5/k\).
At both ghosts \(Q=0\), so the necessary crossing is
\[
 Q_{\rm eff}(w)U_{\rm rev}(z)-Q_{\rm eff}(z)U_{\rm rev}(w)=0 .
\]
This is a unit in rank 180 modulo 101. Thus the genuine
slope-\(-1\) chart is excluded for all \(\gamma=3,4,5\).

Run `python3 replay.py` for the exact projection and both
finite-free unit tests. The replay can import the sibling
constant-exclusion, cubic five-prefix and cubic two-gap
replays, or accept `--arithmetic`, `--old-pair`
and `--old-mark` paths. The only reduction is in the
monic clock algebras over \(\mathbb Z_{(101)}\). A residue
multiplication unit lifts there by its determinant and
adjugate, after which every actual characteristic-zero
solution would give an evaluation homomorphism. This
requires no reduction of an unknown weight, ghost clock,
or arbitrary diagonal. The three companion Lean statements
check the marked cancellation, affine-slope coefficient,
and diagonal implication; the full actual-row transfer
and finite coefficient computations here are exact source
proofs, not an end-to-end Lean order nonexistence theorem.

[Lean scalar certificates](../../lean/RKCert/ReviewedNative/DIRKOrderElevenInvisibleSixCubicLiveFourth.lean) and the [pinned axiom audit](lean-audit-4.36.0.txt).
