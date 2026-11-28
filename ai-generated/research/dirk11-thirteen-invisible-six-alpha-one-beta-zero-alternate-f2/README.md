# Alternate F2 is impossible in live beta-zero DIRK11/13

**Result.** No characteristic-zero coefficient field supports
a normalized no-late invisible-six DIRK11/13 candidate in the
live \((\alpha,\beta,\gamma)=(1,0,5)\) chart with an
alternate old \(F_2\) profile. This is the nonmonomial
old fit with live \(rs(c_2s-c_0)\) and vanished affine pivot
\(A_1=0\) in the
[old-profile census](../dirk11-thirteen-invisible-six-early-profile-census/README.md).
It is distinct from the already closed direct noncontact
\(F_n\) and the named finite old contacts. Other alternate
profiles and the unrestricted real stage interval **13–14**
are not decided by this packet.

## 1. The alternate old root and its factors

Use \(R=Y^3+c_2Y^2+c_1Y+c_0\), \(m=Y^2+rY+s\) in the
monic gauge, and the genuine old affinity and first-ghost
fit of the census. Here \(c_0\ne0\) from the old ordinary
clocks, and \(s\ne0\) from the nonmonomial old identity
\(IP=\ell P+\delta P_0\) and its origin coefficient.
Set \(a=c_0/s\ne0\). Then
\[
 F_2=s^3-c_1s^2+c_0c_2s-c_0^2=0
       \quad\Longrightarrow\quad c_1=s+a(c_2-a).
\]
The old hull factors as \((Y+a)(Y^2+(c_2-a)Y+s)\).
The normalized affinity equation is exactly
\[
 \mathfrak D=s(r-(c_2-a))(ar-3s)=0.
\]
The root \(r=c_2-a\) makes \(m\mid R\), contrary to the
live values of \(m\) at the three old actual regular clocks,
whose product is the multiplication determinant. Thus the
true alternate root is \(r=3s/a\). This includes the
possibility that the two formal affinity roots coincide:
that coincidence would already make \(m\mid R\).

**old-factors.py** reconstructs the common old adjugate
and the affine remainder \(A_1r+A_0\) before specializing.
Up to a live constant, the specialized \(A_1\) is
\[
 (7s-a^2-a c_2)
       (a^2-a c_2+3s)
       (5a^2-5a c_2+16s).
\]
It also checks \(A_0=(a-c_2)A_1\).
The middle factor cannot vanish. At \(r=3s/a\), the
actual old multiplication determinant is
\[
 n=-\frac{s(-a^2+2s)(a^2-a c_2+3s)^2}{a^2}\ne0 .
\]
There is no sign assumption and no division by that factor.
If the last factor vanishes, then
\(c_2-a=16s/(5a)\) and \(c_2-r-a=s/(5a)\ne0\).
The actual coefficient
\(\delta(c_2-r-a)=r/12\)
forces \(\delta=5/4\) and \(\ell_1=1/4-\delta=-1\).
This is the already excluded [slope-minus-one beta-zero
profile](../dirk11-thirteen-invisible-six-alpha-one-slope-minus-one-beta-zero/README.md),
irrespective of the old affine pivot. Consequently
\(7s=a^2+a c_2\) is the sole live branch.

## 2. A degree-24 ordinary field that keeps both V/B assignments

The clock \(X=-a\) is one of the actual three old regular
clocks by the displayed factorization of \(R\). Thus
\(X\ne0,1\), \(J_4(X)\ne0\) by the actual ordinary Jacobi
pencil. Deflate that pencil at \(X\) to get
\[
 T_4(Y)=
 \frac{J_4(X)J_5(Y)-J_5(X)J_4(Y)}
      {132J_4(X)(Y-X)}
 =Y^4+d_3Y^3+d_2Y^2+d_1Y+d_0 .
\]
The other two old clocks are the roots of
\(Y^2+uY+s\), where \(u=2X-7s/X\).
The actual fourth and fifth regular clocks \(V,B\)
are the roots of the complementary \(Y^2+vY+w\).
Coefficient comparison gives
\[
 v=d_3-u,\qquad w=d_2-s-uv,\qquad
 uw+sv-d_1=0,\qquad sw-d_0=0.
\]
In the cleared last two equations the only denominators
are supported on \(X\) and \(J_4(X)\), both live.
Before clearing, their cubic leaders in \(s\) are
\(-343/X^3\) and \(49/X^2\). Thus no leader drop occurs
at an actual candidate. In particular \(s=0\) is not an
omitted candidate: it was already ruled out by the live old
profile. The replay also checks both cleared cubic leaders
and the recovered \(s\) are units in the exact finite field.

The exact resultant in \(s\) is a nonzero rational constant
times \(X^6J_4(X)^3 f_{24}(X)\), with exact irreducible
\(f_{24}\) of primitive constant coefficient **3176523**.
In \(\mathbb Q[X]/f_{24}\) the penultimate subresultant has
degree one and its leading coefficient is a unit.
The replay also computes the full exact Euclidean gcd there;
its monic linear row gives precisely the same recovered \(s\).
All inverse pivots are individually checked. This is an
exact field calculation, not an inference from a modular
degree. Adjoin a **monic quadratic**
\(V^2+vV+w=0\) and define \(B=-v-V\). This retains both
assignments of the distinguished ordinary rows, without
ordering or an assumption of splitness of the quotient used
in the certificate.

## 3. Opposite primitive pins in the same finite algebra

The [universal fifth-diagonal proof](../dirk11-thirteen-invisible-six-alpha-one-beta-zero-universal-fifth/README.md)
gives \(d_B=0\) and \(D_B\ne0\) without an old ratio.
As \(B\) immediately follows \(V\), \((ND)_V=(ND)_B=0\).
The [beta-zero primitive proof](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-beta-zero/README.md)
then gives the true affine forward first-clean row
\(J_b(t)=j_0+j_1t=0\) and the two reverse primitive rows
\(H_C(t)=h_{C0}+h_{C1}t+h_{C2}t^2=0\), \(C=V,B\).
This ingress uses no direct \(F_n\) ratio and does not
divide by \(V-z\). The correct unscaled upper endpoint
in the reflected primitive is 1.

From the actual survivor coordinates,
\(r=-3s/X\), so use the old gauge
\(m^\#=XY^2-3sY+Xs\), and use
\(p=Xs, q=2X^2-3s\) for \(z=p/q\).
The old live affine-root denominator verifies \(q\ne0\);
there is no assumption of new clock separation.
Compute the two necessary homogeneous pins
\(j_1^2h_{C0}-j_0j_1h_{C1}+j_0^2h_{C2}\) in the **same**
finite algebra. Neither old cubic nor carrier parameters
are divided by a leader of one of these two rows.

At prime **103**, using the degree-one residue \(X+21\)
of \(f_{24}\), their joint multiplication image in the
monic complementary quadratic has rank **2/2**. All
modular inverses used in reconstructing \(s,d_i\) are
checked. Thus this is one exact nonzero minor after
a permitted local coefficient reduction, proving full
rank over the exact base field. The image contains 1,
contrary to any evaluation killing both actual pins.
The first pin alone reaches full rank on this particular
factor; no artificial row-independence is assumed.
No unknown tableau, clock or carrier is reduced.

Replay with `bash verify.sh` (SymPy and python-flint 0.9).
The accompanying Lean module checks the local old-affinity
root and forbidden determinant factor, with Lean 4.36.0
and standard axioms. The full exclusion uses the exact
written/source proof, not an end-to-end Lean tableau theorem.
