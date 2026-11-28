# The last alternate Fn beta-zero cubic chart is empty

**Result.** Over characteristic-zero fields, no normalized
no-late invisible-six DIRK11/13 candidate in the live reciprocal
\((\alpha,\beta,\gamma)=(1,0,5)\) chart has the remaining
alternate noncontact \(F_n\) old fit. In this scope the old
affine pivot \(A_1=0\), the contact and lost-ratio profiles are
already excluded, and the exact alternate \(F_1,F_2\) branches
are already closed. This completes the live beta-zero old-fit
inventory in this normalization, not the remaining alpha-one
middle-ghost charts or an unrestricted stage bound. The real
DIRK11 interval remains **13–14**.

## 1. The repeated root is paid by the two old affine coefficients

Use the actual old quartic zero prefix and
[old-profile census](../dirk11-thirteen-invisible-six-early-profile-census/README.md).
The remaining old fit is a nonmonomial quadratic, normalized
\(m=Y^2+rY+s\), with \(rs(c_2s-c_0)\ne0\) and \(c_0\ne0\);
\(R=Y^3+c_2Y^2+c_1Y+c_0\) is the actual three-clock hull.
Write the old affinity as
\[
 \mathfrak D=c_0r^2+D_1r+D_0,qquad
 D_1=-s(2s+c_1),\qquad D_0=3s(c_2s-c_0).
\]
The genuine first-ghost cleared gate, reduced modulo
\(\mathfrak D\) in \(r\), is \(A_1(s)r+A_0(s)=0\). The
vanished affine pivot therefore also gives \(A_0(s)=0\).
At the actual \(s\), both evaluations are zero, not
necessarily the polynomials themselves.

By the previously closed
[finite contacts](../dirk11-thirteen-invisible-six-alpha-one-beta-zero-finite-contacts/README.md),
[alternate F1](../dirk11-thirteen-invisible-six-alpha-one-beta-zero-alternate-f1/README.md),
and [alternate F2](../dirk11-thirteen-invisible-six-alpha-one-beta-zero-alternate-f2/README.md),
the remaining contact factor and both \(F_1(s),F_2(s)\) are
live on the remaining candidates. The exact old resultant is
\[
 \mathcal R(s)=c_0A_0^2-D_1A_0A_1+D_0A_1^2
              =\frac3{100}(c_2s-c_0)^2F_1F_2^2F_n.
\]
Differentiating in \(s\), **holding the old hull coefficients
fixed**, every derivative term of the first expression still
has one \(A_0\) or \(A_1\) factor. Thus \(\mathcal R(s)\)
and \(\mathcal R'(s)\) both vanish. The live product factor
on the right gives \(F_n(s)=F_n'(s)=0\).
No division by an old affine or old discriminant leader is
implicit. **old-repeated.py** reproduces the exact old
adjugate remainder and resultant and verifies this derivative
identity.

The cubic used here is
\[
 F_n(S)=12c_2 S^3-(36c_0+4c_1c_2)S^2
  +(-12c_0c_1+12c_0c_2^2-c_1^2c_2)S-c_0c_1^2 .
\]
If \(c_2=0\), this is \(-c_0(c_1+6S)^2\), so the actual
root is the already excluded lost ratio \(c_1+6s=0\).
Thus \(c_2\ne0\) and we really have a cubic. This separate
step handles its leading-degree loss before taking a
discriminant.

## 2. Both discriminant factors and exact multiple-root checks

Its full discriminant is \(-64c_2^2 H_3H_5\), where
\[
 \begin{split}
 H_3&=18c_0c_1-9c_0c_2^2+c_1^2c_2,\\
 H_5&=324c_0^3+216c_0^2c_1c_2-144c_0^2c_2^3
          -2c_0c_1^3+24c_0c_1^2c_2^2-c_1^4c_2.
 \end{split}
\]
Both routes are treated. Deflate the actual ordinary Jacobi
pencil at the physically fourth ordinary \(V\) to get
\[
 F(Y)=\frac{J_4(V)J_5(Y)-J_5(V)J_4(Y)}{Y-V}
\]
with live leader \(132J_4(V)\). Deflating at \(B\)
gives the cleared \(c_i\). For either discriminant factor,
substitute those coefficients and take the primitive
pseudo-remainder \(G(B)\) modulo \(F(B)\), removing only
nonzero rational constants and the listed live \(J_4(V)\)
powers. The exact \(B\)-resultants are:

| Factor | Removed pseudo-remainder content | Resultant support |
|---|---:|---|
| \(H_3\) | \(J_4(V)^2\) | \(J_4(V)^6 f_{36}(V)\), primitive constant −7295157 |
| \(H_5\) | \(J_4(V)^6\) | \(J_4(V)^8 f_{60}(V)\), primitive constant −10289767396352176431 |

Each \(f_d\) is exactly irreducible. They are different
and have no common root, so there is no missing intersection
of the two discriminant charts in the ordinary live locus.
For both exact base fields \(\mathbb Q[V]/f_d\), **proof.py**
checks the exact inverse pivot of the penultimate linear
\(B\)-subresultant, then independently computes the full
quotient-field \(\gcd(F,G)\). Its monic row is exactly that
linear lift. Both physical orders are kept: the program
checks \(B\ne0,1,V\), \(J_4(B)\ne0\), \(f_d(B)=0\),
and exact \(B(B(V))=V\) by evaluating the same linear
subresultant at \(B\), with its leading coefficient still live.

With the reconstructed old coefficients in each exact field,
the full Euclidean \(\gcd(F_n,F_n')\) has monic degree one.
Its degree trace is \(3/2\), \(2/1\), then zero, and each
inverse pivot is checked. Thus both branches have a single
actual repeated root \(s\), nonzero, and **neither** a
triple-root fiber nor a derivative/old leading-drop fiber
has been silently selected out. On \(H_3\) the code also
checks \(s=c_1/6\). As a separate symbolic check for this
branch, \(H_3=0\) with the live \(c_0,c_2\) forces live
\(c_1\) and \(2c_1-c_2^2\); then
\[
 F_n(S)=\frac{c_2(6S-c_1)^2(c_1^2+6c_1S-3c_2^2S)}
                     {9(2c_1-c_2^2)}.
\]
A triple would give \(4c_1=c_2^2\), coalescing the two old
affinity roots to \(r=c_2/2\) and making the literal first
ghost denominator \(q=3sc_2-4rs-3c_0\) zero. This is an
independent excluded contact, not a residue-only test.

## 3. Retain both old affinity roots and use the actual pins

After exact \(s\) recovery, do **not** choose an old
affinity root or assume separation. Adjoin \(r_*=c_0r\)
by the monic quadratic
\[
 r_*^2-s(2s+c_1)r_*+3c_0s(c_2s-c_0)=0 .
\]
Use the cleared live gauge \(m^\#=c_0Y^2+r_*Y+c_0s\).
The standard homogeneous coefficients \(p,q\) of the old
affine-root formula give \(z=p/q\), using the actual live
denominator. This preserves both formal old roots whether
or not the algebra is reduced; it never divides by a
discriminant of this quadratic.

The [universal fifth pivot](../dirk11-thirteen-invisible-six-alpha-one-beta-zero-universal-fifth/README.md)
gives \(d_B=0\) and live \(D_B\). The immediately adjacent
ordinary rows therefore give actual \((ND)_V=(ND)_B=0\).
Use the true affine first-forward-clean equation
\(J_b(t)=j_0+j_1t=0\) and opposite primitive quadratics
\(H_C(t)=h_{C0}+h_{C1}t+h_{C2}t^2=0\), \(C=V,B\),
of the [beta-zero primitive proof](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-beta-zero/README.md).
No position of a first middle ghost or its diagonal is
borrowed. In this unscaled code the reflected upper endpoint
is 1. The homogeneous pins
\[
        j_1^2 h_{C0}-j_0j_1h_{C1}+j_0^2h_{C2}=0
\]
are formed in the same finite algebra without dividing by a
leader, \(V-z\), or an old inverse that might formally drop.

Both finite free rank-two algebras have full joint
multiplication rank **2/2** at 103. The checked residue
factors, in the order \(f_{36},f_{60}\), are
\[
 V^4+16V^3+54V^2+101V+100,qquad
 V^4+64V^3+102V^2+54V+44.
\]
The residue lifts redo the entire \(s\)-Euclidean sequence
with the same degrees and checked inverse pivots.
Ordinary \(B\)-lift and Jacobi denominators are also checked
units in those selected residues. Thus these are nonzero minors of a permitted local
reduction of the same exact coefficient columns; no actual
tableau or unknown parameter is reduced. The exact joint
image contains 1, impossible for a field evaluation killing
both pins. In fact the first pin reaches the full rank on
each exact factor, so no false row-independence is assumed.

## Scope and replay

The old monomial census permits only \(m=1,Y^2\) since
\(m=Y\) has a nonzero old origin ghost gate.
The finite beta-zero packet closes these two, \(c_2s=c_0\)
and the lost ratio; old \(r=0\) is the already closed slope
\(-1\) case. In the remaining noncontact case the live
affine pivot gives direct \(F_1,F_2,F_n\): direct \(F_1\)
has slope \(-1\), direct \(F_2\) makes \(m\mid R\),
and direct \(F_n\) is closed in the cited beta-zero proof.
The zero affine pivot leaves only its three alternate
factors: the two cited alternate packets and this one
now close all three.

Run `bash verify.sh` with SymPy and python-flint 0.9.
The longest step is the exact arithmetic in the second
ordinary field; it does not write raw large polynomials.
The derivative transfer and finite field calculations here are
exact written and executable source arithmetic, not an
end-to-end native tableau nonexistence theorem.
