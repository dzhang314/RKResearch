# Reflection-paired rational strict SDIRK7 charts

This packet tests a nine-stage architecture with the first
three weights zero, six distinct nonzero-weight active clocks,
and **three reflection pairs** about the uniform integration
midpoint. It does not assume positive weights.

- A nonzero visible cubic defect is impossible on any such
  three-pair grid over an ordered field.
- In the cubic-clean, paid-head chart over \(\mathbb Q\),
  the first normalized forward clock cannot be \(0,2,11\);
  for the constant-seed head \((1,3,5)\), its only allowed
  first clock is \(1\), and all three possible paired
  chronologies are excluded there too.
- A separate rank-two reflected/star head cannot open any
  cubic-clean tail over \(\mathbb Q\), even without pairing.
- Two less restrictive single-pair rational searches for the
  nontrivial arithmetic head remain unresolved; no rational
  nine-stage tableau or global exclusion follows.

The [native Lean scalar gates](../../lean/RKCert/Research/SDIRKSevenPairedClean.lean)
were checked using stock 4.36.0. Their scalar and field scope
is recorded separately from the chart ingress and arithmetic
chronology results below.

## Two immediate pairing gates

On six distinct active sites consisting of three reflection
pairs, the degree-five Lagrange formula gives the same mass
to both members of a pair, since the uniform integral is
invariant under reflection. Thus the number of negative
active weights is even. On the other hand a nonzero cubic
defect on the six sites is orthogonal to the four sampled
clock powers through degree three and is isotropic for the
weighted diagonal form. The four-dimensional clock space has
a positive-definite form, given by the paid degree-six
uniform Hilbert matrix. Its complement has dimension two
and is nondegenerate. The presence of the isotropic vector
makes that complement a hyperbolic plane (choose a vector
paired nontrivially with it, then subtract a multiple to make
both isotropic). The whole form thus has exactly one negative
direction. This is incompatible with paired nonzero masses
over any ordered field. No real-closed assumption or square
root of a positive element is needed.

Likewise five symmetrically arranged sites
\(-a,a,-b,b,0\) and a sixth unmatched site \(c\) cannot
all carry nonzero weight, even with signs. The centered odd
quintic \(X(X^2-a^2)(X^2-b^2)\) integrates to zero and
vanishes on the five symmetric sites, forcing the unmatched
weight to vanish. This is native as a field moment identity.
It rejects the centered \(z=2u\) arithmetic suffix with a
paired first two active clocks, since \(1,u,2u-1\) already
make a symmetric triple.

## Rational paid clean pairs

Normalize the common diagonal to one so that the interval
in normalized time is \([0,z]\) and \(\gamma=1/z\).
Use reflected coordinates \(y=z-x\), with \(y_{\mathrm{last}}=1\)
by the exact first adjoint. Write \(u\) for the penultimate
reflected clock and \(m=z/2\). For the established
[paid-head reverse chart](../strict-sdirk7-dirty-tail/README.md),
the active second adjoint error \(D\) annihilates the five
moments through degree four and has terminal ratios
\[
  \frac{D_{\rm last}}{\beta_{\rm last}}=-\frac12,\qquad
  \frac{D_{\rm penult}}{\beta_{\rm penult}}=\frac{u^2-4u+2}{2}.
\]
The support is six distinct sites, so \(D_y=\kappa/P'(y)\)
for their nodal polynomial \(P\). The quadrature weight is
\(\beta_y=K_y/P'(y)\) with \(K_y=I(P/(X-y))\) and
\(I(X^j)=z^j/(j+1)\).
Consequently \((u^2-4u+2)K_u+K_1=0\).

If the last two sites were opposite members of a pair,
\(K_u=-K_1\ne0\) by reflection, forcing \((u-2)^2=3\).
This is impossible over \(\mathbb Q\).
Thus the standardized radii
\[
 r=1/m-1,\qquad q=u/m-1,\qquad d
\]
come from three different pairs \(\{\pm r\},\{\pm q\},\{\pm d\}\)
on the centered uniform interval \([-1,1]\).
All three are nonzero, and \(r+1=1/m\ne0\).

Put \(R=r^2,\ U=q^2,\ D=d^2\) in this paragraph only.
The monic nodal product has uniform integral zero, which is
\[
 N(R,U)-A(R,U)D=0,\quad
 N(R,U)=1/7-(R+U)/5+RU/3,\quad
 A(R,U)=1/5-(R+U)/3+RU .
\]
There is no degree-six pivot loss over \(\mathbb Q\):
\(N=A=0\) would give \(R+U=6/7,\,RU=3/35\), hence
\((35(R-U)/4)^2=30\). By symmetry the same pivot works for
any elimination of one squared radius. The native proof
checks this rational nonsquare argument.

In centered coordinates the divided-difference numerator at
the \(r\) site is proportional to
\(r[1/5-(U+D)/3+UD]\), and similarly at \(q\).
After using paid quadrature, multiplication by \(A\) reduces
the bracket to \((-4/1575)(35U^2-30U+3)\).
With \((r+1)^2(u^2-4u+2)=(q+1)^2-4(q+1)(r+1)+2(r+1)^2\),
the terminal equality factors as \((q-r)H(r,q)=0\), where
\[
 \begin{split}
 H(r,q)={}&35q^3r^3+70q^3r^2+35q^3r
 +70q^2r^4+70q^2r^3+5q^2r^2+3q^2\\
 &-70qr^5+95qr^3-39qr-6q-3r^2-6r-3 .
 \end{split}
\]
Distinctness removes \(q-r\). These reductions, including
the paid-moment-to-\(H\) ingress without division, are native.

### Opener \(a=0,2,11\)

Here \(a\) is the first active **forward** clock.
It cannot be the last or penultimate physical clock,
and it is not the reflection partner \(1\) of the last.
If it is the partner of the penultimate, \(u=a\), substitute
\(q=a(r+1)-1\) into \(H\). Otherwise its radius is the
third, \(d=\pm(a(r+1)-1)\). Then use paid quadrature to solve
\(U=q^2=N(R,D)/A(R,D)\). Reducing the cubic \(H\) by
\(q^2-U\) produces \(L(r)q+C(r)\); any root forces
\(C^2-U L^2=0\), including at \(L=0\).
[check-fixed-openers.py](check-fixed-openers.py) verifies the
exact factor products and a projective prime-rootlessness
certificate for every nonlinear factor in all six cases.
The only linear possibilities are the forbidden \(r=-1\)
or \(r=0\). In particular the \(a=11\) third-radius
projection has nonlinear degrees \(14,4\), excluded
projectively modulo \(37,11\) respectively.
This exclusion uses the paid second-adjoint rule but
does not assume a particular three-row coefficient matrix.

### Opener \(a=1\) on the constant-seed head

Here the three head clocks are \((1,3,5)\) and all three
strict head taps are two. The first active clock is 1,
the partner of the last physical clock \(z-1\).
In centered reflected time, \(Y_1=-r\). Among active slots
2,3,4 one must have \(Y=-q\) and the other two \(Y=\pm d\).
Up to choosing the sign of \(d\), the three chronologies are
\[
 (-q,d,-d),\quad(d,-q,-d),\quad(d,-d,-q).
\]
On this head the normalized quadratic seed is the constant
one, and the three reverse test profiles in the forward
variable are \(1,X,(X-1)(X-3)(X-5)\).
Following the [single-slot chronology](../strict-sdirk7-rational-nine-collision/README.md#2-necessary-curve-equations-for-the-relaxed-distinct-tail-chart),
choose the member vanishing at the first two actual sites.
In centered reflected coordinates its scaled polynomial is
\[
 F_2=(X-Y_1)(X-Y_2),\qquad
 f=F_2(X+Y_1+Y_2+9r+6).
\]
Indeed the \(X^2\) coefficient in forward time must be
minus nine times the \(X^3\) coefficient.
The reverse combinations have densities
\(h=(X-r)(X-q)\) and
\(k=-[(1+X)^2-4(r+1)(1+X)+2(r+1)^2]\), with harmless
nonzero scales. Write \(\widehat T=\int_{-1}^X-(r+1)\mathrm{Id}\)
and the uniform centered mean \(I_0\). The read on \(f\)
after a strict triangular advance only uses the fourth
active stage, so its two combinations force
\[
 I_0\bigl((kI_0(\widehat T(h)f)-hI_0(\widehat T(k)f))
              F_2(X-Y_3)\bigr)=0.
\]
No tap, numerator value, or fourth moment is canceled.
Reduce this equation by \(d^2=N(R,U)/A(R,U)\) and take
its norm in \(d\). Then use the resultant with \(H(r,q)\).
[check-constant-chronology.py](check-constant-chronology.py)
checks each resultant and exact factor product. The large
factors have degrees 70, 58 and 66, projectively rootless
modulo 19, 11 and 11; the smaller factors are also tested.
Only \(r=0,-1\) can survive. This excludes all three
paired chronologies on this constant-seed head.

## Other rational heads and a direct witness attempt

The reflected/star rank-two head has clocks \(1,1+t,3-t\)
and taps \(A'_{21}=t,A'_{31}=2-t,A'_{32}=0\).
Its head seed \(g=2A'x-x^2\) interpolates the same quadratic
for every allowed distinct triple,
\[
 Q(X)=-X^2+4X-2 .
\]
The seed vanishes on the clean tail, and its advance vanishes
there as a cubic defect. At the first active stage this
requires \(Q(a)=JQ(a)\), with zero-origin primitive \(J\):
there are no earlier active taps and the diagonal is one.
The resulting homogeneous Laguerre cubic is projectively
rootless modulo 5. The head interpolation and scalar
nonexistence are native. This particular reflected/star
head cannot feed a rational clean tail, regardless of
clock pairing.

For arithmetic clocks \(1,1+t,1+2t\), the rank-two third
tap is
\[
 A'_{32}=-2t(3t-2)/(t^3-4t^2-t+2).
\]
The first clean forward read is cubic in its opening \(a\).
A tangent through the cusp of the opener curve meeting the
known rational points \((t,a)=(1,2),(2,1)\) is the Möbius
graph \(a=2t/(3t-2)\). Substitution gives exactly
\(2t^3(t-2)(t-1)(31t-22)/(3t-2)^3\) for the
canonical cubic numerator. This recovers the known rational
nontrivial opener \((22/31,11)\), not a tableau. Other
degree-one and degree-two secants to the known points did not
produce a new opener; they are not exhaustive.

For \(t=22/31,a=11\) we also left the second early clock
\(b_*\) free and tried just one terminal mirror pair, setting
\(u=11\) or \(u=b_*\). Both produce a primitive univariate
projection in \(z\) after specializing \(b_*\), of degree
at most 16. [search-single-pair.py](search-single-pair.py)
tests projective residue conditions and factors each
surviving specialization for **all rational \(z\)**. It
includes the literal rational linear assembly and a direct
85-tree verification if a candidate is found. In the
height-80 diagnostics there was no nonzero rational
projected \(z\), so no candidate reached rooted replay.
The height bound on \(b_*\) remains, and neither single-pair
family is excluded globally.

## Replay

    python3 check-fixed-openers.py
    python3 check-constant-chronology.py
    python3 search-single-pair.py first --height 80
    python3 search-single-pair.py second --height 80

The exact arithmetic scripts use SymPy 1.14.0 and
python-flint 0.8.0, without floating point or a numerical
grid. Only the last two commands are bounded diagnostics.
The typed [proof audit](proof-audit.lean) lists the axioms
of the scalar Lean gates. The pairing ingress from rooted
conditions and the chronology resultants are mathematical
arguments with separate exact replay.
