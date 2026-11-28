# The exact univariate parameter and degree-18 coefficient field

The [forced zero first donor response](README.md) reduces
the five-equation geometry much further than its earlier
bivariate eliminants. This section treats fields of
characteristic zero, and paid finite characteristic
when the displayed pivots do not vanish.

Let
\[
\begin{aligned}
 B(a)&=896a^4-840a^3+300a^2-48a+3,\\
 M_0(a)&=5600a^4-5400a^3+1984a^2-327a+21,\\
 N_0(a)&=1600a^4-1600a^3+611a^2-105a+7 .
\end{aligned}
\]
The actual two \(JM\) equations give by fraction-free Cramer
identities \(5B(a)m=-M_0(a)\), \(5B(a)n=N_0(a)\).
In characteristic zero they cannot have \(B(a)=0\)
because \(\operatorname{Res}(B,M_0)=2^{14}3^2 7^3\cdot13\ne0\).
The same applies in paid positive characteristic other than 13.
Consequently \(a\) is a root of the degree-nine polynomial
\(N\) in the [univariate replay](univariate.py), and
\(V=Y^2+mY+n\) is uniquely determined.

On the regular branch let \(s_i=I((Y-1)VY^iM)\).
When \(s_0\ne0\), choose \(e=s_1/s_0\); then
\(N(a)=0\) gives \(s_2=e s_1\). Pick the distinct
splitting roots \(f,g\) of \(V\).
These formulas pay all \(JM\) equations and both
\(I(\nu M)=I(\nu YM)=0\); the latter identities pay
the blind \(JG\) read for every \(c\) by the exact
new primitive identity. The fifth pressure is already
zero. Finally choose \(d\) freely, and with
\(G_1=Y(Y-a)(Y-2a)\) set
\[
  c=\frac{I(\nu(Y-d)Y G_1)}{I(\nu(Y-d)G_1)}
\]
if the denominator is nonzero.
This is exactly the remaining nodal \(G\)-equation;
all five geometry equations hold. The unit stage
reconstruction still needs its original distinctness,
mass and physical-read guards. The executable modulo
solver verifies all five equations, and in the default
17-adic cell reproduces the archived geometry through
\(17^9\).

The nonic \(N\) is irreducible over \(\mathbb Q\).
Its reduction modulo 29 has degree nine and is
irreducible: the exact Frobenius check gives
\(X^{29^9}\equiv X\bmod N\) and
\(\gcd(N,X^{29^3}-X)=1\bmod29\).
These are the complete degree-nine irreducibility
tests, since 3 is the only prime dividing nine.
Thus \(\mathbb Q(a)\) has degree nine for every
candidate in this chart. This also gives a chart
exclusion over \(\mathbb F_{29^j}\) when \(9\nmid j\)
and over \(\mathbb Q_{11}\) by the already checked
projective mod-11 root obstruction for \(N\).

The splitting of \(V\) requires an additional **quadratic
extension** of \(\mathbb Q(a)\), not just one witness-specific
choice. Embed \(\mathbb Q(a)\) into \(\mathbb Q_{17}\)
using the other simple residue \(a=14\), where \(N'\equiv4\).
Here \(B=13\) is a unit, and \(m,n\) reduce to \(12,5\).
The discriminant \(m^2-4n\) reduces to \(5\), a nonsquare
unit modulo 17. It cannot be a square in \(\mathbb Q(a)\),
since a square of valuation zero would reduce to a residue
square at this place. Hence \(V\) is irreducible over
\(\mathbb Q(a)\). Any characteristic-zero tableau in the
guarded two-pair chart contains the actual scalar ordinates
\(a,f\) in its coefficient field (they are reverse row-sum
clocks), and so contains a subfield of degree \(18\)
over \(\mathbb Q\).

For the **existence** construction use the other simple
residue \(a=16\), where \(V\) splits at \(4,6\).
With \(d=8\), \(s_0\) and the \(c\)-pivot reduce to
\(8,16\) respectively. The root \(a\) and one root \(f\)
therefore generate a degree-\(18\) subfield of
\(\mathbb Q_{17}\); the other ordinates and all
coefficients are rational functions of them. The
previously verified unit guards make this exactly a
15-stage order-ten tableau over that field. Its
coefficient field is exactly degree \(18\), as the
clock sums recover \(a,f\).

The field is not intrinsically nonreal: an independent
exact Sturm check isolates all three real roots of \(N\)
and finds the quadratic discriminant positive at each.
The parameter field has signature \((6,6)\) (six real
embeddings and six complex conjugate pairs). This
only yields another explicit ordered algebraic
coefficient field supporting the 15-stage existence
bound; neither minimal degree over arbitrary charts
nor rational existence is implied.

## Reproduce

    python3 -B univariate.py
    python3 -B field-audit.py
    sha256sum -c closure-sha256.txt

The univariate solver uses exact modular arithmetic and
reconstructs \(V,e,c\) directly. The field audit checks
the exact polynomial identities, both 17 places,
the modular irreducibility criterion, and the real root
isolation. None of these field statements is a native
HasOrder theorem over a symbolic algebraic extension.

The portable Core source ERK10FifteenDegreeEighteen.lean
checks the monic reduction of \(N\) modulo 29,
all ordinary adjacent powers through \(X^{232}\),
the nine Frobenius steps, the explicit degree-three
Bézout identity, and the nonsquare residue of the
other 17-adic place. Its finite arithmetic was
replayed on Lean 4.34.1, 4.35.0, 4.36.0 and
4.37.0-rc1 with only standard axioms. The passage
from those arithmetic receipts to irreducibility
and to the exact number-field tableau is mathematical.
