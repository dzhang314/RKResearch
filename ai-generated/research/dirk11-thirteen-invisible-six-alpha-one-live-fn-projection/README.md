# Finite ordinary projection for the live direct Fn cubic chart

**Result.** For the normalized no-late invisible-six
DIRK11/13 chart with cubic carrier, \(\tau\ne0\),
\(\alpha=1\), and direct noncontact old \(F_n\)
profile, each of the \(\beta=1,2\) physical counts has
only finitely many possible fourth reverse ordinary
clocks \(V\) in an algebraic closure of characteristic zero.
Two exact polynomials with that property are specified
by this source. This is a finite ordinary reduction,
**not** a replayed enumeration or exclusion of the
remaining live-diagonal profile. The unrestricted real
interval stays **13–14**.

Use the actual ingress and the same degree bounds of the
[live finite-profile proof](../dirk11-thirteen-invisible-six-alpha-one-live-cubic/README.md).
There are two genuine equations:
the stronger actual fourth-clean adjacent mark
\(A(t)=0\) with carrier degree at most 2,
and the appropriate true middle crossing
\(B_1(t)=0\) or \(B_2(t)=0\).
The latter have carrier degree at most 7 and 5
respectively. Both include the internal rank-leader
and commutator degeneracies, as derived there. Neither
a grade-seven forward determinant nor independence
of the two common adjacent and F6 tests is assumed.
The [additional first-middle gate](../dirk11-thirteen-invisible-six-alpha-one-live-first-middle/README.md)
can be used to reduce the resulting finite support further;
it is not needed to establish finiteness.

## Exact free clock algebra

Write \(V\) for the fourth ordinary **reverse** clock,
\(B\) for the fifth, \(L=132J_4(V)\),
and \(\widehat B=LB\).
The monic finite-free ordinary quartic follows by
deflating the Jacobi pencil at \(V\). Adjoin the
scaled old-profile cubic variable
\(\sigma=L_3 L^2s\) monically, where \(L_3\) is the
leader of the Fn profile cubic in the scaled
coordinates. The rank of the resulting algebra
\(\mathcal A\) over \(\mathbb Q[V]\) is 12.
The actual direct profile uses
\(r=6c_2s/(c_1+6s)\) with the stated live denominators.
Their homogeneous numerator gauge for the old quadratic
\(m\), and the common adjugate for its old fits,
are exactly as in the earlier profile arithmetic.
Every actual evaluation of the chart defines a map
of this monic clock algebra to the coefficient field.

The code keeps the full old adjugate gauge \(n\)
without dividing any nonconstant scalar content.
For example the physical reciprocal reads at regular
sites use \(k=n YJ_4/U_r\) in that gauge, and the actual
carrier is \(U_r=M+tR\) after its common scaling.
The adjacent polynomial uses precisely that same
gauge. The reflected forward primitives are checked
independently against the reverse-endpoint primitive
\(\int_Y^L (L-Z)U_r(Z)\,dZ\); both bounds on the
beta-specific determinant degrees follow from the
literal column constructions in the earlier proof.

## Fixed-degree resultants and an exact nonzero witness

For \(\beta=1,2\), define the exact univariate
ordinary projector
\[
 F_\beta(V)=
 \operatorname{Norm}_{\mathcal A/\mathbb Q[V]}
       \operatorname{Res}_t(A(t),B_\beta(t)),
\]
using fixed Sylvester degrees 2 and respectively
7 or 5. Even when a specialized polynomial loses
a leader, evaluations at an actual common finite
root annihilate the Sylvester columns, so the exact
resultant still vanishes there. The actual field
evaluation next kills the multiplication map of
this zero resultant, hence its exact norm specializes
to zero at the actual \(V\).

The code evaluates the universal fixed-degree
resultant without computing a large Sylvester
determinant. If \(A=a t^2+b t+c\) and
\(E=\sum_{i=0}^m e_i t^i\), define
\(S_0=2,S_1=-b,S_j=-bS_{j-1}-acS_{j-2}\).
Then
\[
 \operatorname{Res}(A,E)=
 \sum_{i=0}^m e_i^2 a^{m-i}c^i+
 \sum_{0\le i<j\le m} e_i e_j c^i a^{m-j} S_{j-i}.
\]
Indeed for two generic roots \(t_1,t_2\) of \(A\),
fold \(a^m E(t_1)E(t_2)\) using
\(t_1t_2=c/a\) and
\(S_j=a^j(t_1^j+t_2^j)\). This is an identity of
integer coefficient polynomials, so specialization
retains all leading-loss cases.

No reduction of an actual unknown clock is used to
prove nonzeroness. All preceding constructions use
monic polynomial reduction and rational constants
with denominators prime to 103. Evaluating the
fully specified coefficient construction at the
**formal** value \(V=2\) modulo 103 gives the
two norm values **32** and **9**, respectively.
Thus each exact rational projector is nonzero;
its characteristic-zero zero set is finite.
The witness alone does not determine the exact
factor support or its degrees.

Run **python3 projection.py** with python-flint 0.9.0
for the small residue witness that certifies exact
nonzeroness. **--exact 1** and **--exact 2** request
full expansion of the respective rational norms
and can be significantly more expensive. No full
expansion or factorization is claimed as a receipt
in this packet. The adjacent, divided-difference
and squared-diagonal scalar inputs have separate
Lean receipts in the linked live finite-profile
packet; this is a source-level algebraic reduction.
