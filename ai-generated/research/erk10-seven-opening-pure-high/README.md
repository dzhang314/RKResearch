# Seven-row rational opening obstruction for a pure-high ERK10 splice

This rules out an alternative rational ERK10 construction architecture,
not an arbitrary ERK10 tableau. It applies, for example, if one extends
the [actual seven-stage local size-six port](../erk10-six-opening-singleton/README.md)
using only pure-through-size-six high rows.

**Hypotheses.** The first six strict explicit rows pay \(C(2)\) except
the second, and give actual order five at a nonzero horizon \(\xi\).
The seventh physical row is the true FSAL row with those output weights,
so is locally pure through size six at \(\xi\). Every later row is
also locally pure through size six. The final output is supported on
the origin and high rows, including FSAL. The proof assumes neither
a mirror nor any particular reverse equation or donor coefficients.

## Obtain a dimension-two bound on the projected opening defects

For combinations of trees of size at most five, the ideal derivative
model is the corresponding combination of
\( |\tau|X^{|\tau|-1}/\gamma(\tau) \).
Let \(m\) be the dimension of the ideal-model image of the kernel of the
physical seven-opening profile map. If \(m\le1\), the joint profile and
model map has rank at most eight, because its physical projection has
rank at most seven. Subtract ideal evaluations from the physical
profiles. The five ordinary bush profiles give independently every
ideal monomial and zero secondary defect, so the joint rank is
exactly five plus the dimension of the secondary defect space.

The secondary defects vanish at the origin and at the pure FSAL. Set
\(\boldsymbol d=A\boldsymbol c-\boldsymbol c^2/2\).
It is nonzero isolated at the second row, so the projection of the
secondary space onto the four physical rows \(3,4,5,6\) has dimension
at most two. Indeed the second clock \(e\) cannot be zero, or the row
duplicates the origin. The third clock cannot be zero either: \(C(2)\)
then forces zero tap to the starter, which again duplicates the origin.
One may therefore normalize the six clocks to \(0,e,1,r,s,t\).
A literal duplicate may be merged into its earlier equal padded row
by adding the two incoming-column coefficients in every remaining row,
and adding their output weights. All rooted profiles are preserved
by chronological induction. This is impossible in an order-five
six-row opening by the [uniform strict-stage floor](../../lean/RKCert/UniformERK.lean).

Let \(C=\operatorname{diag}(\boldsymbol c)\) and define
\[
 \boldsymbol F=A\boldsymbol c^2-\boldsymbol c^3/3,\quad
 \boldsymbol V=A\boldsymbol d,\quad
 \boldsymbol G=A\boldsymbol c^3-\boldsymbol c^4/4,\quad
 \boldsymbol W=A\boldsymbol V.
\]
These four plus \(C\boldsymbol F,C\boldsymbol V\) are actual secondary
tree combinations of size at most five. In the rest of the low-stage
proof all spans refer to their projections onto rows \(3,4,5,6\).

The six-stage order-five weights have \(b_2=0\) by the isolated
\(\boldsymbol d\) condition. Both \(\boldsymbol F,\boldsymbol V\)
are killed by \(\boldsymbol b^\top\) and \(\boldsymbol b^\top C\).
On the four entries these functionals are independent, since otherwise
the output is supported at only one other clock and the origin;
the square of their node hull gives a nonzero integral in degree four.
If \(\boldsymbol F,\boldsymbol V\) were independent, their span would
equal the common kernel and contain their \(C\)-multiples, hence be
\(C\)-invariant. Thus \(\boldsymbol b^\top C^2\) lies in the span of
the two functionals, and every active site off the origin is a root
of a single monic quadratic. A rational degree-four rule with at most
three sites including the origin is impossible: normalize to horizon
one, and integrate \(X(X-a)(X-b)\) and its product with \(X\).
Both integrals must vanish, giving \((5(a-b))^2=6\).
This also treats smaller supports by padding their node hull.

So \(\boldsymbol F=\lambda\boldsymbol V\), with
\(\lambda=-2+4/(3e)\) at row three because \(V_3=-e/4\).
Let \(T_i=e a_{i2}\). The altered cubic read has argument \(2e/3\)
at the starter instead of \(e^2\), and \(c_j^2\) at other columns;
it gives \(c_i^3/3\). In particular
\(T_4=r^2(3-2r)/2\), \(a_{43}=r^2(r-1)\).
The cases \(r=0,1\) make literal duplicate rows and are impossible.

## If \(\boldsymbol V,C\boldsymbol V\) are independent

The projected space is their span. It cannot have \(r=3/2\), since
\(V_4=(C\boldsymbol V)_4=0\) but \(W_4=a_{43}V_3\ne0\).
Comparing their values at the third and fourth rows gives
\[
  W_i=\frac{c_i-1}{3-2r}V_i,\qquad
  G_i=\left(\frac1e-2e+\frac{(r-1)(c_i-1)}{e(3-2r)}\right)V_i.
\]
For row five write \(T=e a_{52}, U=a_{53}, J=a_{54}\). Its
second moment, altered cubic, and last two relations give
\[
\begin{split}
 T+U+rJ&=s^2/2,\\
 (2/3)T+U+r^2J&=s^3/3,\\
 (3-2r)(U+r^2(3-2r)J)&=2(s-1)T,\\
 (3-2r)(U+r^3J-s^4/4)+(3-2r+(r-1)(s-1))T/2&=0.
\end{split}
\]
The augmented determinant is
\(r s^2(r-1)(r-s)^2(2r-3)(s-1)/2\).
Thus \(s=0,1,r\) without assuming a nonzero three-row minor.
The first two give exact duplicates even at their singular minors
(\(r=1/2,-1\), respectively). At \(s=r\), the new row also duplicates
row four unless \(r=2\). The exact replay checks each specialization.

The remaining clocks are \(0,e,1,2,2,t\), with \(t\notin\{0,1,2\}\)
by the anchored three-site obstruction. For row six replace \(J\)
by the aggregate coefficient to the two clock-two rows. Its second,
altered cubic, and \(\boldsymbol G\) equations yield a system with
determinant \(2-t\), whose starter tap is \(T_6=t^2(2-t)/2\).
The actual order-five equation
\(\boldsymbol b^\top(C-2I)\boldsymbol V=0\) implies
\(w_1+t^2(t-2)^2w_t=0\), where \(w_1,w_t\) are the order-five
scalar masses at clocks 1 and \(t\).
The nodal degree-four condition gives
\(15t(\xi-2)^2=\xi(12\xi^2-45\xi+40)\); in particular \(\xi\ne2\).
The two cardinal integral formulas substitute into the weighted
equation to give
\(\xi^3(3\xi^2-15\xi+20)/15=0\).
The quadratic has discriminant \(-15\), a contradiction.

## If \(\boldsymbol V,C\boldsymbol V\) are dependent

Since \(V_3\ne0\), \(\boldsymbol V\) is supported at clock one. Then
\(V_4=0\) implies \(r=3/2\), and \(W_4\ne0\) makes
\(\boldsymbol V,\boldsymbol W\) a spanning pair.
Rows three and four give
\(\boldsymbol G=(1/e-2e)\boldsymbol V+\boldsymbol W/(2e)\).
The fifth-row moment system is now
\[
 T+U+(3/2)J=s^2/2,\quad
 (2/3)T+U+(9/4)J=s^3/3,\quad
 T/2+(9/8)U+(27/8)J=s^4/4 .
\]
Its solution has \(T=s^2(2s-3)^2/2\). If \(s\ne1\), then
\(V_5=0\) forces \(T=0\); thus \(s\in\{0,1,3/2\}\).
In each case the exact solution duplicates an earlier row. This
finishes the contradiction to \(m\le1\).

## Chronological obstruction

For any missing model \(f\), the primitive
\(Jf(X)=\int_0^X f(u)\,du\) vanishes at \(0,\xi\).
The derivative \(f\) also vanishes there, by the actual origin
and FSAL profiles. The second primitive zero comes from the six
order-five output coefficients, which annihilate the missing physical
vector. Thus \(Jf\in X^2(X-\xi)^2\mathcal P_1\). Since \(m\ge2\),
these primitives span that entire two-dimensional space.

Take the first high clock outside \(\{0,\xi\}\), if one exists.
The missing sources vanish on all old stages and on all high
predecessors (whose true values are \(f(0)\) or \(f(\xi)\)).
Hence its incoming combination vanishes. By local purity it must
equal \(Jf\) at the new clock, which contradicts the attainable choice
\(Jf=X^2(X-\xi)^2\). Therefore all high clocks are at \(0,\xi\).
The final output support cannot even pay scalar degree four.

Escapes include a different, non-\(C(2)\) low opening, high purity
only through size five, or final weight on rough old stages.
No conclusion about those architectures follows.

## Replay

From the repository's ai-generated directory:

    python -B research/erk10-seven-opening-pure-high/audit.py
    sha256sum -c research/erk10-seven-opening-pure-high/sha256.txt

From ai-generated/lean:

    lake env lean RKCert/ReviewedNative/ERK10SevenOpeningScalars.lean

Lean 4.36.0 checks the three named scalar theorems
`fifth_clock`, `weighted_last_clock_impossible`,
and `anchored_three_clock_square` with only standard axioms.
The rank and physical arguments above are mathematical, not claimed
as native all-tableau results.
