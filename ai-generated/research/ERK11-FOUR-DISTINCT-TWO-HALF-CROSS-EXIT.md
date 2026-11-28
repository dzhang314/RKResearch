# Four distinct calibrations: the two calibrated halves cannot both cross in the free-extra diagrams

**Scope.** Continue the four-distinct part of the
[nonzero-mass eight-clock atlas](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md).
Assume the left extras are \(\{e,t\}\) and the right extras
are \(\{h,t'\}\), where \(t,t'\) are free active labels, possibly
equal. Assume both half labels \(h,e\) are ordinary pairs
(not the triple). Since each half is read on both fronts,
both are crossing pairs. This excludes both choices \(t'=t\)
and \(t'\ne t\) in characteristic zero.
It does not cover a triple at one of those halves, or a
diagram which uses the opposite **plateau** as an extra.

## 1. Scaled quadric contact and the half crossover

Use \(h=a/2,\ d=1-b,\ e=1-b/2\). The actual monic free
quadratic is \(X^2+(A/\Delta)X+B/\Delta\), with
\[
 \Delta=m_0m_2-m_1^2,\quad A=m_1m_2-m_0m_3,\quad
 B=m_1m_3-m_2^2 .
\]
The previously checked assumptions give \(D=0,\ \Delta\ne0\),
where \(D\) is the 3-by-3 Hankel determinant from the
four-calibration hull \(P_4\). Write \(Y=\Delta t\);
the scaled monic quadratic is \(Y^2+AY+\Delta B\).
Let \(Y'=Y\) if \(t'=t\) and \(Y'=-A-Y\) if \(t'\) is the
other free clock.

The inverse mixed-Gram contact has factors \(\ell,r\)
from the ordinary left and reflected extras. Multiply each
by \(\Delta\) to obtain
\[
 \begin{split}
 L_0&=(a-e)(\Delta a-Y), & L_1&=-eY,\\
 R_0&=(h-d)(Y'-\Delta d), & R_1&=-(1-h)(\Delta-Y').
 \end{split}
\]
The paid off-diagonal pairing of actual rows 7 and 11
says \(L_0R_0+T_4(a)L_1R_0+T_4(b)L_0R_1+
U_{4,4}(a,b)L_1R_1=0\) at the actual scaled free root.
The nonzero prefactors of that gate are those of the
both-new fronts: the two sixth and seventh clocks differ
from each other, the corresponding half, plateau and
origin. It only uses genuine grade-five anchored rows in
the mixed forward/weighted-transpose Gram.

Reduce this polynomial modulo the scaled monic quadratic,
writing its remainder \(u+vY\). Then its norm
\[
 C=u^2-Auv+\Delta Bv^2
\]
vanishes in either diagram, since the product of the two
conjugate evaluations has the actual zero factor.

Separately the pair crossover relation gives
\(\Xi(h)=\Xi(e)\) on the two ordinary half crossing pairs.
As in the [same-free-pair exit](ERK11-FOUR-DISTINCT-SAME-FREE-PAIR-EXIT.md),
construct \(\widehat\Xi=\Delta\Xi\) from
\(\widehat H=P_4(\Delta X^2+AX+B)\), formally using the
divided difference and the scalar moments.
Then
\[
 E=\frac{\widehat\Xi(h)-\widehat\Xi(e)}{h-e}=0
\]
is a polynomial equation in \(a,b\). The polynomial
division is exact identically; the canceled \(h-e\) is
nonzero on the four-distinct chart. Both compared pair
clock weights and all response scales are genuinely live,
by the earlier pair and endpoint calculations; no
third-response equality is used here.

The two norm polynomials \(C\) (for the two choices of
\(Y'\)), the crossover \(E\), \(D\), and \(\Delta\) are all
symmetric in \(a,b\), checked coefficientwise by exact
symmetric expansion. Reflection swaps the half labels and
the front roles, and exchanges free roots as needed, which
explains why the two contact norms (not each unsymmetrized
root evaluation) are symmetric. The crossover numerator
and denominator transform compatibly.

## 2. Projection plus a complete check of its exceptional fibers

Put \(S=a+b,\ T=ab\), and use integer primitive
coefficient polynomials. For each contact norm the
\(T\)-resultant with \(D\) has degree 156 in \(S\), and
the corresponding crossover resultant has degree 36.
Any actual common \(T\) makes both vanish, even on a
degree-drop fiber. Their gcd has only two irreducible
factors, of degrees 4 and 10, each once. These factors
are not discarded because they happen to occur in a
guard resultant.

For each of the two factors and each of the two diagrams,
the exact quotient-coefficient Euclidean calculation of
\(\gcd_T(D,C,E)\) yields a monic linear polynomial that
divides \(\Delta^2\). The replay computes this divisibility
directly in the coefficient quotients; every inverse used
there is a unit. Hence any actual common pair \(S,T\)
would give \(\Delta=0\), contrary to its proved nonvanishing.
This pays the exceptional fibers for both same-free and
different-free choices, not just a generic projection
argument.

The [standalone Python replay](erk11-four-distinct-two-half-cross-exit/replay_four_halves.py) checks the exact
resultants and all four fiber implications with SymPy.
No numerical root sample or separate Lean replay of the
large elimination is claimed.
