# Four distinct calibrations: excluding both opposite-plateau two-cross diagrams

**Scope.** Continue the four-distinct part of the
[nonzero-mass eight-clock atlas](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md).
Suppose one front chooses the opposite plateau as an extra,
and there are two crossing ordinary pairs. This excludes
the resulting two diagrams (and their reflections) over
any characteristic-zero field. Opposite-plateau one-cross
layouts and other four-distinct geometries remain open.

## 1. Actual two-clock middle support

Reflect the polynomial clock and mixed Gram systems if
needed so the right front chooses the left plateau \(a\).
It has two left occurrences and this one right occurrence,
so \(a\) is the triple. The other plateau \(d=1-b\) is
therefore an ordinary pair entirely on the right. Let
\(t,u\) denote the two free labels. Since the four
calibrations \(a,h,d,e\) are distinct, two ordinary
crossing pairs are possible only in the following ways:
\[
 \begin{array}{c|c|c|c}
 \text{left extras}&\text{right extras}&
    \text{crossing pairs}&\text{inner labels}\\ \hline
 \{e,t\}&\{a,h\}&h,e&\{t,u,u\}\\
 \{e,t\}&\{a,t\}&e,t&\{h,u,u\}.
 \end{array}
\]
Indeed the only left extra labels allowed are \(e,t,u\).
If the other right extra is \(h\), there must be a left
occurrence of \(e\) to have a second crossing. If the
other right extra is \(t\), there must be left occurrences
of both \(e\) and \(t\). The inner multisets follow from
the literal pair and triple occurrence counts.

Use the actual forward/reverse grade-four square-clock
vectors \(V_L,V_R\), whose model product is
\[
 W(X)=X^2(X-a)^2(1-X)^2(X-d)^2 .
\]
Their numerical product is supported only on physical
rows 8,9,10 because both seventh boundaries are new.
If the two inner labels are \(y,z\), multiplication by
\((C-yI)(C-zI)\) kills it, and \(4+4+2=10\) pays
\[
 \int_0^1 W(X)(X-y)(X-z)\,dX=0.
\]
Write \(I_j=\int_0^1 X^j W\) for \(j=0,1,2\).
This is entirely a grade-four mixed support argument
with two clock factors, not an extra grade-five square
or ordinary reverse order eleven.

## 2. Clock polynomials with all pivots kept

Use the four-distinct Hankel determinant \(D=0\),
independently live pivot \(\Delta\), and Cramer numerators
\(A=m_1m_2-m_0m_3\), \(B=m_1m_3-m_2^2\).
The monic free quadratic is \(X^2+(A/\Delta)X+B/\Delta\).
For the first diagram the two inner labels are the
two free roots. Its support equation is simply
\[
 E_0=\Delta I_2+A I_1+B I_0=0.
\]
For the second diagram, \(y=h,z=u\); the linear
polynomial
\[
 E_g(Y)=\Delta(I_2-gI_1)+Y(g I_0-I_1)
\]
vanishes at \(Y=\Delta u\) for \(g=h\).
Take its norm in the monic scaled quadratic
\(Y^2+AY+\Delta B\). Use the product of the norms for
\(g=h,e\) so the reflected diagram is included. In both
cases the resulting support polynomial is symmetric
in the widths \(a,b\). Only exact factors of the
proved-live \(\Delta\) and nonzero scalar content are
removed. No moment centroid is divided by a denominator.

For the first contact \(\Psi\) use the actual extras
\(\{e,t\}\) on the left and \(\{a,r\}\) on the right,
with \(r=h\) or \(r=t\) according to the diagram.
Let \(Y=\Delta t\), and set \(Y_r=\Delta h\) or \(Y\),
respectively. The four factors multiplied by \(\Delta\)
are
\[
 \begin{split}
 L_0&=(a-e)(\Delta a-Y),& L_1&=-eY,\\
 R_0&=(a-d)(Y_r-\Delta d),& R_1&=-(1-a)(\Delta-Y_r).
 \end{split}
\]
The paid row-7/row-11 inverse Gram equality gives
\(L_0R_0+T_4(a)L_1R_0+T_4(b)L_0R_1+
U_{4,4}(a,b)L_1R_1=0\). Thus its norm in the free
quadratic vanishes. Multiply that norm by its width
reflection to get a symmetric necessary polynomial,
covering both orientations, and strip only proved-live
\(\Delta\) powers and scalar content. This introduces
no assumption about actual reverse order eleven: the
off-diagonal equality is the known mixed Gram with
both actual grade-five rows.

## 3. Exact projection and all exceptional fibers

In \(S=a+b,T=ab\), the resultants in \(T\) of \(D\)
with the contact norm and support polynomial have
respective degrees \(180,36\) for the first diagram and
\(216,108\) for the second. In the first diagram their
gcd has one degree-4 and one degree-10 factor, and
in the second it has the same degrees with multiplicities
one and two. These are necessary at every common
finite root, including specialized degree drops.

For each factor in each diagram, the exact fiber
calculation in \((\mathbb Q[S]/g)[T]\) gives a monic
linear polynomial that vanishes at any actual common
\(T\) and divides \(\Delta^2\). The receipt takes the
gcd of \(D\) and the lower-degree support gate, adding
the contact to the gcd only if needed. Thus it checks
polynomial divisibility at the actual same \(T\), not
only a projected root of a guard resultant. Every Euclidean pivot inverted in
these coefficient quotients is checked as a unit.
An actual layout would therefore have \(\Delta=0\),
contradicting its independent proof of nonvanishing.
No other fibers have been discarded.

The [standalone Python replay](erk11-four-distinct-opposite-plateau-two-cross-exit/replay_four_opposite_two_cross.py) checks
the polynomial constructions, both resultant gcds, and
all four exact residue-fiber implications in SymPy.
These are exact mathematical eliminations, not a
numerical sample or an additional Lean replay.
