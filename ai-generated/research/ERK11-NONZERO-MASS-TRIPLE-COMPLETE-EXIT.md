# The four remaining ERK11 nonzero-mass one-cross layouts are impossible

**Scope.** Continue the
[thirteen-active, six-label eight-clock atlas](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md):
the maximal all-live two-total-carrier ERK11 chart, both seventh
boundaries genuinely new, pooled first response zero at each label,
and nonzero ordinary mass on the unique triple. This excludes the
last four-distinct-calibration one-cross geometries over
characteristic-zero fields. Together with the previous packets,
it closes the **whole nonzero-mass thirteen-active chart**, not
the twelve-active six-pair chart or the ordinary 17-stage ERK11
problem. No ordering assumption or reverse order eleven is used.

## 1. The literal remaining diagrams

Use left plateau and half \((a,h=a/2)\), right plateau and
half \((d=1-b,e=1-b/2)\), with all four distinct, and free
labels \(t,u\). Call a pair crossing if one physical occurrence
is on each front. Relative to the earlier completed overlaps
and two-cross diagrams, the remaining one-cross diagrams, up to
reflection and free-root names, are
\[
\begin{array}{c|c|c|c|c}
 \text{left extras}&\text{right extras}&\text{triple }p&
  \text{cross pair}&\text{inner clock multiset}\\ \hline
 \{e,t\}&\{t,u\}&e\text{ or }t&
   \text{the other of }e,t&\{p,h,u\}\\
 \{t,u\}&\{a,h\}&a&h&\{t,u,e\}\\
 \{t,u\}&\{a,t\}&a&t&\{h,u,e\}\\
 \{e,u\}&\{a,t\}&a&e&\{h,u,t\}.
\end{array}
\]
Each chosen clock is an actual active label. Every inner
multiset counts occurrences, not just distinct nodes. For
each fixed triple choice the physical 24 schedules are the
two orders of two extras on each front (which is sixth or
seventh) and the six inner permutations. Neither a reverse
ordinary order-eleven assumption nor arbitrary physical
stage reindexing is used.

## 2. Exact width projection and all low-degree guard factors

Use the full calibrated hull \(P_4=(X-a)(X-h)(X-d)(X-e)\).
For \(m_j=\int X(1-X)P_4(X)X^j\,dX\) put
\[
 D=\det(m_{i+j})_{0\le i,j\le2},\quad
 \Delta=m_0m_2-m_1^2,\quad
 A=m_1m_2-m_0m_3,\quad B=m_1m_3-m_2^2 .
\]
The actual Hankel equation is \(D=0\); the **proved-live**
minor is \(\Delta\ne0\). The scaled free roots \(Y=\Delta t\)
and \(\bar Y=\Delta u=-A-Y\) form the monic quadratic
\(Y^2+AY+\Delta B\).

For two extras with scaled clocks \(y,z\), the two left
contact factors are \(((\Delta a-y)(\Delta a-z),-yz)\).
The right factors are \(((y-\Delta d)(z-\Delta d),
-(\Delta-y)(\Delta-z))\). These are the actual derivative
row factors multiplied by \(\Delta^2\). If a front
chooses both free roots one may instead multiply its
two factors by just \(\Delta\): on the left use
\((a^2\Delta+aA+B,-B)\) and on the right
\((d^2\Delta+dA+B,-\Delta-A-B)\).
For the corresponding four factors form
\[
 C_{\mathrm{raw}}=L_0R_0+T_4(a)L_1R_0+
                  T_4(b)L_0R_1+U_{4,4}(a,b)L_1R_1 .
\]
It vanishes at the actual selected free root by the
exact off-diagonal row-7/row-11 inverse mixed Gram
contact. Take its quadratic norm if it depends on one
selected free root. In the second diagram the contact
already depends only on the widths because the left
choice is both free roots and the right two are known.
Remove only exact powers of \(\Delta\) and nonzero
constant coefficient content. The resulting primitive
polynomial \(C(a,b)\) must vanish.

Eliminate \(b\) by the exact subresultant sequence of
\(D,C\), **without** symmetrizing the widths. Its last
nonconstant member is a line \(L(a)b+R(a)\), a
polynomial combination of the two inputs by the
shifted-row cofactor construction. Thus it holds at
any actual finite common \(b\), independent of any
specialized input degree drop. The resultant and factor
degree/multiplicity data are:
\[
\begin{array}{c|r|l}
 \text{diagram (top to bottom)}&\deg_a \operatorname{Res}_b&
 \text{factor degrees with multiplicity}\\ \hline
 1&252&1^{12},4^3,6^2,20^3,156\\
 2&108&1^{6},4,6,20,72\\
 3&252&1^{12},4^3,6^2,20^3,156\\
 4&216&1^{12},4^2,6^2,20^2,144 .
\end{array}
\]
The degree-one factor is \(a\), invalid by the width
guard even though the projection line can degenerate
there. On the degree-4, degree-6 and degree-20 factors,
the exact rational coefficient computation makes \(L\)
a unit. For the degree-6 factor it forces \(b=0\).
For each of degrees 4 and 20 it forces \(\Delta=0\),
checked by clearing the evaluated powers of \(L\) in
the polynomial \(\Delta(a,-R/L)\). These are actual
same-\(b\) fiber implications, not discarded merely
because of a guard projection. Only the respective
degree \(156,72,156,144\) factor remains.

## 3. Live finite free coefficient algebras

For each remaining factor make it monic over
\(\mathbb Z_{(101)}\), using its checked unit leading
coefficient modulo 101. In the mod-101 scalar coefficient
algebra, both \(L\) and the Hankel \(\Delta\) at \(b=-R/L\)
are units by exact polynomial gcd. Their multiplication
determinants therefore lift to units over
\(\mathbb Z_{(101)}\), so \(b\) and the unscaled free
quadratic coefficients \(A/\Delta,B/\Delta\) are defined
there. This permits **every** actual coefficient evaluation
at a root of the retained factor. No unknown tableau is
itself specialized modulo a prime.

In the second diagram leave \(t\) as a root of this monic
free quadratic and recover \(u\) by trace. The algebra is
then finite free of rank \(72\cdot2\) over
\(\mathbb Z_{(101)}\); it retains both free label choices.
In the other diagrams insert the actual choices of front
extras (and \(u=-A/\Delta-t\)) into the **unscaled**
first contact \(\Psi\), and reduce modulo the free
quadratic. Its remainder \(V_0+V_1t\) has \(V_1\) a unit
modulo 101 in the full scalar coefficient algebra, checked
by Euclid. It lifts as a unit, so actual evaluation forces
\(t=-V_0/V_1\), and trace forces \(u\).
The replay checks that the forced \(t\) satisfies the
free quadratic also in the exact mod-101 replica.
Thus the actual free-root role is identified, not guessed
from a norm of an unlabeled pair.

## 4. The 120 physical second contacts

Use the \(\Phi,D_w,E_w\) construction from the
[mixed one-cross proof](ERK11-MIXED-OVERLAP-ONE-CROSS-EXIT.md).
Each actual grade-four clock-square vector is zero
through physical row 7 of its own orientation, since
both seventh boundaries are genuinely new. Its literal
primitive is therefore zero through row 8. Subtracting
that primitive model makes the adjusted read through
these rows a model plus the quadratic response correction,
with the independent fifth pure correction killed by the
literal plateau reads. The actual row 7 is a live
multiple of \(\Phi_L\); row 8 is in
\(\operatorname{span}\{D_{c_8},E_{c_8}\}\).
The actual reflected rows 11 and 10 give the corresponding
right statements. All pairings here are between actual
degree-at-most-five rows in the known forward/weighted-
transpose mixed Gram, never a reverse pure square.

At a repeated left clock, the earlier response and row-8
response cannot coincide: on the adjusted anchored lift
equal states would make row 8 zero or duplicate row 7,
contrary to the measured middle invertibility. This works
even for a triple label. The two readings thus isolate
\(D_{c_8}\) in the span of actual rows 7 and 8, giving
\(\langle D_{c_8},\Phi_R\rangle=0\).
The reverse repeated-clock argument gives its mirror.
When the two side contacts are unrepeated, their
3-by-3 pairing determinant must vanish because two
independent actual rows on each side are orthogonal.

In the first diagram, for each \(p=e,t\), there are 16
left repeats (\(c_8=p,h\)); four right repeats
(\(c_8=u,c_{10}=p\)); and four remaining determinants.
In the other three diagrams the first two listed inner
labels \((t,u)\), \((h,u)\), or \((h,u)\) are left repeats,
giving 16 schedules. The other eight in each diagram are
determinants. The coefficient replay checks all 120
such vanishing conditions are units modulo 101.
For the diagram retaining a free quadratic, use the
extra quadratic norm to the scalar algebra before its
polynomial gcd. No modular irreducibility is required.

Each unit lifts by its multiplication determinant in the
fixed finite free basis over \(\mathbb Z_{(101)}\).
Any actual characteristic-zero tableau would give a
unital evaluation of this algebra with the corresponding
second contact zero, impossible. This excludes every
diagram in the table.

## 5. Completeness of the nonzero-mass thirteen-active chart

The eight-clock atlas excludes endpoint collisions and
leaves only the three possible calibration overlap types
or four distinct calibrations. The
[mixed two-cross](ERK11-MIXED-OVERLAP-TWO-CROSS-EXIT.md),
[mixed one-cross](ERK11-MIXED-OVERLAP-ONE-CROSS-EXIT.md),
and [half-half](ERK11-HALF-HALF-OVERLAP-EXIT.md) packets
exclude all overlaps.

For four distinct calibrations without an opposite plateau
chosen as an extra, the left extras come from \(\{e,t,u\}\)
and the right from \(\{h,t,u\}\). Up to reflection and swap
of the free names the possible two-subset pairs are:
* \(\{t,u\}\mid\{t,u\}\), excluded by the
  [two-cross](ERK11-FOUR-DISTINCT-SAME-FREE-PAIR-EXIT.md)
  and [one-cross](ERK11-FOUR-DISTINCT-SAME-EXTRAS-ONE-CROSS-EXIT.md)
  exits.
* \(\{e,t\}\mid\{h,t\}\), excluded by the
  [two-half](ERK11-FOUR-DISTINCT-TWO-HALF-CROSS-EXIT.md) or
  [half-triple](ERK11-FOUR-DISTINCT-SELECTED-FREE-HALF-TRIPLE-EXIT.md)
  exits.
* \(\{e,t\}\mid\{h,u\}\), similarly by the two-half exit or
  [different-free half-triple exit](ERK11-FOUR-DISTINCT-DIFFERENT-FREE-HALF-TRIPLE-EXIT.md).
* \(\{e,t\}\mid\{t,u\}\), by the
  [asymmetric two-cross exit](ERK11-FOUR-DISTINCT-ASYMMETRIC-TWO-CROSS-EXIT.md)
  or diagram 1 above.

If an opposite plateau is chosen, the triple is at that
plateau, and two opposite choices are impossible. Reflect
so that \(a\) is chosen on the right. If the other right
extra is \(h\), the two left subsets up to swap are
\(\{t,u\}\) and \(\{e,t\}\). If the other right extra is \(t\),
the left subset is \(\{t,u\}\), \(\{e,t\}\), or \(\{e,u\}\).
The [opposite-plateau two-cross exit](ERK11-FOUR-DISTINCT-OPPOSITE-PLATEAU-TWO-CROSS-EXIT.md)
excludes the two with two crossing pairs. The other
three are diagrams 2–4 above. This exhausts the chart
without a generic distinct-free-order assumption.

Thus no nonzero-mass triple remains over characteristic zero.
The separate
[zero-mass triple exit](ERK11-ZERO-MASS-TRIPLE-ONE-CROSS-EXIT.md),
with its earlier cross-pair reduction, closes that scalar
mass case over ordered fields. Together they exclude
thirteen active rows in this six-label zero-first-response
branch over ordered fields. The twelve-active six-pair
case and other ordinary ERK11 charts remain open.

The [standalone Python replay](erk11-nonzero-mass-triple-complete-exit/replay_four_remaining_onecross.py) rebuilds
every exact coefficient, performs the projection and unit tests
without approximate parameter parsing, and needs only SymPy
(NumPy is optional for exact bounded-integer multiplication).
The large final elimination does not claim a separate Lean
replay; the earlier clock and mixed-contact scalar receipts
are independent.
