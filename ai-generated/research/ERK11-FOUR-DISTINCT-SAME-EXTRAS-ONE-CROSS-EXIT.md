# Four distinct calibrations: no one-cross layout with the same free extras

**Scope.** Continue the [nonzero-mass eight-clock atlas](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md)
with four distinct calibrations and **both** fronts choosing the same
two free active labels as extras. The [two-cross proof](ERK11-FOUR-DISTINCT-SAME-FREE-PAIR-EXIT.md)
excluded the case where both are ordinary pairs. This proof excludes the
remaining one-cross case, where one free label is the triple. The same
free-extras geometry is now closed over any characteristic-zero field,
but not the whole four-distinct atlas or the ordinary ERK11 gap.

## 1. Exact projection, including degenerate parameter fibers

Write \(S=a+b,\ T=ab\). Use the polynomials \(D,\Delta,C\) of
the two-cross proof: \(D=0\) is the Hankel determinant, \(\Delta\ne0\)
is the proved-live two-by-two pivot, and \(C=\Delta^2\Psi=0\)
is the inverse-Gram first contact. None of these uses the local
scalar crossover equality. In particular \(C\) holds also for
the triple at one of the two free labels.

The exact \(T\)-resultant of \(D,C\) has degree 72 in \(S\).
Its factor degrees and multiplicities are
\[
 (4,1),\quad (6,1),\quad (10,2),\quad (42,1).
\]
A common finite \(T\) makes it zero even if specialized degrees
drop. The last nonconstant polynomial of the exact subresultant
sequence in \(T\) is linear, \(L(S)T+R(S)\).
A subresultant is a polynomial combination of the inputs:
this follows by the signed-cofactor construction with shifted
coefficient rows of \(D,C\), canceling the higher powers of \(T\).
Thus it vanishes at a common root without dividing by an
input leading coefficient. No promise about a generic \(T\)
degree after specializing \(S\) is used.

In the degree-4 and degree-10 coefficient quotients, \(L\)
is a unit and substituting \(T=-R/L\) into \(\Delta\) gives
zero. In the degree-6 quotient \(L\) is a unit and the same
substitution gives \(T=0\), contrary to \(ab\ne0\).
Those are explicit exact field computations in the standalone
receipt; none is inferred merely because a projection factor
coincides with an unwanted branch. Hence an actual \(S\) would
lie on the degree-42 factor.

## 2. Literal second contacts on the retained geometry

Let \(p\) be the triple free label and \(t\) the crossing
pair free label. The extras are \(\{p,t\}\) on both fronts.
The half-plateau \(h\) belongs to the left and \(e\) to the
right, with no other front occurrence. Thus the physical
middle rows 8,9,10 consist of \(\{p,h,e\}\), one each.
The 24 schedules are the two ways to place the left sixth
extra, the two ways to place the reflected sixth extra,
and the six inner permutations.

Use the polynomial functionals \(\Phi,D_w,E_w\) of the
[mixed one-cross proof](ERK11-MIXED-OVERLAP-ONE-CROSS-EXIT.md).
The actual grade-four square-clock vectors vanish through
the seventh row on each calibrated front, so their *literal*
grade-five primitives vanish through the eighth. Thus the
left row 7 is a nonzero multiple of \(\Phi_L\), and its row
8 lies in \(\operatorname{span}(D_{c_8},E_{c_8})\) after
removing its calibrated primitive model. Similarly reverse
rows 11 and 10 use \(\Phi_R,D^R_{1-c_{10}},E^R_{1-c_{10}}\).
The required first-six nonzero interpolation factors are
the distinct calibrated half, plateau and sixth clocks,
nonzero physical responses at half and sixth, and the
previous independent fifth pivot. The both-new boundaries
ensure the row-7 and row-11 derivative prefactors are live.
These are exactly the existing hypothesis guards, rather
than consequences of a speculative modular diagram.

If \(c_8=p,h\), it repeats an earlier left clock \(i\) in
row 3, 6 or 7. This includes the triple. If its response
equaled that earlier response, the adjusted anchored
row 8 would duplicate row 7 or be zero (the earlier
row 3 or 6). That is impossible by invertibility of
the actual 7–11 mixed read matrix. The two readings
\(D_{c_8}/a^5+F_i T(c_8)\) and
\(D_{c_8}/a^5+F_8T(c_8)\) thus isolate \(D_{c_8}\)
in the span of rows 7 and 8. Its pairing with \(\Phi_R\)
must be zero. This gives 16 schedules.
If \(c_8=e\) and \(c_{10}=p\), the reverse repeated-clock
argument gives \(\langle\Phi_L,D^R_{1-c_{10}}\rangle=0\)
in four schedules. In the final four, \(c_8=e,c_{10}=h\),
the two unrepeated contacts have a vanishing 3-by-3
pairing determinant: two independent actual rows on each
side are orthogonal under that pairing. All these equations
use the forward order-eleven mixed Gram with the actual
order-ten weighted transpose. No reverse fifth-grade
square or ordinary reverse order eleven is used.

## 3. Unit checks without losing a degree-42 fiber

Make the degree-42 factor monic over \(\mathbb Z_{(101)}\);
its leading coefficient is a unit as checked in the replay.
The scalar \(L(S)\) is a unit in its mod-101 coefficient
quotient by exact Euclidean gcd. Thus it is also a unit in
the rank-42 monic algebra over \(\mathbb Z_{(101)}\):
multiplication has a unit determinant there and the
adjugate gives an inverse. Put \(T=-R/L\) in this algebra.
This **retains every actual degree-42 root** and does not
assume that a rational formula sampled at selected real
roots is defined. Adjoin \(a\) with monic relation
\(a^2-Sa+T=0\), set \(b=S-a\), and compute moments \(m_j\)
through \(j=3\) from the four calibrated clocks.

The Hankel pivot \(\Delta=m_0m_2-m_1^2\) is a unit in the
mod-101 width algebra by its quadratic norm to the scalar
quotient. Consequently it is a unit in the finite free width
algebra over \(\mathbb Z_{(101)}\), not just a live pivot
at the unknown tableau. The Cramer coefficients of the free
monic quadratic are therefore defined over this ring. Adjoin
one of its roots \(p\) as the triple, and recover \(t\)
by trace. The resulting coefficient algebra has rank
\(42\cdot2\cdot2=168\) with fixed monomial basis. Its two
quadratic towers retain both width orientations and both
free-root assignments.

For each chronology the exact numerator of its second
contact is a unit in this algebra modulo 101. The replay
checks all 16 left and four right repeated-clock pairings
and four determinants: take the quadratic norm twice
and use a polynomial gcd with the scalar modulus. These
checks make no irreducibility assumption on modular factors.
The multiplication determinant of each gate is therefore
a unit in \(\mathbb Z_{(101)}\), so the gate cannot vanish
under any unital evaluation into a characteristic-zero field.
An actual tableau would supply such an evaluation and would
make that gate zero, contradiction. The finite reduction
is on an explicit coefficient algebra, not on unknown
tableau entries.

The [standalone Python replay](erk11-four-distinct-same-extras-one-cross-exit/replay_four_same_onecross.py) checks the
projection line and every algebraic unit condition exactly
with SymPy, without a numerical root sample. A separate
Lean replay of this larger elimination is not claimed.
