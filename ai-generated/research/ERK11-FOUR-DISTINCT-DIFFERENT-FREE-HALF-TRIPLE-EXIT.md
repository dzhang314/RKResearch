# Four distinct calibrations: no different-free half-triple one-cross layout

**Scope.** In the nonzero-mass four-distinct chart, suppose the
left extras are \(\{e,t\}\) and the right extras \(\{h,u\}\),
with **different** free labels \(t,u\). The
[two-half crossing proof](ERK11-FOUR-DISTINCT-TWO-HALF-CROSS-EXIT.md)
excludes both halves ordinary. This excludes the remaining
case with one half the triple, over characteristic zero.
The other four-distinct one-cross extra geometries are not
covered and no ordinary ERK11 bound changes.

## 1. Exact projection and physical chronology

There are two shared clocks \(h,e\), so if one half \(p=h,e\)
is the triple, the other is the unique crossing pair. The
three middle slots 8–10 have the clock multiset \(\{p,t,u\}\):
the triple needs its third occurrence, \(t\) its unseen
right partner, and \(u\) its unseen left partner.
There are 24 chronologies for each triple choice (two
left sixth choices, two reversed sixth choices, six inner
permutations).

Use \(D,\Delta\) from the four-calibration Hankel and the
first-contact quadratic norm \(C\) of the two-half packet
for **different** free choices. This contact equation uses
only the actual both-new anchored grade-five pair at rows 7
and 11; the crossover condition of that packet is not used.
With \(S=a+b,T=ab\), the exact \(T\)-resultant of \(D,C\)
has degree 156 and factors of degrees/multiplicities
\[
 (4,3),\quad (6,2),\quad (10,6),\quad (72,1).
\]
Its last nonconstant subresultant is a linear polynomial
\(L(S)T+R(S)\), a polynomial combination of the two
inputs and thus zero at every actual common finite root.
Direct exact arithmetic in the degree-4 and degree-10
quotients proves \(L\) a unit there and \(\Delta=0\) on
\(T=-R/L\). On the degree-6 quotient it gives \(T=0\).
Those three fibers are thereby ruled out by actual
nonzero pivots/widths, not merely by generic resultants.

## 2. The degree-72 coefficient algebra forces the free labels

Make the degree-72 factor monic over \(\mathbb Z_{(101)}\).
Its leading coefficient retains degree mod 101, and
\(L\) is a unit in the scalar quotient mod 101, checked
by polynomial Euclid. Invert \(L\) by the finite free
multiplication adjugate and put \(T=-R/L\).
Then adjoin \(a\) by its monic quadratic
\(a^2-Sa+T=0\), and set \(b=S-a\). Both width orientations
are retained. The Hankel minor \(\Delta\) is a unit in
the mod-101 width algebra by quadratic norm and
polynomial gcd, so it is a unit in the rank-144
width algebra over \(\mathbb Z_{(101)}\).

Use the Cramer coefficients \(q_1,q_0\) of the unscaled
monic quadratic \(X^2+q_1X+q_0\) for the free labels.
The actual left free label \(t\) and right free label
\(u=-q_1-t\) meet the **underlying** first contact,
not just its norm. In the formal monic free quadratic
the exact contact remainder is \(A+Bt\). Its coefficient
\(B\) is a unit in the full width algebra mod 101
by the same quadratic norm criterion. Thus it lifts
as a unit over \(\mathbb Z_{(101)}\), forcing
\(t=-A/B\) and \(u=-q_1-t\) for any actual evaluation.
This chooses the correct root for the labeled front;
checking the contact norm alone would not identify it.

## 3. Exact second contacts

The actual grade-four clock-square vectors vanish through
the seventh row at each local front when the boundary
is new. Their literal primitive vanishes through the
eighth. Hence the second-contact construction from the
[mixed one-cross packet](ERK11-MIXED-OVERLAP-ONE-CROSS-EXIT.md)
applies without a shifted or synthetic tree condition.
Left row 7 is a nonzero multiple of \(\Phi_L\), row 8
lies in \(\operatorname{span}\{D_{c_8},E_{c_8}\}\),
and the reverse analogues occur at physical 11 and 10.
All degree-five pairings are in the established forward
order-eleven mixed Gram with the order-ten weighted
transpose, not any reverse pure square.

If \(c_8=p,t\) it repeats a left clock. This permits a
triple repetition: equal response values would make the
adjusted anchored row 8 either zero or duplicate row 7,
contradicting the actual invertible middle read matrix.
So \(D_{c_8}\) lies in the span of the actual rows 7,8
by their nonzero response difference, and it must pair
to zero with \(\Phi_R\). This covers 16 schedules for
each \(p\).
If \(c_8=u,c_{10}=p\), the reverse repeated-contact
constraint covers four more. If \(c_8=u,c_{10}=t\),
the two left and two right independent actual rows force
the three-by-three contact determinant zero, covering
the final four.

All 48 of these vanishing conditions are instead
**units** in the computed width algebra modulo 101:
for each first and reversed sixth choice, and each
middle permutation in both triple choices, take the
quadratic norm to the scalar modulus and a polynomial
gcd. The mod-101 width algebra is finite free and need
not be a field. Its nonzero multiplication determinant
lifts to a unit over \(\mathbb Z_{(101)}\), so a
characteristic-zero tableau cannot evaluate the forced
gate to zero. This is a coefficient-algebra calculation,
not reduction of an unknown tableau.

The standalone `replay_four_different_half_onecross.py`
checks the exact projection, all unit pivots and every
schedule using SymPy. No separate Lean replay of this
large elimination is asserted.
