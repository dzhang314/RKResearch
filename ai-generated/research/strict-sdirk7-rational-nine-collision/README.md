# Rational strict SDIRK7: repeated tail clocks and the reduced curves

This is an exact **subclass exclusion**, not an exclusion of all
nine-stage strict methods over Q. It also does not settle the
integer-localized upper bound.

## 1. No repeated clock in the six-active-stage, paid-head chart

Take a rational triangular nine-stage tableau of reviewed order seven
with common diagonal γ≠0. Assume the last six weights are all nonzero.
If the first three coordinate columns belong to the grade-four pure
defect space, then the six tail clocks are **pairwise distinct**.
A sufficient head condition is three distinct helper clocks, a nonzero
quadratic primitive defect at each helper, and zero quadratic defect
on every tail row. In particular this applies to the rank-two helper
families used in the [quadratic construction](../strict-sdirk7-quadratic/README.md).
No extra pointwise adjoint assumption, choice of γ, ordering of clock
values, or positivity of weights is needed.

The native theorem from the actual reviewed `HasOrder` is
`RKResearch.Certified.SDIRKSevenTailCollision.distinct_tail_of_headPaid`
and the ready-to-use quadratic-clean version is
`distinct_tail_in_seed_chart` in
[SDIRKSevenTailCollisionIngress.lean](../../lean/RKCert/Research/SDIRKSevenTailCollisionIngress.lean).

**Proof.** Work initially in physical coordinates with clock vector
c=A1. Write (u=bA, v=(bC)A, C=operatorname{diag}(c)). The head
defect assumption forces all three head entries of b, u and v to
vanish: apply their paid order budget to each head coordinate column.
Full reviewed order shows (u-b(1-c)) and (v-b(1-c^2)/2) have
zero moments through degrees five and four respectively. For example
the underlying primitive probe is
[
  (b C^k)A c^j = rac1{(j+1)(j+k+2)}
  quad (j+k+2le 7).
]
The rational grouped quadrature floor gives at least five active sites.
If any tail clocks coincide, there are exactly five distinct sites,
one twin pair and no cancellations. Evaluating the degree-four
cardinal product of all other clock factors proves each of the two
errors sums to zero on every fibre.

If the final stage is a singleton, its two grouped equations force
(1-c_9=gamma) and ( (1-c_9^2)/2=c_9gamma), hence
(gamma^2=0). Otherwise let its twin be stage i<9. The first error
row can differ from zero only by a multiple of the twin contrast.
It annihilates every actual grade-at-most-five pure defect:
bA reads one primitive extension, and b(1−c) reads a linear
combination of two clock probes. If the contrast is nonzero, the two
twins therefore agree on every such defect. In particular they agree
on A applied to each head coordinate column, so their head taps agree,
and on the primitive defects ((j+1)A c^j-c^{j+1}), j≤4.
Their row difference vanishes on the head and its tail moments
through degree four vanish, so its sum on every clock fibre is zero.
If i is not penultimate, applying this to the penultimate singleton
forces (A_{9,8}=0). If i is penultimate, applying it to the repeated
fibre forces the same result by the common diagonal. Thus the last
(singleton or twin-aggregate) two chronological equations again
imply (gamma^2=0).

If the first error row is zero pointwise, (c_9=1-gamma). An
adjacent pair with (c_8=c_9) gives (A_{9,8}=0) immediately by
the penultimate first row, with the same contradiction. Otherwise
the penultimate stage is a singleton. Its first and second grouped
equations eliminate (A_{9,8}), giving
[
 ((1-c_8)-2gamma)^2=2gamma^2,
]
impossible over Q. For the sufficient head condition, apply the
two clock-difference operators for the other helper clocks to
the quadratic defect. The result singles out the chosen helper and
is an actual pure defect of grade at most four.

## 2. Necessary curve equations for the relaxed distinct-tail chart

Normalize the common diagonal to 1, write (z=1/gamma), B for the
six-tail block, J for the primitive based at 0, and
(I(x^k)=z^k/(k+1)). Three-helper AP designs use two hidden low-degree
directions and the helper node polynomial g. With actual quadratic
and cubic purity on the tail, the relaxed chart asks the rows
(bC^2) and (r=bCB) to integrate only the relevant defect span,
rather than every cubic. The exact first adjoint (bB=b(z-C))
also follows in the paid-head, distinct-tail chart by degree-five
interpolation of its first error row.

For the two literal helper families below, the ordered physical
tail has last normalized clock (z-1). Reflect to the clock
(y=z-x); write u and 1 for the last two reflected values,
(y_1=z-a,y_2=z-d) for the first two, and
(F_2=(y-y_1)(y-y_2)). Define
[
 h=(y-1)(y-u),qquad k=-(y^2-4y+2)/2,qquad T=J-mathrm{Id}.
]
The rows (H=b,h(y)) and (K=r-b,ell(x)) vanish at the final
two physical slots, where (ell) is the affine interpolant of
(r_i/b_i) at those slots. Their paid densities on degree-four
tests are h and k (the reflected density of r is
((z^2-x^2)/2) before subtracting (ell)).

For each branch choose a polynomial f in the paid reverse defect
span which vanishes at the first two tail clocks. The two rows
read (H(B-I)f=I((Th)f)), (K(B-I)f=I((Tk)f)). The normalized
head contributes nothing to these tests: on helper-germ profiles
it is an advance of an actual pure defect in budget, and the remaining
profile is the node polynomial vanishing on the head. Since (B−I) is
strictly triangular, these two readings only see the fourth tail slot.
Put (P=I((Th)f), Q=I((Tk)f), W=Pk-Qh), and (L_j=I(y^j W F_2)).
The single-slot bridge implies (I(W(y-y_3)F_2)=0);
degree-four quadrature gives
(I(W(y-y_4)(y-y_3)F_2)=0). Consequently
[
 L_1^2=L_0 L_2
]
with no division by any (L_j). This expression is quadratic in u.
It is a **necessary** scalar condition; a rational point on a listed
curve still has to pass reconstruction and rank tests.

### Linear-seed helpers (1,2,3), origin as first readout

Use all helper lower entries equal to one, so the quadratic helper
defect is x. Cubic cleanliness gives (Bx=x^2/2). Its first
active row has a=0 or 2. In the a=0 branch, the second row also
forces d=0 or 2, hence d=2 by the collision theorem. Use f=F₂.
The discriminant of the primitive quadratic in u is
[
   4 z^4 (z^4-24z^3+180z^2-480z+360)^2,P_6(z),qquad
   P_6(z)=z^6-30z^5+405z^4-3190z^3+14400z^2-31500z+25725.
]
The quartic factor has no rational zero: it is monic integral, and
has no root modulo 13. The sextic is squarefree, so the affine
rational-point problem is a genus-two curve. **No rational u is
possible for any nonzero integral reciprocal diagonal z.** Indeed,
with t=z−5, complete the square:
[
 P_6(t+5)=(t^3+15t-45)^2-(1050t^2-2100t-2450).
]
For (|t|ge600), the subtracted quantity is strictly between zero
and (2|t^3+15t-45|-1), putting the value strictly between
consecutive squares. For (|t|le600), the 1201 integer evaluations
are all nonsquares. A rational square root
of an integer is integral. The
[Lean scalar module](../../lean/RKCert/Research/SDIRKSevenZeroFirstCurve.lean)
certifies the discriminant, finite check, square-gap inequalities, and
nonexistence for the displayed moment equation. The causal bridge
from the chart to those explicit scalar moments is the mathematical
argument above. Nonintegral rational z is not covered.

### Linear-seed helpers (1,2,3), first readout 2, z=4

Here (V=langle x,x^2,x^3-6x^2+11x-6angle) and take
(f=F_2(2d(4-y)-6)). The generic necessary square class is
(3G_8(d)), where the integer coefficient list of (G_8) in
descending degree is

    [24500,-490700,3876985,-15297290,31600324,-33601568,18747248,-5240640,580032].

The discarded square factor besides a constant square is
((35d^2-209d+105)^2), whose quadratic has no rational zero.
The octic is squarefree, so this is a genus-three curve. The
existing quadratic witness has d=5; it does not give a rational
point of the curve.

### Constant-seed helpers (1,3,5), first readout 1, z=4

Use all helper lower entries equal to two. Their doubled quadratic
defect is 1, and the paid reverse span is
(V=langle1,x,x^3-9x^2+23x-15angle). Take
(f=F_2(4-y-8+d)). The generic necessary square class is
(H_8(d)), where the descending coefficients are

    [86975,-2030350,18454725,-82924460,194230660,-230935520,129356480,-28040704,2052352].

This octic is squarefree (genus three). The removed squared factor
is (((7d-48)(7d-8))^2). At either of its two roots the
chronological quadratic forces (u=59/27), but the two quadrature
tests (I(hF_4)=I(kF_4)=0) force a quadratic for the remaining
two reflected clocks with discriminant
(-854814911/1190043009) at (d=48/7) and
(54545409/5276209) at (d=8/7). Neither is a square in Q, so
both degenerate cases are rejected exactly.

Run `python3 check-curves.py` with SymPy for independent
polynomial arithmetic, the finite integer list, and both degenerate
cases. No bounded rational scan is used as a nonexistence proof.
The two literal helper families are not exhaustive; for example,
AP spacing (22/31) also admits a rational first active clock 11
for its primitive seed equation. No nine-stage rational witness or
unconditional rational nine-stage exclusion is claimed.
