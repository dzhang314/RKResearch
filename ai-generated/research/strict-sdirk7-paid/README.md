# A single ten-stage strict SDIRK7 over every paid ring

A single literal tableau of **exact classical order seven** and ten
physical stages works over every nonzero commutative ring in which
7! = 5040 is a unit. Its common diagonal satisfies 4γ=1. This improves
the coefficient-ring scope of the earlier two-witness upper bound:
no selection between tableaux, local-ring structure, or extra
denominator unit is needed. It does not change the eight-stage lower
bound, close the possible rational nine-stage gap, or improve the
nine-stage real-algebraic upper bound.

* [Literal integer numerator tableau](ten-stage-paid.json)
* [Native Lean certificate](../../lean/RKCert/Research/SDIRKTenStageOrderSevenPaid.lean)
* [Exact linear reconstruction](construct-paid.py) and
  [independent 85-tree replay](check-paid.py), both using only the Python
  standard library

The stage and weight scales are, respectively,
4,423,680 = 2¹⁵·3³·5 and 52,920 = 2³·3³·5·7².
Both divide (7!)⁴. The order-eight bush does **not** witness exactness
(it is paid). Instead use the two actual rooted trees:

1. A unary stem above a root with a leaf child and a five-vertex bush
   child. Its eighth-order payment is 631/576.
2. Three successive unary stems above a five-vertex bush. Its
   eighth-order payment is −5/96.

Both would have payment one at order eight. In integer numerator
form, if both were paid, the common scale Ω would satisfy
−55Ω=101Ω=0. Since 6·101−11·55=1 and Ω is a unit, this would make
the coefficient ring zero. The argument therefore proves **exact**
order seven after every allowed specialization. The order-seven tall
tree conversely requires 5040 to be a unit for any order-seven tableau.

## Reconstruction

Use the three-helper and seven-readout linear chart in the
[earlier construction](../strict-sdirk7/README.md), but change the
helper quadratic defect. In normalized time z=4 the three helper clocks
are (1,6,0), with normalized lower triangular rows

    [1,0,0], [5,1,0], [-8/5,3/5,1].

Twice the quadratic defect at the helpers is P(c₀) for P(x)=4−3x.
Use tail clocks (4,0,8,2,−4,1,3) with signed scalar quadrature weights.
The tail block B now obeys B P(c)=(J P)(c), where J is zero-origin
integration; the three feed equations are
U1=c−B1, Uc₀=c²/2−Bc, and Uc₀²=c³/3−Bc². The new relation gives
U P(c₀)=0. The original first adjoint and the two further low-moment
rows are otherwise unchanged. The exact linear solve needs only
ordinary rational row operations and free variables set to zero.
The native checker and independent replay verify the result directly.

## Why different clocks were needed

Pivot freedom alone cannot clear every extra prime on the two earlier
fixed-clock charts. In normalized diagonal-one form the first adjoint
condition on the penultimate column gives exactly

    b_last B_last,penultimate = b_penultimate (c_last−c_penultimate).

The older z=5 and z=4 rows force that particular entry to be −159/1585
and 7/837, respectively. Their reduced denominators contain 317 and
31. No change of free variables or pivots in those same charts can
remove those factors. This is conditional on the fixed clocks,
quadrature, and first adjoint equations, not on all ten-stage tableaux.

More generally, for a fixed chart with all its linear-equation
coefficients in Z[1/5040], clear row denominators by units and take
integer Smith form. An exact solution over Z[1/5040] exists if and
only if the transformed right side is zero on all zero rows and each
nonzero Smith entry divides the transformed right side after
localization. Thus a bad prime in one rational elimination is not
itself a proof of obstruction; an actual divisibility failure is.
