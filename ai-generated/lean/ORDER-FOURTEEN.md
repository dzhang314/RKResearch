# Strict explicit order 14 requires 21 stages in characteristic zero

The ordered-field bound of 21 was already known. This kernel proof removes
the ordering assumption, strengthening the previous characteristic-zero
field and commutative-ring floor from 20 to 21. Strict lower triangularity
and the actual rooted-tree order conditions are its only tableau hypotheses.
Weights may be signed or zero; clocks may repeat or be exterior.

## Saturated chart and leakage

An assumed stage count at most 20 forces exactly 20, a live last output
weight, exact defect ranks in grades 5–7, and full forward ranks 13,15
at grades 6,7. Use the common midpoint construction, whose structural
proof actually applies at half order q≥6. The even terminal column belongs
to E7, its clock is 1, and F7 vanishes there. The first clock escape is
one-dimensional, with actual stable core U and head w. At least r≥2 of its
powers lie in F5. The escape plus P7 is a direct sum, from the exact
terminal-zero moment packet: the only possible mesh polynomial has degree
8, and is proportional to x(1−x) times the shifted Legendre derivative of
degree 6. The reverse rank gains force exact expansions through E11; the
last two ranks give at least r+6 different effective head clocks.

In grade 10 the possible polynomial leak has two scalar coefficients.
All three polynomial components in a consecutive triple vanish by two
multiplication-by-x congruences modulo the literal mesh G. The two exact
rational identities use no ordered Gram hypothesis. Localize grade-five
products to a single clock, use the triple to place each product back
in the head-plus-core chain, and use the effective clock count to force
the localized product into U. Thus U is a coordinatewise algebra. After
subtracting an actual core column via its support indicator, w is physically
disjoint from U. All 2r−1 shifts of w² are affordable grade-ten products and
have no leakage. Dividing on the head and using polynomial uniqueness gives
a nonzero head polynomial P with deg P+r≤6.

## Causal tests and the terminal quartic factor

Every multiplier of polynomial degree at most r on w is affordable
through grade 6 (r paid head powers in grade 5, plus one clock shift).
Subtract the core mask and the corresponding head multiplier from a true
polynomial profile through grade 6. The first nonzero residual stage lies
outside both supports. It receives zero from A applied to every affordable
test multiple, and the grade-seven primitive difference, being in the
actual chart, also vanishes there. This gives true primitive moments at
that one clock. With r≥3, masks x and x(x−u) produce the standard 3+2 tests
of the cubic or lower head, an impossibility.

At r=2, the genuine terminal column has polynomial profile a·x·D6 for
nonzero a, where D6 is the fixed normalized derivative of the shifted
degree-seven Legendre polynomial. On the head, its representation in F7
forces a literal polynomial factorization by P; the cofactor has degree
at most 3 and the number of clock sites exceeds the product degree. Hence
deg P=4. If P(0)=0, test P/x using masks 1 and x−u; the same 3+2 tests then
fit the grade-six budget. Otherwise P divides D6. A mask x then produces
a single zero primitive moment at u=1 or at a root of D6 off P. The exact
fixed-divisor gate rules out both choices. It eliminates the two literal
monic quadratic cofactor coefficients by rational unit identities checked
in Lean. A splitting field, a lift from unsupported modular experiments,
and ordering of mesh roots are unnecessary.

The characteristic-zero ring statement uses the existing
`explicit_of_charZero_fields` transfer; no quotient-field assumption on the
input ring is introduced. The ordered-field statement is a specialization.

## Independent reusable ordered ingredients

`OrderedMomentGram` proves exact positive Cauchy forms by a Schur-square
identity and diagonal rescaling, and thereby proves positivity of the
formal integral of x^k P² at 1 for every nonzero polynomial over an ordered
field. It assumes no positivity of RK weights. `OrderedIntervalMoments`
adds native polynomial affine substitution, positive formal integrals of
squares on arbitrary increasing intervals, and a directly usable anchored
polynomial-defect separation test. These independently checked ingredients
are included for the remaining ordered-endpoint work; the characteristic-zero
order-14 endpoint above does not depend on them.

## Reproduce

From the Lean project directory, using the pinned Lean and Mathlib v4.36.0:
```sh
lake build RKCert.ExplicitOrderFourteen RKCert.OrderedIntervalMoments
lake env lean OrderFourteenAudit.lean
lake env leanchecker RKCert.ExplicitOrderFourteen
```

Mathlib finite sums, native polynomial
evaluation/degree/divisibility, finite-dimensional rank, and existing
project chart and causality theorems are reused.
