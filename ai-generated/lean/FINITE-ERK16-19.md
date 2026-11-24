# Finite characteristic-zero ERK endpoints at orders 16 through 19

This source supplement targets the strongest established finite endpoints at
orders 16, 17, 18, and 19, respectively 24, 26, 27, and 29 stages. It does not
search for tableaux or assume distinct numerical clocks, ordered fields, or
positive and nonzero weights. Here q is 8 or 9, the achieved order is 2q+ε,
and ε is 0 or 1.

## Actual equality charts

An assumed stage count at most 3q+2ε−1 forces equality, a live last output
weight, exact forward defect ranks in grades 5 through q, and exact midpoint
and preceding ranks of 2q+1 and 2q−1. Clock multiplication is not invariant
even at the true midpoint (the physical incoming Hermite gain is too large).
OneEscape gives an invariant core and a normalized single head with at
least two paid powers in grade five. It does not assume a dimension for
grade four.

The three parity/reverse-seed cases can be treated without deleting or
changing a tableau row. Mark the terminal coordinate line exactly in the
odd case with zero affine backward seed, and add it to both forward
spaces. This line is an ideal for pointwise products, is killed by A, and
is invisible to the actual reverse hull. Its clock is 1 in the marked case.
The honest order probes then give either ordinary zero moments or moments
that differ by zero, since the unknown contribution from the marked
coordinate is independent of the moment index.

At the escaped midpoint, the exact short rational moment packets classify
the nodal polynomial alias. In the full even and full odd cases there is
no alias. In the marked case any alias has exactly degree q and lies in the
single line x times the (q−1)-st derivative-mesh polynomial. The first
band therefore has polynomial part of degree a=q, or a=q−1 only for that
marked alias. The first escaping polynomial G has degree a+1.
Using true affordable reflected primitives, the reverse gain is three
at the midpoint and two at later one-unit steps. This forces the exact
forward bands through grade p−3 and enough numerical head sites to
interpolate uniquely. The rank of the band part gives separation from
polynomial degree at most a.

## Leakage, algebra and physical knots

At grade 10, the remainder of a polynomial-plus-band decomposition is
either zero, a one-dimensional polynomial packet, or a two-dimensional
marked packet. Comparing three actual consecutive clock shifts modulo the
true polynomial G kills all three remainders. No generic sign or
orthogonality hypothesis enters: the exact rational row combinations in
ERKFinitePackets and ERKFiniteShifts are checked directly in Lean.

For each invariant core element, localize to a numerical clock and
multiply by any grade-five defect. These products and their two shifts
have grade at most 10, so leakage removal and the number of numerical
head sites put every localized product back in the core. This makes the
core a coordinatewise algebra and permits subtracting an actual core
element to make the head physically disjoint from the whole core.
All 2r−1 grade-ten shifts of its square are paid by products of the r
grade-five head powers. The generic multiplier-degree theorem gives a
polynomial P of degree at most four that equals the head on its support.
The first escape gives a literal factorization P | G by comparing their
values on more numerical head sites than the degrees allow. In the alias
case the top head coefficient in G is necessary, which improves the
degree of P to at most three.

The two literal masks are x and x(x−u). In either case remove from the
polynomial vector its core-supported part and the corresponding weighted
head. The residual has a first nonzero stage, which lies off both supports.
All affordable clock-polynomial multiples of that residual still receive
zero from the strictly causal A at that row. The actual defect of the
formal primitive has no support there, so every affordable primitive
test vanishes at that same knot. The two knots u,v are nonzero and distinct,
P is nonzero at both, and both are roots of G. This does not assume a
last-active head or a simple/repeated distribution of the numerical sites.

## Exact terminal gates

For q=9 the genuine tests are four at the first knot and three at the
second. The generic characteristic-zero Jacobi gate rules out P. For q=8
there are three and two. For a cubic the generic cubic gate suffices.
In the even and live-odd quartic charts the roots belong to the published
fixed Lobatto/right-weight meshes. In the marked no-alias quartic chart,
the only possible normalized exception satisfies 15(v/u)^2−24(v/u)+10=0.
The tested quartic has nonzero intercept at that ratio, so the actual
cofactor G/P has three distinct roots 0,u,v. After removing them its
degree is two. Rescaling yields the exact polynomial fit for the
published free-parameter Jacobi pencil gate, with no real-root argument or
root splitting. The scalar gate then forces P=0, contradicting the
physical head.

## Reproduction and reuse

The sole proof dependencies are Lean and Mathlib v4.36.0. From this directory:
```sh
lake build RKCert.ExplicitFiniteERK16to19
lake env lean FiniteERK16to19Audit.lean
lake env leanchecker RKCert.ExplicitFiniteERK16to19
```

The proof reuses the existing project-level rooted-tree conditions, grade
separation, forward and reverse Hermite, OneEscape, native primitive,
mask/coordinate-algebra, fixed-knot, free-pencil, and char-zero transfer
APIs. In particular it uses Mathlib `Submodule.finrank_sup_add_finrank_inf_eq`,
`LinearMap.finrank_range_of_inj`, `Polynomial.ofFn`,
`Polynomial.eq_of_degrees_lt_of_eval_finset_eq`,
`Polynomial.dvd_iff_isRoot`, `Polynomial.natDegree_comp_le`,
and `Polynomial.funext`; no parallel polynomial or finite-dimensional
framework is defined. Degree-specific row certificates are exact rational
linear combinations, not a second solver or a numerical search.
