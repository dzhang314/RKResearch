# Finite-characteristic extension of the fourteen-stage ERK9 portfolio

The two [exact tableaux and third-prime checks](README.md) also give
fourteen-stage exact order nine over every nonzero commutative ring
of positive finite characteristic in which 11! is a unit. The ambient
ring need not be finite or local.

Write its characteristic as m, and factor m = m₁m₂ with coprime
factors, taking m₂ to contain the full powers of 13, 19 and 47 that
divide m. The factorial-unit hypothesis makes m coprime to 11!.
The map from Z/m to the scalars of the ring transports the canonical
two complementary CRT idempotents. They split the ring as a product
of two unital factor rings (a trivial factor can be omitted), with
m₁ and m₂ acting as zero on their respective factors.

On the m₁ factor use the primary tableau: its denominator is coprime
to m₁ and its tenth bush defect is a unit. On the m₂ factor use the
second tableau: both its denominator and the numerator of its tenth
tall defect are coprime to m₂ by the checked residues. Form the
entrywise pair of the tableaux under the product decomposition.
The order conditions are polynomial and hence hold in both factors.
At least one factor is nontrivial and fails order ten, so the paired
tableau has exact order nine. The construction does not handle
characteristic divisible by 11, and does not give a single rational
tableau with only factorial primes inverted. The CRT extension is a
written argument, not a new native Lean theorem.
