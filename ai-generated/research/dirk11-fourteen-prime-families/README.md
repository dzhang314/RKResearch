# Fourteen-stage DIRK of exact order eleven in 68 prime families

The [literal 14-stage real-algebraic tableau](../dirk11-width14-real-reflected-shell/README.md)
also supplies an exact-order-eleven method over the p-adic integers for
the 68 primes in [the seed table](seeds.json), beginning with 113.
It supplies the same upper bound over every nonzero unital commutative
ring of characteristic p^k for those primes, with no restriction on
k≥1. More generally the bound holds in every nonzero commutative
ring of finite characteristic supported on those primes. This is an
**upper** bound of 14, not an exclusion of 13. The [characteristic-43
tableau](../dirk11-width14-f43-reflected-shell/README.md) is a separate
construction, not included in those 68 families.

There is also an extension-field bound: the same coefficient export
gives exact order eleven in 14 stages over the field with p^8 elements
for every prime p not dividing the full denominator D displayed in
[the exact replay](exact-replay.log). This does not assert existence
in its prime subfield or minimality over the extension.

## Coefficient rings and exact order

Let D₀ be the common denominator of the four quadratic relations,
the literal A and b, and the recorded scaled twelfth-order defect.
Let D be the lcm of D₀ and the denominator of the exported inverse of
that defect. Work first over Z[1/D₀]. The successive monic quadratic
quotients form a free module with the sixteen squarefree monomials
as its basis. The natural map to its rational base change is injective.
Thus the checked rooted-order identities and the literal expression
for the defect descend to this localized integral tower. Inverting D
instead also descends the identity certifying the inverse. The defect
is the size-twelve tree with four leaf children and a size-seven bush:
84 times the weighted outer stage derivative, minus one. Showing
it is a unit is enough to show exact, rather than merely at-least,
order eleven over every nonzero target ring.

For each p in the seed table, D₀ is prime to p and the four quadratic
roots have nonzero successive derivatives modulo p. Lift them in
order, one precision digit at a time. At precision p^k, after lifting
earlier coordinates, the current monic polynomial F has F(t)≡0
modulo p^(k−1) at the old root. The unique correcting digit is
−(F(t)/p^(k−1))/F′(t) modulo p, computed before reducing beyond
precision p^k. This explicitly produces compatible roots for all k
and hence in Z_p. Specialization gives the tableau and the rooted
identities. The defect is already nonzero in the residue field, so
it is a unit at every higher precision and in Z_p. At p=709 this
argument deliberately does not use the exported inverse: D is
divisible by 709 but D₀ is not. Direct replay gives defect 519 modulo
709. Every nonzero ring of characteristic p^k receives the canonical
map from Z/p^k; for finite characteristic with multiple listed prime
factors, combine the literal coefficient arrays by the Chinese
remainder isomorphism first. Units and equations transfer under these
unital maps.

For the extension-field assertion, the first root is a square root
of 15 and may be taken in the field with p² elements. The next two
radicands both depend only on this root, so take both square roots
in the field with p⁴ elements. The final monic quadratic splits
over the field with p⁸ elements, including if it has a repeated
root. The homomorphism from the tower with D inverted sends the
exported defect inverse to an actual inverse. Simplicity or a
separately verified field-degree search is not needed for this claim.

## Replay

Run `python3 -B check.py` in this directory. It pins the full source
JSON by SHA-256, evaluates the unscaled Butcher weight recursion and
the tree densities independently of the original normalized replay,
and checks every root and all 3,047 rooted conditions for each of
the 68 prime and prime-square tableaux. It also checks prime cubes
and fifth powers for 113 and 709. The size-twelve defect is a unit
in every checked specialization. For example at p=113 the defect
is 43 modulo p and 382 modulo p². The two general transfers use the
mathematical tower argument above; the finite replay is not a
Lean formalization of the all-powers or extension-field assertions.
