# Ten strict SDIRK stages of exact order seven

Two new rational tableaux need **ten** physical stages, improving the
previously verified rational upper bound of eleven. Both have one common
nonzero diagonal. Together they give the same upper bound over **every
nonzero commutative local ring in which 7! is a unit**, including all
fields that can support these order conditions. This is not a lower bound:
the general eight-stage floor and the nine-stage real-algebraic upper
bound are unchanged.

| Tableau | Common diagonal | Extra denominator primes, beyond 7! | Eighth bush payment |
|---|---:|---|---:|
| [First](ten-stage-rational.json) | 1/5 | 11, 23, 53, 317 | 109436/109375 |
| [Complement](ten-stage-rational-alt.json) | 1/4 | 31, 37 | 449/448 |

The JSON arrays are literal integer numerators with separate common
stage and weight denominators. Native Lean:
[first tableau](../../lean/RKCert/Research/SDIRKTenStageOrderSevenRing.lean),
[complement](../../lean/RKCert/Research/SDIRKTenStageOrderSevenAltRing.lean),
[local-ring selection](../../lean/RKCert/Research/SDIRKTenStageOrderSevenLocal.lean).
The three modules passed Lean/Mathlib 4.36.0. From `ai-generated/lean`, run `lake build RKCert.Research.SDIRKTenStageOrderSevenLocal`. The reviewed `HasOrder` checker uses every ordered tree; the
[independent replay](check-ten-stage.py) uses the 85 unordered rooted
trees through order seven. Run `python3 construct-ten-stage.py` to
reconstruct both matrices from small linear systems, then
`python3 check-ten-stage.py` for an independent exact check.

## Coefficient scope and exactness

Each tableau specializes over any nonzero commutative ring in which its
stage denominator is a unit. The two weight denominators divide powers of
the respective stage denominator. The selected diagonals satisfy,
respectively, 5γ=1 or 4γ=1 in these rings. For the first tableau the
eighth bush discrepancy is 61/109375 and the eighth tall discrepancy is
−7371296909/11207109375, whose numerators are coprime. This proves exact
order seven even if the eighth bush alone could become paid. For the
complement, the bush discrepancy 1/448 is already a unit.

The two stage denominators d₅=13255661380500 and d₄=2913563520 satisfy
196151 d₅−892416183 d₄=11340, and 11340 divides (7!)². In a local ring a
sum of nonunits is a nonunit. Thus at least one stage denominator is a
unit, and its tableau works there. This does not select a tableau over an
arbitrary ring with only 7! invertible: in Z[1/5040] both denominators are
nonunits. That failure of this portfolio is not a proof that ten stages
are impossible over Z[1/5040].

## Discovery: a three-helper and seven-readout linear chart

Scale by z so that the common diagonal equals one, and use normalized
time on [0,z] with moment functional I(x^j)=z^j/(j+1). The fixed first
three helper rows are

    [1,0,0], [1,1,0], [-2,1,1].

Their clocks are c₀=(1,2,0), and twice their quadratic defect is c₀
itself. Their output weights are all zero. Fix an ordered list c of
seven distinct tail clocks, with first clock 2 and last clock z−1,
and determine b by seven scalar quadrature equations. Write the tail
as a block (U,B), with diagonal-one lower-triangular block B.
Exponentiation of clock vectors is coordinatewise; write Lⱼ=b diag(c)^j.

Impose the row relation Bc=c²/2 and fill the three feed coefficients
uniquely by

    U1 = c−B1,     Uc₀ = 0,     Uc₀² = c³/3−Bc².

These give the exact polynomial profile of every normalized stage tree
through size four on the tail. In particular the cubic chain is exact
there because the old quadratic defect is annihilated. Impose L₀B=b
diag(z−c); quadrature implies L₀U=0. This is the full first-order adjoint
condition, even though the second-order adjoint condition cannot be
imposed literally at the last active stage.

Use r=L₁B as an extra known row. Prescribe r c^j=b c^(j+2)/(j+1)
for j=0,...,4, and its last two entries by the diagonal and the first
adjoint equation. This fixes r by a seven-row linear solve. Finally,
for each row w in {r,L₂}, impose

    w B c^j = w c^(j+1)/(j+1),   j = 0,2,3.

The remaining equations for the strict part of B are linear. Together
they give L₁U=L₂U=rU=0 and the necessary low integrations. To see why
they suffice, every root through size seven has at most one child of size
≥4. When no such child occurs, the paid tail profiles already suffice.
A single such child with no other branches is handled by the first
adjoint condition, reducing to decorated lower-child trees. With a side
branch, the only large-child cases are size four with side total one or
two, and size five with side total one. The normal size-four tail profile
is c³. A size-five stage is already pure at the tail unless the only
child has size four; in that case rU=0 and r B c³=r c⁴/4 produce exactly
the needed average. These are the displayed linear equations. Finally
divide the full matrix by z.

For the first tableau use z=5 and normalized tail clocks
(2,7,0,1,−2,6,4). For the complement use z=4 and
(2,0,1,4,−4,5,3), choosing linear elimination pivots away from
11,23,53,317. Neither construction appends a pinned Newton tail to an
order-five seed. The linear recipe explains discovery; the direct
native and independent rooted checks do not assume its sufficiency.
