# Fixed characteristic, different order-six minima

Set F = 𝔽₃₅₃₃ and E = F[t]/(t²−824t+524). The quadratic has no
root in F, so E is its degree-two field extension. In E the minimum strict
SDIRK stage count for order six is **six**. The new tableau has six nonzero
weights, its common diagonal **189 already belongs to F**, and the seventh
bush gives 1230 rather than 1.

The [literal data](quadratic3533.json) represent a coefficient as the pair
[a,b] for a+b t. [Native Lean](../../lean/RKCert/Research/SDIRKSix3533Quadratic.lean)
certifies the field, its degree, the tableau and the failure at order seven.
The [standalone replay](check-quadratic3533.py) checks irreducibility, all
37 unordered rooted trees through six and the separate seventh-order bush.

The [prime-field exclusion](../../lean/RKCert/ReviewedNative/SDIRKSixSmallCharacteristicExclusion.lean)
shows that six stages over any characteristic-3533 field require a square
root of 2077. Conversely, if x²=2077 then t=(x+824)/2 is a root of the
displayed quadratic: its discriminant 824²−4·524 equals 2077 modulo 3533.
Sending t to this root embeds E into the coefficient field and carries over
the full tableau. This classifies the six-stage endpoint over fields in
this characteristic, not just the prime field and its quadratic extension.

The [rational seven-stage tableau](../../lean/RKCert/ReviewedNative/RationalStrictSDIRKSevenStageSixUpper.lean)
has matrix denominator 1536 and weight denominator 90, both invertible
modulo 3533. Reducing its integer-scaled conditions supplies seven stages
in the other fields. Thus the difference in minima, seven over F versus
six over E, is a coefficient-field effect rather than a diagonal restriction.

For reconstruction, use the two arithmetic triples of the
[prime-field construction](README.md) at z=1645, u=t and v=824−t.
The same three independent Vandermonde equations give the missing
three-by-three block. Discovery used this chart, but the full-tree proof
depends only on the displayed tableau.
