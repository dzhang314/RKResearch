# Why characteristics 241 and 255919 are not exceptions

A common-diagonal lower-triangular tableau of classical order six needs at
least **seven** stages over every nonzero commutative ring of characteristic
241 or 255919. No order, positivity, diagonal unit or nonzero-weight premise
is required. Neither prime can be removed merely by checking that the
existing four obstruction constants are nonzero: in both characteristics a
constant actually vanishes. The new argument uses physical information not
present in the original scalar elimination.

**Native statements:** [scalar chart projections](../../lean/RKCert/Research/SDIRKSixResidualCharts.lean)
and [literal-stage and ring obstructions](../../lean/RKCert/Research/SDIRKSixResidualExclusions.lean).
All computations below are in the indicated characteristic, not approximate
real-root computations. In particular the exclusions survive arbitrary
field extension.

For a six-stage candidate with common nonzero diagonal γ over a field,
write z=1/γ, T=zA, c=T1 and g=Tc−c²/2. Stage indices in this note start
at 1. The existing equality and chronology arguments give

    c = (1, 1+u, 1+2u, X, z−1−v, z−1),

with one undetermined physical clock X at stage 4. The original integer
receipts force the degree-twelve scalar branch in both characteristics.
Its monic polynomial Q(z) and its equations hTwelve=vTwelve=0 determine
u=v=U(z), where U has degree at most 11. Modulo Q, substituting U into
the terminal polynomial (241) or the kappa polynomial (255919) produces
a common divisor precisely z−2 or z−47708, respectively. The other
alternative is excluded by the surviving original multiplier. Horner
remainders and a final Bézout identity are checked as polynomial identities
in an arbitrary coefficient field of that characteristic. The forced triples
are (z,u,v)=(2,82,82) and (47708,250912,250912).

Let I(P) denote the functional on polynomials of degree ≤5 determined by
I(x^j)=z^j/(j+1). The actual bush conditions give I(P)=∑ bᵢP(cᵢ).
Consequently, if P vanishes at the other active clocks, the two paid
moments satisfy b₄P(X)=I(P) and b₄XP(X)=I(xP). If I(P) is nonzero,
these determine X even without any sign assumptions. The argument needs
both support and degree; it would not follow from the scalar polynomials alone.

* **Characteristic 241.** Outside the unknown stage, the physical clocks
  are 1,83,165,160,1. The monic polynomial with distinct roots 1,83,165,160
  is P=x⁴+73x³+40x²+99x+28. Its moments are I(P)=201, I(xP)=13, so X=78.
  The saturated clock and collapsed cubic equations give twice the physical
  defect (2gᵢ)=(1,189,172,172,189,1); the last entry uses the terminal
  ratio and does not divide by any output weight. These values also equal
  2H(cᵢ) for H(x)=27+49x+133x²+204x³+190x⁴. Therefore ∑ bᵢgᵢ=I(H)=225,
  contradicting the paid quadratic defect condition ∑ bᵢgᵢ=0.
* **Characteristic 255919.** Here 1+2u−u²=0 and c₆=47707≠1. The
  saturated identity (c−1)g=(1+2u−u²)(T−I)g forces g₆=0. The weighted
  seed proportionality at equality and the nonzero terminal weight then
  imply b₁g₁=0. Since g₁=1/2, b₁=0; this is **derived**, not assumed.
  Besides X only 250913,245906,52714,47707 can now contribute. Their
  monic nodal polynomial has coefficients, in descending order,
  (1,−85402,39326,28077,66467). Its two moments are 158780 and 225071,
  forcing X=57721. Finally the monic polynomial with roots
  250913,245906,57721,52714 has integral zero but takes the nonzero value
  233129 at c₆=47707. Thus b₆=0, contradicting terminal chronology.

The established quadratic lower bound rules out fewer than six stages.
The ring conclusions follow from residue-field specialization and the
existing explicit bound when the diagonal specializes to zero. The
seven-stage rational tableau has denominators invertible in these
characteristics and supplies the matching upper bound.
