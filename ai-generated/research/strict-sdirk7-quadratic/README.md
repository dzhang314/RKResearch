# Exact nine-stage strict SDIRK7 over a quadratic field and 19-power rings

There is a nine-stage strict SDIRK tableau of **exact order seven**
over Q(√432969), with common diagonal **1/4**. Both real square-root
choices work. The radicand is a positive nonsquare integer
(658² < 432969 < 659²), so this is an explicit *degree-two* coefficient
field, not just existence over the real algebraic numbers.

The same tableau specializes to **every nonzero commutative ring in
which 19 is nilpotent**, without assuming the ring is a field, local,
or reduced. Combining with the independent
[eight-stage exclusion over F19](../strict-sdirk7-eight-stage-face/README.md)
gives **minimum nine at every positive power Z/19^k**, and for other
rings in the nilpotent-19 class that admit a unital map *to* F19.
The lower proof's native and mathematical/exhaustive components remain
distinct. This does not prove a lower bound for extensions merely
containing F19, or existence over Q or Z[1/5040].

- [Explicit rational-pair tableau](nine-stage-quadratic.json), with all
  pairs in the basis (1,ρ), ρ² = 432969.
- [Native Lean proof](../../lean/RKCert/Research/SDIRKNineStageOrderSevenQuadratic.lean):
  `exists_exact_quadratic`, `exists_exact_of_nineteen_nilpotent`, and
  `exists_exact_mod_power` use the reviewed `HasOrder` without adding
  a chart hypothesis to the theorem.
- `python3 construct-quadratic.py` reconstructs the scalar clocks and
  exact linear solves. `python3 check-quadratic.py` independently
  checks all 85 trees and exactness in the quadratic field and checks
  the reductions for both roots modulo 19 and the first 12 powers for
  root 4. Both scripts need only the Python standard library.

## Why the 19-primary specialization works for all k

The separate stage and output scales obtained by clearing all pair
denominators are coprime to 19. The eighth bush has factorial-scaled
payment

    2729092071773/2734296566848 + (35828299/6835741417120) ρ.

Subtracting one and clearing its denominator gives the numerator
−26022475375 + 71656598 ρ, whose norm is −1545982860640624199651,
also coprime to 19. Consequently the defect cannot become zero in
any nonzero target ring with 19 nilpotent: the product of the defect
numerator and its conjugate is a unit there. Modulo 19 the exact
payment is **6 at ρ=4** and **17 at ρ=15**, not 1.

The parameter has the simple root 4 modulo 19: 432969 ≡ 4², and
the derivative 2·4 is a unit. If a = 4+19t and a²−432969 = 19^k v
at k ≥ 1, take a' = a − 12·19^k v. Since 8·12 = 1 mod 19, the
new difference a'²−432969 is divisible by 19^(k+1). This is
the explicit induction in Lean. The scales and norm are units at
every finite level by coprimality with every power of 19. In an
arbitrary nilpotent-19 ring, pick a power 19^k that vanishes and
transport from its cyclic coefficient ring. No incompatible
choice of finite tableaux is needed.

The same root recurrence gives a compatible sequence and therefore
a root in the 19-adic integers; the three scales remain units there.
This also gives an exact nine-stage method over Z_19 and Q_19, with
minimum nine over Z_19 using its residue map. This additional
19-adic corollary is mathematical; this Lean module certifies the
quadratic specialization and every finite power, not the completed
19-adic rings. There is no lower claim over the field Q_19 here.

## Construction: weaken the two reverse rows

Normalize by γ = 1/4 and use the three hidden helpers with clocks
(1,2,3), all strict helper taps one. Their doubled quadratic defect
is exactly the coordinate x. At grade three the hidden defects
span x and x²; one no longer has to make both extra reverse rows
integrate every cubic. In the six-stage tail, impose:

1. Quadrature through degree six and the first adjoint bB=b(4−x).
2. A second row r=bCB integrating the weighted primitive x·Jf
   through degree four. Here C is the diagonal matrix of tail
   clocks and J is the primitive starting at zero.
3. Bx=Jx and exact primitive action under the rows bC² and r on
   x² and g=x³−6x²+11x−6 only. The polynomial g vanishes on
   the three helpers.

In reflected time y=4−x, take the first two tail clocks 2,−1
and the last two u,1. Set F₂=(y−2)(y+1), h=(y−1)(y−u),
k=−(y²−4y+2)/2. The two extra reverse combinations H,K subtract
their values at the last two stages, so they are read only at the
first four. On a polynomial that vanishes at the first two, H(B−I)
and K(B−I) can read only the fourth physical stage. In particular take
f=F₂(34−10y), the reflected polynomial in the span of x,x²,g with
this vanishing. If T=J−I in reflected time, P=I((Th)f),
Q=I((Tk)f), and W=Pk−Qh, then the chronological bridge and the
quadrature equations give L₁²=L₀L₂ with Lᵢ=I(yⁱ W F₂).
Here the scalar mean on [0,4] is I(yⁱ)=4ⁱ/(i+1).

This quadratic has nonzero scalar multiple
248477u²−906502u+355613. Select
u=(453251−520ρ)/248477. The two remaining reflected clocks follow
as y₃=L₁/L₀ and
y₄=I(yh F₃)/I(h F₃), where F₃=(y−y₃)F₂.
The linear system then has rank 15 on the 15 strict entries of B.
Three feed moments determine each tail row's helper entries.
This explains the discovery and reconstruction only: the proof
replays all reviewed rooted equations on the resulting tableau.
