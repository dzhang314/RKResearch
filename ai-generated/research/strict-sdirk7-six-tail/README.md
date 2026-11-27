# Why the paid ten-stage strict SDIRK7 chart does not immediately compress

This is a **restricted chart obstruction**, not a new global stage bound.
It rules out folding to two head helpers while keeping every subsequent
stage pure through rooted size four over Q. It also rejects the
three-helper/six-active-tail version of the original linear moment solve
at the same common diagonal 1/4 as the [paid ten-stage tableau](../strict-sdirk7-paid/README.md).
For a general common diagonal, one of the two six-tail scalar branches
is ruled out over Q. No claim is made about all rational nine-stage
tableaux or all real eight-stage ones.

The [native Lean module](../../lean/RKCert/Research/SDIRKSixTailScalarObstruction.lean)
certifies the literal three-row obstruction, a clock identity, and both
exact scalar eliminations. The connection from the six-tail chart to its
explicit scalar hypotheses is the mathematical derivation below.
The [independent SymPy replay](check-six-tail.py) recomputes the
resultants, factorizations, and modular root tests exactly.

## 1. A rational third row cannot be fully pure

After dividing by the nonzero common diagonal, the first three
normalized clocks are 1, x, y. Write the third row as (a,b,1).
If it is pure through size four, the actual stage conditions give

    a+b+1=y,
    a+xb+y=y²/2,
    a+x²b+y²=y³/3,
    a+(4x−2−x²)b=0.

The last identity subtracts the quadratic-stage profile from the
twice-integrated chain. The first two stages of the quadratic defect
2Ac−c² are 1 and 4x−2−x²; the third is zero by the second equality.
Consequently the last equation reads the actual third component of
A(2Ac−c²)=0. Eliminating a,b gives y³−9y²+18y−6=0. The homogeneous
version has no projective root modulo 5, so this is impossible over Q.
The native proof derives the four scalar equations from a literal
triangular 3×3 matrix with unit normalized diagonal.

Thus a two-helper rational architecture in which every tail stage is
pure through size four cannot work, regardless of the chosen clocks,
not merely for one of the existing helper choices.

## 2. Six active tail rows: exact chronological constraints

Use the six-row tail block B, lower triangular with diagonal one.
The six active clocks c are distinct and all six output weights bᵢ
are nonzero. Time runs from 0 to z=1/γ in the normalized coordinates.
Write I(x^j)=z^j/(j+1), J for integration from 0, and C=diag(c).
The linear construction in question imposes:

* b represents I on degrees through six;
* bB=b(zI−C);
* r=bCB represents f ↦ I(x·Jf) on degrees through four;
* both bC² and r read Bf(c) exactly as they read (Jf)(c) for degrees
  through three.

These are **the chart's actual equalities**; imposing them on every
order-seven method without proof would be incorrect. The tail row
purity and feed choices are not needed for the obstruction once these
equalities hold.

The last clock is z−1 by the first adjoint equation. Reflect the
clocks to y=z−x. Write 1 and u for the last and penultimate reflected
clocks, respectively, and let

    h(y)=(y−1)(y−u),       k(y)=−(y²−4y+2)/2,       T=J−I.

Here T is the zero-origin primitive minus identity in the reflected
variable. Define two actual rows H and K that vanish at the last two
physical stages. Set H=b·h(z−c). To get K, subtract from r the row
b times the linear interpolant of rᵢ/bᵢ at those last two clocks.
The first adjoint equation and triangularity give their unreflected
interpolant (z−1)²+(2−z)x. The formal density of r is (z²−x²)/2
in the prescribed budget. Subtraction leaves precisely k(z−x).
Thus H and K represent I(hf) and I(kf) on degrees through four.
By the displayed chart identities, applying B to a polynomial
column of degree at most three integrates it exactly against either
row. In the reflected variable the ideal adjoint integration is
integration from 0, so applying B−I corresponds to the tests
I((Th)f) and I((Tk)f).

Let F₃ and F₂ be the monic polynomials through the first three and
first two physical tail clocks, respectively, in the reflected
coordinate. They vanish at those actual stages. With B−I strictly
lower triangular, H(B−I)F₃ and K(B−I)F₃ are both zero: their first
four coordinates are zero and their two remaining coordinates
are unread. Hence

    I((Th)F₃)=I((Tk)F₃)=0.

For F₂ the only possibly read coordinate of (B−I)F₂ is the fourth.
Since H₄F₃(y₄)=I(hF₃), K₄F₃(y₄)=I(kF₃), the two readings force

    I(kF₃) I((Th)F₂) = I(hF₃) I((Tk)F₂).

In particular H₀:=I(hF₃) is nonzero by distinctness and b₄≠0.
The product (y−y₄)F₃ vanishes at every coordinate either row reads.
Therefore I(h(y−y₄)F₃)=I(k(y−y₄)F₃)=0. These two bookkeeping
facts use no positivity of the weights.

## 3. Both scalar branches at gamma = 1/4

Write K₀=I(kF₃). The exact identity
y k−(2u−1)k = −2Th−Tk gives (y₄−(2u−1))K₀=0.

* **Exceptional, K₀=0.** With the ordinary Laguerre polynomials Lᵢ,
  one has k=−L₂, Tk=L₃ and Th=−L₁−(u−3)L₂−2L₃.
  Thus F₃ is orthogonal to L₁,L₂,L₃, and the penultimate bridge
  becomes I(L₃F₂)=0. Since F₂=F₃/(y−r) for the third clock r, these
  are three linear cubic-coefficient equations, a nodal root
  equation and one causal bridge. Clearing them and taking the
  cubic/quadratic resultant forces a degree-12 polynomial in z
  with no projective root modulo 11. The native proof uses a
  denominator-free Cramer and Bézout receipt and cancels only a
  nonzero constant times z⁴. This rejects the branch at **every**
  nonzero rational z.

* **Generic, K₀≠0.** The last three reflected clocks are 1,u,2u−1.
  The preceding equalities give
  D(u) K₀=(3u−5) H₀, with D(u)=u³−7u²+10u−2.
  Put Q=D(u)k−(3u−5)h. The penultimate bridge gives I((TQ)F₂)=0
  and F₃=(y−r)F₂ then gives I(y(TQ)F₂)=0. Here

      TQ = (3u−5)L₁ + (3u−5)(u−3)L₂ + (u−2)²(u−3)L₃.

  The cubic F₃ is orthogonal to L₃, L₁+(u−3)L₂ and the terminal
  hull h(y)(y−2u+1). The two displayed tests constrain F₂, and
  F₂ divides F₃. At z=4, clearing these Cramer identities and the
  linear coefficient of the division remainder forces
  −1680·(u−1)·(u²−9u+12)·P₁₂(u)=0. Distinctness excludes u=1,
  and the two other factors have no projective roots modulo 5
  and 17 respectively. This proof does not divide by either
  Cramer determinant.

The generic branch at arbitrary z is not ruled out by these results.
Colliding clocks, mixed active helper weights, or a different
second-order reverse treatment are also outside this chart.

## 4. Independent ordered-field restriction at eight stages

For any strict eight-stage order-seven tableau over an ordered field,
there can be **at most two negative weights and at least two
nonpositive weights**. Thus if every weight is nonzero, exactly
two are negative. This mathematical restriction does not assume
the tail chart above and does not exclude all eight-stage methods.

Indeed let R=CA−AC−A², whose triangular diagonal is −γ², and use the
six columns 1,c,c²,c³,R1,Rc. The first four have the nonsingular,
positive-definite Hilbert pairing under the weighted physical
product (its rational Cholesky factors work over any ordered field).
The last two are independent by invertibility of R and independent
clocks; their zero formal profiles annihilate every column in the set
at the paid total grade six. The span is therefore six-dimensional
with positive-semidefinite quadratic form. It meets the pure
negative-weight coordinate subspace only in zero, giving at most two
negative weights. Finally, projection of the two-dimensional pure span
of R1,Rc onto the nonpositive-weight coordinates is injective:
a nonzero vector supported only on positive weights cannot have
weighted square zero. This proves the second count, including zeros.
