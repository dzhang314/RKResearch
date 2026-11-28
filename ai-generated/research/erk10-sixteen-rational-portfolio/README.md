# Exact sixteen-stage ERK10 over every admissible local or finite-characteristic ring

Five explicit rational tableaux, each with sixteen distinct stages,
give **exact order ten in sixteen stages** over every nonzero
commutative **local** ring and every nonzero commutative ring of
**finite characteristic**, provided 10! is a unit. This includes all
fields with 10! nonzero and all p-adic integers and fields for primes
greater than seven. It does not give a single tableau over the factorial
localization or change the real 14–15 gap.

| Tableau | Rational horizon | Family placement |
| --- | ---: | --- |
| [First witness](../erk10-sixteen-rational-mirror/README.md) | −1/2 | Case 2, anchor b |
| [Compact witness](theta-five-fourths.json) | 5/4 | Case 0, anchor b |
| [11-unit witness](denominator-unit-at-11.json) | −1 | Case 0, anchor a |
| [13-unit witness](denominator-unit-at-13.json) | −1 | Case 1, anchor a |
| [17-unit witness](theta-four.json) | 4 | Case 0, anchor b |

The compact witness has a 28-digit coefficient denominator.

## Verification and ring argument

The [independent replay](replay.py) constructs all ordinary non-plane
rooted trees through order ten and checks every condition after clearing
the integer denominator. For each tableau, the two normalized order-eleven
defects at the ten-leaf bush and at the four-leaf-plus-five-leaf-bush tree
have coprime reduced numerators. Both defect denominators divide a power
of the tableau's coefficient denominator. Therefore each tableau has
exact order ten over any nonzero commutative ring inverting that
denominator.

The gcd of the five coefficient denominators is 816480000, which
has no prime factor outside 10!. In a local ring with 10! a unit,
at least one of the five denominators must be a unit: otherwise
the maximal ideal would contain their integer gcd, which is a unit.
This does not require a Henselian local ring.

For positive finite characteristic N, apply this local result to
each prime-power factor ring of the integers modulo N. Combine the
chosen literal arrays by the integer Chinese remainder theorem and
map them into the target ring. All cleared conditions through order
ten hold. If all order-eleven conditions held in the target, they
would hold in each of its nonzero prime-power components. This
contradicts the exact-order witness in any such component, at least
one of which is nonzero. The proof does not depend on the separate
p-adic constructions.

From this directory:

    python3 -B replay.py
    sha256sum -c sources.sha256

The literal arithmetic and domain argument are exact. This packet
does not claim an end-to-end Lean theorem for the full portfolio.
