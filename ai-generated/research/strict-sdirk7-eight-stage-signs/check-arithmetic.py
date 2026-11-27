"""Independent exact arithmetic for the eight-stage SDIRK7 support notes."""
from fractions import Fraction

L3 = (-1, 12, -30, 20)
L4 = (1, -20, 90, -140, 70)

def value(coeff, x, p):
    return sum(a * pow(x, k, p) for k, a in enumerate(coeff)) % p

def derivative(coeff):
    return tuple(k * a for k, a in enumerate(coeff) if k)

def moment(coeff, k):
    return sum(Fraction(a, j + k + 1) for j, a in enumerate(coeff))

assert all(moment(L3, k) == moment(L4, k) == 0 for k in range(3))
# Shifted Legendre expansion of x^j used by the midpoint Gram proof.
change = [
    [1, 0, 0, 0],
    [Fraction(1, 2), Fraction(1, 2), 0, 0],
    [Fraction(1, 3), Fraction(1, 2), Fraction(1, 6), 0],
    [Fraction(1, 4), Fraction(9, 20), Fraction(1, 4), Fraction(1, 20)],
]
assert all(
    sum(Fraction(change[i][k] * change[j][k], 2*k+1) for k in range(4))
    == Fraction(1, i+j+1)
    for i in range(4) for j in range(4)
)
# Homogeneous data (1:lambda) and (0:1); no roots are assumed finite.
root_counts = []
for lam in range(19):
    coeff = tuple(a + lam*b for a, b in zip(L4, L3 + (0,)))
    assert coeff[4] % 19 != 0
    roots = [x for x in range(19) if value(coeff, x, 19) == 0]
    assert len(roots) <= 2 and all(value(derivative(coeff), x, 19) for x in roots)
    root_counts.append(len(roots))
roots = [x for x in range(19) if value(L3, x, 19) == 0]
# Y*homogenize_3(L3) has one simple projective root at infinity.
assert L3[3] % 19 != 0
assert len(roots) == 1 and all(value(derivative(L3), x, 19) for x in roots)
# Projective no-root certificate for y^3 - 9 y^2 + 18 y - 6 mod 5.
assert all(
    (a**3 - 9*a*a*b + 18*a*b*b - 6*b**3) % 5
    for a, b in [(a, 1) for a in range(5)] + [(1, 0)]
)
# Laguerre scalar identity, in the displayed unnormalized notation of the proof.
for G, a, d, x, y in [(3, 5, 7, -8, 9), (2, -1, 3, 4, 5)]:
    h0 = a+d+G-y
    h1 = 2*(a*G+d*x+G*y)-y*y
    h2 = 3*(a*G*G+d*x*x+G*y*y)-y**3
    h3 = a*G*G+d*(4*G*x-2*G*G-x*x)
    assert -3*h3-h2+6*G*h1-6*G*G*h0 == y**3-9*G*y*y+18*G*G*y-6*G**3
print("Verified Legendre/Hilbert arithmetic, 20 projective mod-19 directions, and all six projective mod-5 points.")
print("Finite-root counts for the mod-19 pencil:", root_counts, "infinity direction:", len(roots))
