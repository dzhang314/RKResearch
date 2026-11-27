#!/usr/bin/env python3
"""Independent exact replay of the outside-11 scalar charts.

All values are in Q[u]/(7*u^2 - 7*u + 1) or exact residues of its
two roots in a listed prime field. This is not a tableau search.
The Lean certificates convert the same finite algebra into literal proofs.
"""
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F


@dataclass(frozen=True)
class Pair:
    a: F = F(0)
    b: F = F(0)

    @staticmethod
    def of(other):
        return other if isinstance(other, Pair) else Pair(F(other))

    def __add__(self, other):
        other = Pair.of(other)
        return Pair(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Pair(-self.a, -self.b)

    def __sub__(self, other):
        return self + -Pair.of(other)

    def __rsub__(self, other):
        return Pair.of(other) + -self

    def __mul__(self, other):
        other = Pair.of(other)
        return Pair(
            self.a * other.a - self.b * other.b / 7,
            self.a * other.b + self.b * other.a + self.b * other.b,
        )

    __rmul__ = __mul__

    def __pow__(self, exponent):
        answer = Pair.of(1)
        for _ in range(exponent):
            answer *= self
        return answer

    def norm(self):
        return self.a * self.a + self.a * self.b + self.b * self.b / 7

    def specialize(self, root, prime):
        value = self.a + self.b * root
        return value.numerator * pow(value.denominator, -1, prime) % prime


def prime_factors(n):
    n = abs(n)
    answer = set()
    factor = 2
    while factor * factor <= n:
        while n % factor == 0:
            answer.add(factor)
            n //= factor
        factor += 1
    if n > 1:
        answer.add(n)
    return answer


u = Pair(F(0), F(1))
v = 1 - u
m = Pair.of(F(1, 2))
grid = [
    (u, m, v, 28, 14 - 56 * u),
    (u, v, m, 28, 42 - 196 * u),
    (m, u, v, 308, 588 - 1568 * u),
]
expected = [
    (3 + 21 * u, -69 - 42 * u, 154 - 56 * u),
    (15 - 21 * u, -147 + 168 * u, 182 - 196 * u),
    (84 + 84 * u, -1050 + 336 * u, 2128 - 1568 * u),
]
cases = []
for (h, x, z, scale, theta), coefficients in zip(grid, expected):
    e = 3*h*h - 4*h*(x+z) + 6*x*z
    numer = 4*h*x - 3*h*h
    assert e.norm() != 0 and theta * e == scale * numer
    a0, a1, a2 = coefficients
    assert coefficients == (
        theta*x*z + 2*scale*h*x,
        -theta*(x+z) - scale*(4*x+3*h),
        theta+5*scale,
    )
    cap = lambda t: a0 + a1*t + a2*t*t
    A, B, C = cap(u), cap(v), cap(m)
    U = [(2*u)**r*B*C+(2*v)**r*A*C-2*A*B for r in range(4)]
    gates = (
        U[3]-4*h*U[2]+4*h*h*U[1],
        U[0]*U[2]-U[1]**2,
        a2*U[3]-8*a0*U[1],
    )
    cases.append((a0, a1, a2, A, B, C, *gates))

paid = {2, 3, 5, 7}
exceptional = set()
for a0, _, a2, A, B, C, *gates in cases:
    for f in [a0, a2, A, B, C, *gates]:
        norm = f.norm()
        assert norm
        exceptional |= prime_factors(norm.numerator) - paid
        assert not (prime_factors(norm.denominator) - paid)
assert exceptional == {11, 17, 37, 41, 43, 79}
print("Exactly the nonfactorial norm guards:", sorted(exceptional))
for p, repaired in [(17, "shared last"), (37, "linear"), (41, "linear"),
                    (43, "shared first"), (79, "shared center")]:
    roots = [r for r in range(p) if (7*r*r-7*r+1) % p == 0]
    assert len(roots) == 2
    kinds = Counter()
    for root in roots:
        for values in cases:
            a0, a1, a2, A, B, C, f4, gram, f5 = (
                v.specialize(root, p) for v in values
            )
            assert a0
            bad = [name for name, value in
                   [("shared first", A), ("shared last", B), ("shared center", C)]
                   if not value]
            if bad:
                assert len(bad) == 1 and a2
                kinds[bad[0]] += 1
            elif not a2:
                assert a1 and f4
                kinds["linear"] += 1
            else:
                assert f4 and gram and f5
                kinds["quadratic"] += 1
    assert set(kinds) == {"quadratic", repaired}
    print(p, roots, dict(kinds))
