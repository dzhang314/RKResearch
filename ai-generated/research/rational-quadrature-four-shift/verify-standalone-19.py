#!/usr/bin/env python3
"""Derive and check the standalone rational rule by exact interpolation."""
from fractions import Fraction
from math import lcm, prod


def check(test, label):
    if not test:
        raise AssertionError(label)


U = (1, 3, 6, 11, 18, 26, 34, 44, 54, 64,
     74, 84, 94, 102, 110, 117, 122, 125, 127)
N = 128


def product_without(u):
    coef = [1]
    for v in U:
        if v != u:
            out = [0] * (len(coef)+1)
            for k, a in enumerate(coef):
                out[k] -= v*a
                out[k+1] += a
            coef = out
    return coef


def weight(u):
    integral = sum(Fraction(a*N**k, k+1)
                   for k, a in enumerate(product_without(u)))
    return integral / prod(u-v for v in U if u != v)


check(len(U) == len(set(U)) == 19 and all(0 < u < N for u in U),
      "distinct interior sites")
b = tuple(weight(u) for u in U)
check(all(w > 0 for w in b), "positive exact weights")
check(tuple(N-u for u in reversed(U)) == U and b == b[::-1],
      "reflection symmetry")
d = lcm(*(w.denominator for w in b))
check(d == 425643294094315542650108828261897814911098830084716100131250000,
      "common denominator")
a = tuple(int(d*w) for w in b)
check(all(Fraction(num, d) == w for num, w in zip(a, b)),
      "integer mass numerators")
for k in range(20):
    check((k+1)*sum(m*u**k for m,u in zip(a,U)) == d*N**k,
          ("exact degree", k))
next_defect = 21*sum(m*u**20 for m,u in zip(a,U)) - d*N**20
check(next_defect != 0, "degree-20 failure")
print("19 distinct interior rational nodes, all weights positive.")
print("Common weight denominator:", d)
print("All integer residuals vanish for degrees 0–19.")
print("Degree-20 moment defect:", Fraction(next_defect, 21*d*N**20))
print("PASS: exact standalone quadrature order 20, not an RK tableau.")
