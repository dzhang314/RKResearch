#!/usr/bin/env python3
"""Exact low-window scalar checks for the native early a=5 ERK13 port.

Polynomials are in increasing coefficient order. No tableau, floating
point, optimization, network, Lean compiler, or old certificate is used.
"""

from fractions import Fraction as F
from itertools import combinations, permutations
from math import gcd, isqrt


def prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def evalp(a, x):
    acc = 0
    for c in reversed(a):
        acc = acc * x + c
    return acc


def red(a, p):
    q = F(a)
    return q.numerator * pow(q.denominator, -1, p) % p


def moment(a, k=0):
    return sum((F(c, i + k + 1) for i, c in enumerate(a)), F(0))


def add(a, b):
    return [
        (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
        for i in range(max(len(a), len(b)))
    ]


def scale(a, c):
    return [x * c for x in a]


def mul(a, b):
    prod = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            prod[i + j] += u * v
    return prod


def determinant_mod(a, p):
    a = [row[:] for row in a]
    d = 1
    for i in range(len(a)):
        j = next((j for j in range(i, len(a)) if a[j][i] % p), None)
        if j is None:
            return 0
        if j != i:
            a[i], a[j] = a[j], a[i]
            d = -d
        h = a[i][i] % p
        d = d * h % p
        inv = pow(h, -1, p)
        for j in range(i + 1, len(a)):
            t = a[j][i] * inv
            for k in range(i, len(a)):
                a[j][k] = (a[j][k] - t * a[i][k]) % p
    return d % p


def split(f, p):
    assert prime(p) and gcd(f[-1], p) == 1
    values = [a for a in range(p) if evalp(f, a) % p == 0]
    assert len(values) == len(f) - 1  # simple split by the field root bound
    return values


def integ_row(a, k, p):
    return [pow(a, i + k + 1, p) * pow(i + k + 1, -1, p) % p for i in range(4)]


def cubic_rows(t, u, j, p):
    rows = [
        integ_row(t, 1, p) + [0],
        integ_row(t, 2, p) + [0],
        integ_row(t, 3, p) + [-evalp(j, t) % p],
    ]
    for k in [2, 3]:
        lo = integ_row(u, k - 1, p)
        hi = integ_row(u, k, p)
        rows.append(
            [(b - t * a) % p for a, b in zip(lo, hi)]
            + ([0] if k == 2 else [-evalp(j, u) % p])
        )
    return rows


lobatto5 = [-1, 20, -120, 300, -330, 132]
lobatto6 = [0] + lobatto5
radau7 = [0, 7, -168, 1260, -4200, 6930, -5544, 1716]

assert evalp(lobatto6, 1) == evalp(radau7, 1) == 1
assert [moment(lobatto6, k) for k in range(6)] == [F(1, 42)] * 6
assert [moment(radau7, k) for k in range(6)] == [0] * 6

h3 = [-F(1, 14), F(9, 14), -F(3, 2), 1]
h4 = [F(1, 42), -F(1, 3), F(4, 3), -2, 1]
h5 = scale(lobatto5, F(1, 132))
assert h5 == add(mul([-F(1, 2), 1], h4), scale(h3, -F(2, 33)))
for j, h in [(3, h3), (4, h4), (5, h5)]:
    assert all(moment(h, k + 1) == moment(h, k + 2) for k in range(j))

roots_43 = split(lobatto5, 43)
assert roots_43 == [2, 9, 22, 35, 42]
assert all(red(evalp(h4, t), 43) for t in roots_43)
assert [evalp(radau7[1:], t) % 43 for t in roots_43] == [2, 10, 40, 10, 2]
residues = [
    determinant_mod(cubic_rows(t, u, radau7, 43), 43)
    for t, u in permutations(roots_43, 2)
]
assert residues == [
    2, 11, 36, 17, 33, 25, 25, 14, 2, 5,
    23, 18, 26, 5, 17, 31, 3, 14, 17, 37,
]

roots_181 = split(lobatto5, 181)
assert roots_181 == [52, 81, 91, 101, 130]
tested = 0
for t in roots_181:
    other = [0] + [u for u in roots_181 if u != t]
    for k in range(6):
        for chosen in combinations(other, k):
            r = [1]
            for a in chosen:
                r = [c % 181 for c in mul(r, [-a, 1])]
            v = sum(
                c * pow(t, i + 2, 181) * pow(i + 2, -1, 181)
                for i, c in enumerate(r)
            ) % 181
            assert v, (t, chosen)
            tested += 1
assert tested == 160

print("rational orthogonality: F5, J7 and the adjacent H3/H4/H5 basis checked")
print("mod 43 cubic rows: all 20 ordered off-diagonal determinants nonzero")
print("mod 181 pure one-port: all 160 complementary factor evaluations nonzero")
