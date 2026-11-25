#!/usr/bin/env python3
"""Exact independent checker for the pure late ERK13 clean-row rank lemma.

No numerical roots, external files, or non-stdlib packages.
"""
from fractions import Fraction
from itertools import permutations
from math import isqrt

P = 40849
C = (435, 8419, 8685, 9891, 20819, 30310)
W = (7, -168, 1260, -4200, 6930, -5544, 1716)
V = (-6, 105, -560, 1260, -1260, 462)
CAP = (2, 0, 0, 1, 2, 3)
SLOTS = tuple((k, j) for k, cap in enumerate(CAP) for j in range(cap + 1))


def value(poly, x):
    t = 0
    for a in reversed(poly):
        t = (t * x + a) % P
    return t


def mul_linear(poly, a, b):
    ans = [0 for _ in range(len(poly) + 1)]
    for j, v in enumerate(poly):
        ans[j] = (ans[j] + a * v) % P
        ans[j + 1] = (ans[j + 1] + b * v) % P
    return ans


def lagrange(roots, z):
    poly = [1]
    den = 1
    for u in roots:
        if u != z:
            poly = mul_linear(poly, -u, 1)
            den = den * (z - u) % P
    mult = pow(den, -1, P)
    return tuple(a * mult % P for a in poly)


def full_rank(rows, columns):
    # Column-by-column Gaussian elimination. Keeping both dimensions explicit
    # guards against an accidentally shortened output equation or unknown list.
    assert all(len(r) == columns for r in rows)
    if len(rows) < columns:
        return False
    a = [r[:] for r in rows]
    for j in range(columns):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return False
        a[j], a[pivot] = a[pivot], a[j]
        den_inv = pow(a[j][j], -1, P)
        for i in range(j + 1, len(a)):
            mult = a[i][j] * den_inv % P
            if mult:
                for k in range(j, columns):
                    a[i][k] = (a[i][k] - mult * a[j][k]) % P
    return True


def main():
    assert all(P % d for d in range(2, isqrt(P) + 1))
    assert W[-1] % P != 0
    assert len(set(C)) == 6
    for poly in (V, W):
        for k in range(len(poly) - 1):
            assert sum(Fraction(a, j + k + 2)
                       for j, a in enumerate(poly)) == 0
    for x in C:
        assert 0 < x < P and x != 1
        assert value(W, x) == 0 and value(V, x) != 0

    Y = tuple((1 - c) % P for c in C)
    polys = tuple(lagrange(Y, z) for z in Y)
    for z, poly in enumerate(polys):
        for i, y in enumerate(Y):
            assert value(poly, y) == int(z == i)

    eq = {}
    for i, y in enumerate(Y):
        for z, poly in enumerate(polys):
            integral = sum(a * pow(k + 1, -1, P) * pow(y, k + 1, P)
                           for k, a in enumerate(poly)) % P
            g = integral * pow(value(V, C[i]), -1, P) % P
            row_r = [g * pow(y, j, P) % P for j in range(5)]
            row_a = [poly[k] * pow(y, j, P) % P for k, j in SLOTS]
            eq[z, i] = row_r + row_a

    seen = 0
    for order in permutations(range(6)):
        forbidden = [eq[order[z], order[i]] for i in range(6)
                     for z in range(i + 1)]
        assert len(forbidden) == 21
        assert full_rank(forbidden, 19), order
        seen += 1
    assert seen == 720
    print("Prime", P, "verified; 720 chronological orders; all ranks 19.")


if __name__ == "__main__":
    main()
