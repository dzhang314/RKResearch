#!/usr/bin/env python3
"""Exact arithmetic checks of symmetry invariants, not tableau searches."""
from fractions import Fraction as Q
from functools import cache
from math import comb, isqrt, prod


@cache
def census(p, j):
    if j == 0:
        return 1
    if j == 1:
        return 1 + min(1, max(p - 2, 0))
    return 1 + min(j, p - 1 - j) + census(p, j - 2)


def rank_and_det(matrix):
    a = [list(map(Q, row)) for row in matrix]
    rk = 0
    det = Q(1)
    for j in range(len(a[0]) if a else 0):
        k = next((k for k in range(rk, len(a)) if a[k][j]), None)
        if k is None:
            continue
        if k != rk:
            a[k], a[rk] = a[rk], a[k]
            det = -det
        pivot = a[rk][j]
        det *= pivot
        for k in range(rk + 1, len(a)):
            f = a[k][j] / pivot
            if f:
                for l in range(j, len(a[k])):
                    a[k][l] -= f * a[rk][l]
        rk += 1
    if rk < len(a):
        det = Q(0)
    return rk, det


def rank_arithmetic():
    checks = 0
    for p in range(2, 129):
        last, previous = census(p, p - 1), census(p, p - 2)
        assert (last == previous) == (p % 4 != 1)
        if last != previous:
            continue
        for j in range(2, p):
            assert census(p, j - 2) + census(p, p - 1 - j) == last
            checks += 1
        if p % 2:
            m = (p + 1) // 4
            assert last == 2 * m**2
            assert census(p, 2 * m - 1) == m * (m + 1)
            local = lambda j: 0 if j < 2 else census(p, j - 2)
            assert local(m) - local(m - 1) == m // 2
        else:
            m = p // 2
            assert last == m * (m + 1) // 2
            defect = 0 if m < 3 else census(p, m - 3)
            assert defect == (m - 1)**2 // 4
            assert last - m - 2 * defect == m // 2
    print("Balanced complementary rank identities:", checks)


def determinant_arithmetic():
    for d in range(80):
        s = sum(Q(comb(d, a) * 2**a * (-1)**(d - a), a + 1)
                for a in range(d + 1))
        assert s == (Q(0) if d % 2 else Q(1, d + 1))
    for m in range(1, 19):
        gram = lambda j: [[Q(1, 2 * (a + b) + j) for b in range(m)]
                          for a in range(m)]
        ge, go = (rank_and_det(gram(j))[1] for j in (1, 3))
        odds = prod(range(1, 4 * m, 2))
        assert ge and go
        assert ge / go == Q(odds, prod(range(1, 2 * m, 2))**2)
        assert isqrt(odds)**2 != odds
    print("Centered moments: 80; exact Gram determinant ratios: 18")


def group_moments():
    checked = 0
    for q in range(1, 14):
        r = q // 2
        nodes = list(range(-r, 0)) + ([0] if q % 2 else []) + list(range(1, r + 1))
        deriv = {x: prod(x - y for y in nodes if y != x) for x in nodes}
        for sigma in (-1, 1):
            variables = list(range(1, r + 1)) + ([0] if q % 2 and sigma == 1 else [])
            columns = lambda d: [((1 + sigma * (-1)**d) * x**d)
                                 if x else (1 if d == 0 else 0) for x in variables]
            for D in range(q + 1):
                degree = q - D - 2
                sign = sigma * (-1)**(q - 1)
                powers = [j for j in range(max(0, degree + 1)) if (-1)**j == sign]
                rank, _ = rank_and_det([columns(d) for d in range(D + 1)])
                assert len(variables) - rank == len(powers)
                for j in powers:
                    mu = {x: Q(x**j, deriv[x]) for x in nodes}
                    assert all(mu[-x] == sigma * mu[x] for x in nodes)
                    assert all(sum(mu[x] * x**d for x in nodes) == 0 for d in range(D + 1))
                checked += 1
    print("Exact signed nodal-kernel dimensions:", checked)


def prime_checks():
    cases = []
    for m in range(1, 41, 2):
        ell = 4 * m + 1
        if any(ell % d == 0 for d in range(2, isqrt(ell) + 1)):
            continue
        det = prod(range(1, 4 * m, 2)) % ell
        assert pow(det, (ell - 1) // 2, ell) == ell - 1
        cases.append(ell)
    assert 13 in cases
    print("Prime-field exclusion examples checked:", len(cases))


if __name__ == "__main__":
    rank_arithmetic()
    determinant_arithmetic()
    group_moments()
    prime_checks()
    print("All checks pass; no attainment is inferred.")
