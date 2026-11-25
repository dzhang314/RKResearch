#!/usr/bin/env python3
"""Exact finite-field certificates, no search for rational or real tableaux."""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb, isqrt


PENCIL_COLUMNS = {
    11: [3, 1, 0, 0, 2, 1, 1, 2, 0, 0, 1],
    13: [0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2],
    17: [0, 2, 0, 0, 0, 1, 3, 2, 1, 1, 2, 3, 1, 0, 0, 0, 2],
    19: [3, 3, 0, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 0, 3],
}
STRICT_FLOORS = [4, 5, 5, 6, 7, 7, 7, 8, 9, 10, 11, 11, 12, 13, 13]
PENCIL_FLOORS = [4, 5, 5, 6, 7, 7, 8, 9, 10, 11, 11, 12, 13, 13, 13]
SLICE_FLOORS = [4, 5, 5, 6, 7, 7, 8, 9, 10, 11, 11, 12, 13, 13, 14]
EXTRA_SLICE_HISTOGRAMS = {
    7: {1: 1},
    8: {0: 7, 1: 4, 2: 4, 3: 2},
    9: {0: 1764, 1: 1762, 2: 866, 3: 388, 4: 118, 5: 10, 7: 5},
}


def prime(q):
    return q > 1 and all(q % d for d in range(2, isqrt(q) + 1))


def legendre(j):
    a = [(-1)**(j-i) * comb(j, i) * comb(j+i, i) for i in range(j+1)]
    assert sum(a) == 1
    assert all(
        sum(Fraction(c, i+k+1) for i, c in enumerate(a)) == 0
        for k in range(j)
    )
    return a


def div_linear(a, x, q):
    """Coefficient arrays ascend; returns division by X-x and remainder."""
    b = [0] * (len(a) - 1)
    running = 0
    for j in range(len(a) - 1, 0, -1):
        running = (a[j] + x * running) % q
        b[j - 1] = running
    return b, (a[0] + x * running) % q


def linear_factor_degree(poly, q):
    f = [z % q for z in poly]
    assert f and f[-1]
    used = 0
    for x in range(q):
        while len(f) > 1:
            z, remainder = div_linear(f, x, q)
            if remainder:
                break
            f = z
            used += 1
    assert len(f) + used == len(poly)
    return used


def projected_moments(poly, m, q):
    assert len(poly) - 1 + m < q
    return [sum(c * pow(i+k+1, -1, q) for i, c in enumerate(poly)) % q
            for k in range(m)]


def pencil_receipt(q):
    assert prime(q)
    t = (q - 1) // 2
    a, b = legendre(t), legendre(t - 1) + [0]
    results = []
    for lam in range(q):
        f = [x + lam*y for x, y in zip(a, b)]
        assert f[-1] % q and projected_moments(f, t-1, q) == [0]*(t-1)
        results.append(linear_factor_degree(f, q))
    assert results == PENCIL_COLUMNS[q] and max(results) < t
    return results


def monic_hilbert_slice(q, r, m):
    """Normal form of the exact affine coefficient space after elimination."""
    assert 0 < m <= r and r+m < q
    rows = [[pow(i+k+1, -1, q) for i in range(r+1)] for k in range(m)]
    for i in range(m):
        j = next(j for j in range(i, m) if rows[j][i])
        rows[i], rows[j] = rows[j], rows[i]
        pivot_inv = pow(rows[i][i], -1, q)
        rows[i] = [pivot_inv*x % q for x in rows[i]]
        for j in range(m):
            if j != i:
                factor = rows[j][i]
                rows[j] = [(a-factor*b) % q for a, b in zip(rows[j], rows[i])]
    assert all(row[:m] == [int(i == j) for j in range(m)]
               for i, row in enumerate(rows))
    for params in product(range(q), repeat=r-m):
        tail = params + (1,)
        f = tuple(-sum(a*b for a, b in zip(row[m:], tail)) % q for row in rows) + tail
        assert projected_moments(f, m, q) == [0]*m
        yield f


def extra_slice_receipt():
    q, t = 17, 7
    for r in range(t, q-t):
        m = t-int(r == q-t-1)
        counts = Counter(linear_factor_degree(f, q) for f in monic_hilbert_slice(q, r, m))
        assert counts == EXTRA_SLICE_HISTOGRAMS[r]
        assert sum(counts.values()) == q**(r-m)
        assert max(counts) < r
        print(f"extra slice q={q}, t={t}, r={r}: {sum(counts.values())} polynomials, max={max(counts)}")


def floor(p, use_pencils, use_slice):
    base = max(4, (p+1)//2)
    primes = [q for q in range(2, p+1) if prime(q)]
    def excluded(n):
        t = p-n
        return any(n < q and (
            q < 2*t
            or (use_pencils and q == 2*t+1 and q in PENCIL_COLUMNS)
            or (use_slice and (q, t) == (17, 7))
        ) for q in primes)
    bound = next(n for n in range(base, p+1) if not excluded(n))
    correction = {q: 1 for q in PENCIL_COLUMNS} if use_pencils else {}
    if use_slice:
        correction[17] = 2
    assert bound == max(base, *(min(q, p-q//2+correction.get(q, 0)) for q in primes))
    return bound


def main():
    for q in PENCIL_COLUMNS:
        counts = pencil_receipt(q)
        print(f"critical pencil q={q}: {counts}; max={max(counts)}")
    extra_slice_receipt()
    bounds = [[], [], []]
    print("p prior strict pencils extra")
    for p in range(6, 21):
        row = [floor(p, False, False), floor(p, True, False), floor(p, True, True)]
        print(p, max(4, (p+1)//2), *row)
        for out, value in zip(bounds, row):
            out.append(value)
    assert bounds == [STRICT_FLOORS, PENCIL_FLOORS, SLICE_FLOORS]


if __name__ == "__main__":
    main()
