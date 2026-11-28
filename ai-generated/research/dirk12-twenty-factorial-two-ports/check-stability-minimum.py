#!/usr/bin/env python3
"""Two independent modular determinant checks of the literal stability function."""
from fractions import Fraction
from pathlib import Path
import json

EXPECTED = {
    19: ([1, 9, 0, 0, 6, 7, 7, 9, 11, 18, 10, 8, 18, 6, 9, 10, 15, 16, 6, 0, 15],
         [1, 8, 1, 17, 18, 2, 1, 15, 15, 8, 11, 18, 2, 1, 17, 18, 4, 4, 10]),
    29: ([1, 5, 18, 24, 11, 11, 20, 20, 6, 26, 17, 0, 20, 4, 20, 27, 13, 25, 0, 24, 24],
         [1, 4, 28, 18, 23, 15, 4, 9, 21, 8, 26, 9, 4, 0, 5, 16, 3, 25, 18]),
}

def trim(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def mul(f, g, p):
    out = [0] * (len(f) + len(g) - 1)
    for i, x in enumerate(f):
        for j, y in enumerate(g):
            out[i+j] = (out[i+j] + x*y) % p
    return trim(out)


def rem(f, g, p):
    f = f[:]
    k = pow(g[-1], -1, p)
    while len(f) >= len(g):
        j = len(f)-len(g)
        x = k*f[-1] % p
        for i, y in enumerate(g):
            f[i+j] = (f[i+j]-x*y) % p
        trim(f)
    return f


def det(m, p):
    a = [[x % p for x in row] for row in m]
    value = 1
    for j in range(len(a)):
        k = next((i for i in range(j, len(a)) if a[i][j]), None)
        if k is None:
            return 0
        if k != j:
            a[j], a[k] = a[k], a[j]
            value = -value
        pivot = a[j][j]
        value = value*pivot % p
        inv = pow(pivot, -1, p)
        for i in range(j+1, len(a)):
            x = inv*a[i][j] % p
            for h in range(j+1, len(a)):
                a[i][h] = (a[i][h]-x*a[j][h]) % p
    return value % p


def evaluate(f, z, p):
    value = 0
    for x in reversed(f):
        value = (value*z+x) % p
    return value


def main():
    path = Path(__file__).with_name("tableau20.json")
    obj = json.loads(path.read_text())
    mat = [list(map(Fraction, row)) for row in obj["A"]]
    weights = list(map(Fraction, obj["b"]))
    n = len(mat)
    assert n == len(weights) == 20 and sum(weights) == 1
    assert all(len(row) == n for row in mat)
    assert not any(mat[i][j] for i in range(n) for j in range(i+1, n))
    assert sum(mat[i][i] != 0 for i in range(n)) == 18
    for p, (want_num, want_den) in EXPECTED.items():
        def mod(x):
            return x.numerator * pow(x.denominator, -1, p) % p
        A = [list(map(mod, row)) for row in mat]
        B = list(map(mod, weights))
        den = [1]
        for i in range(n):
            den = mul(den, trim([1, (-A[i][i]) % p]), p)
        series = [1]
        v = [1] * n
        for _ in range(22):
            series.append(sum(x*y for x, y in zip(B, v, strict=True)) % p)
            v = [sum(x*y for x, y in zip(row, v, strict=True)) % p for row in A]
        num = trim(mul(den, series, p)[:23])
        assert num == want_num and den == want_den
        u, v = num, den
        while v:
            u, v = v, rem(u, v, p)
        assert len(u) == 1
        for z in range(min(p, 21)):
            m = [[int(i == j)-z*A[i][j] for j in range(n)] for i in range(n)]
            k = [[m[i][j]+z*B[j] for j in range(n)] for i in range(n)]
            assert det(m, p) == evaluate(den, z, p)
            assert det(k, p) == evaluate(num, z, p)
        print(f"p={p}: degrees {len(num)-1}/{len(den)-1}; gcd degree 0; "
              f"{min(p, 21)} independent determinant evaluations")
        print("P:", num)
        print("Q:", den)


if __name__ == "__main__":
    main()
