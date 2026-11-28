#!/usr/bin/env python3
"""Exact finite arithmetic for the four-noncancelling DIRK12/15 subface."""
from itertools import combinations
from math import isqrt

p = 43
interiors = (2, 9, 22, 35, 42)
grid = (0, *interiors)
derivative = (-42, 840, -5040, 12600, -13860, 5544)


def poly_mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, f in enumerate(a):
        for j, g in enumerate(b):
            c[i+j] = (c[i+j] + f*g) % p
    return c


def evaluate(coeffs, x):
    return sum(a * pow(x, j, p) for j, a in enumerate(coeffs)) % p


def hull(xs):
    h = [1]
    for x in xs:
        h = poly_mul(h, [-x % p, 1])
    return h


def primitive(coeffs):
    return [0] + [a * pow(j+1, -1, p) % p for j, a in enumerate(coeffs)]


def integral(coeffs, a, b):
    h = primitive(coeffs)
    return (evaluate(h, b) - evaluate(h, a)) % p


def tap_numerator(u, z):
    return integral(hull(x for x in grid if x != z), 0, u)


def two_moment_det(u, d):
    f = hull((0, u, d))
    a, b, c = [integral([0]*i + f, 0, u) for i in range(3)]
    return (a*c - b*b) % p


def oneline_profile(h, a, b):
    return poly_mul(h, [integral([0]+h, a, b), -integral(h, a, b) % p])


def crossed_integral(u, forward, backward):
    f = oneline_profile(hull((0,u,*forward)), 0, u)
    g = oneline_profile(hull((1,u,*backward)), u, 1)
    return integral(poly_mul(primitive(f),g), 0, 1)


def check():
    assert all(p % d for d in range(2,isqrt(p)+1))
    assert derivative[-1] % p and len(set(interiors)) == 5
    assert tuple(x for x in range(p) if evaluate(derivative,x) == 0) == interiors
    assert set(interiors) == {(1-x) % p for x in interiors}
    taps = [[tap_numerator(u,z) for z in grid] for u in interiors]
    dets = [[two_moment_det(u,d) for d in interiors if d != u] for u in interiors]
    integrals = []
    for u in interiors:
        dirty = set(interiors)-{u}
        integrals.append([crossed_integral(u, f, sorted(dirty-set(f)))
                          for f in combinations(sorted(dirty),2)])
    for name, table, n in (("tap numerators",taps,30),("mixed determinants",dets,20),
                           ("opposing primitive integrals",integrals,30)):
        values = [v for row in table for v in row]
        assert len(values) == n and all(values)
        print(f"{name}: {n} nonzero residues")
        for u, row in zip(interiors,table):
            print(u, *row)


if __name__ == '__main__':
    check()
