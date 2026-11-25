#!/usr/bin/env python3
"""Exact low-grade formulas used in the reflected-profile proof."""
from fractions import Fraction as Q
from itertools import product
from math import comb, prod


def reflection():
    count = 0
    for m in range(1, 15):
        # On the error-free monomials the binomial combination is (Z-X)^m.
        for z, x in product(map(Q, [-3, 1, 2, 7]), repeat=2):
            computed = sum((-1)**j * comb(m, j+1) * z**(m-1-j)
                           * (z**(j+1) - x**(j+1)) for j in range(m))
            assert computed == (z-x)**m
            for j in range(m):
                # The coefficient of each abstract transpose action matches too.
                assert m*comb(m-1, j) == (j+1)*comb(m, j+1)
            count += 1
        assert sum((-1)**j * Q(comb(m, j), j+1) for j in range(m+1)) == Q(1, m+1)
    print("Exact primitive-polynomial and quadrature identities:", count)


def gaussian():
    # Shifted Legendre L4 at z=1, in ascending coefficients.
    L = [Q(1), Q(-20), Q(90), Q(-140), Q(70)]
    for k in range(4):
        assert sum(c / (j+k+1) for j, c in enumerate(L)) == 0
    for x in map(Q, range(-4, 6)):
        val = sum(c*x**j for j, c in enumerate(L))
        rev = sum(c*(1-x)**j for j, c in enumerate(L))
        u = 2*x-1
        assert val == rev
        assert 8*val == 35*u**4 - 30*u*u + 3
        assert ((35*u*u-15)/2)**2 - 30 == Q(35, 4)*(35*u**4-30*u*u+3)
    for a, b in [(Q(1), Q(2)), (Q(1, 7), Q(3, 11)), (Q(-5), Q(12))]:
        nodes = [Q(1, 2) + d for d in (-b, -a, a, b)]
        residue = [1/prod(x-y for y in nodes if x!=y) for x in nodes]
        assert all(v==-w for v, w in zip(residue, reversed(residue)))
        assert all(sum(v*x**k for v, x in zip(residue, nodes))==0 for k in range(3))
    print("Legendre parity, four orthogonalities, radical and barycentric signs: pass")


if __name__ == "__main__":
    reflection()
    gaussian()
    print("No tableau attainment is inferred.")
