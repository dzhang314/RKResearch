#!/usr/bin/env python3
"""Recompute the exact integer arithmetic for the idempotent gluing corollary."""
from fractions import Fraction
from math import factorial, gcd, isqrt, lcm, prod
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
NAMES = (
    ('first', '../erk10-sixteen-rational-mirror/tableau.json'),
    ('compact', 'theta-five-fourths.json'),
    ('unit11', 'denominator-unit-at-11.json'),
    ('unit13', 'denominator-unit-at-13.json'),
    ('theta-four', 'theta-four.json'),
)

def denominator(path):
    data = json.loads((HERE / path).read_text())
    D = lcm(*(Fraction(x).denominator for row in [*data['A'], data['b']] for x in row))
    assert D == int(data['denominator'])
    return D

def strip_paid(n):
    for p in (2, 3, 5, 7):
        while n % p == 0:
            n //= p
    return n

ds = {name: denominator(path) for name, path in NAMES}
g = gcd(*ds.values())
f = factorial(10)
assert (g, f*f//g, f*f%g) == (816480000, 16128, 0)
print(f'Denominator gcd {g}; (10!)^2 = {f*f//g} times this gcd.')
compact = {2: 14, 3: 13, 5: 5, 7: 6, 11: 1, 13: 2, 17: 1, 19: 1, 229: 1}
assert prod(p**e for p, e in compact.items()) == ds['compact']
assert all(all(p % d for d in range(2, isqrt(p)+1)) for p in compact)
choices = {11: 'unit11', 13: 'unit13', 17: 'theta-four', 19: 'first', 229: 'first'}
assert set(choices) == set(compact) - {2, 3, 5, 7}
for p, name in choices.items():
    assert ds[name] % p != 0
    surviving = [d for d in ds.values() if d % p != 0]
    blockers = strip_paid(gcd(*surviving))
    if p in (13, 19):
        assert blockers == strip_paid(ds[name])
    else:
        support = {
            11: (17,19,29,97,367), 17: (11,13,19,37,53,79,107,227,467,797,10531),
            229: ()
        }[p]
        assert all(all(q % d for d in range(2, isqrt(q)+1)) for q in support)
        for q in support:
            assert blockers % q == 0
            while blockers % q == 0:
                blockers //= q
        assert blockers == 1
    print(f'{p}: select {name}')
assert all(d%11 == 0 or d%17 == 0 for d in ds.values())
print('Every one of the five denominators is divisible by 11 or 17.')
