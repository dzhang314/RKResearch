#!/usr/bin/env python3
"""Independent directed arithmetic on the same ten checked real site boxes."""
from fractions import Fraction as Q
from functools import lru_cache, reduce

def point(a):
    return (Q(a), Q(a))

def small(k):
    return (Q(k, 10**12), Q(k + 1, 10**12))

def add(x, y):
    return (x[0] + y[0], x[1] + y[1])

def sub(x, y):
    return (x[0] - y[1], x[1] - y[0])

def mul(x, y):
    s = [a*b for a in x for b in y]
    return (min(s), max(s))

def div(x, y):
    assert y[0]*y[1] > 0
    return mul(x, (1/y[1], 1/y[0]))

@lru_cache(maxsize=None)
def moment(roots, deg):
    if not roots:
        return point(Q(1, deg + 1))
    r, *rs = roots
    return sub(moment(tuple(rs), deg+1), mul(r, moment(tuple(rs), deg)))

def sign(x):
    assert x[0]*x[1] > 0
    return "+" if x[0] > 0 else "-"

def range8(x):
    a, b = (q*10**8 for q in x)
    return (a.numerator//a.denominator, -((-b.numerator)//b.denominator))

s, r, u = small(338563414841), small(174846987918), small(621050777002)
d, v = (mul(point(Q(1, 2)), x) for x in (add(s, r), sub(s, r)))
sites = (point(0), point(1), point(Q(1, 2)), small(935163423387),
         small(600005227335), small(831905816910), small(765227149711),
         d, v, u)
ns = []
for i, x in enumerate(sites):
    others = sites[:i] + sites[i+1:]
    n = moment(others, 0)
    den = reduce(mul, (sub(x, y) for y in others), point(1))
    b = div(n, den)
    ns.append(sign(n))
    print(i, "numerator", sign(n), "b in", range8(b), "/ 10^8")
assert "".join(ns) == "-++-++--++"
