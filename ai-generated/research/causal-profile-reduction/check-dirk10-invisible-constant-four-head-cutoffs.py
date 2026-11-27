#!/usr/bin/env python3
"""Exact cutoffs for constant invisible four-head DIRK ten.

This verifies a suffix chronology and first-regular pole: it is not
an exclusion of the entire four-head chart.
"""
from itertools import permutations
import sys

import sympy as sp


def verify_pole_formula():
    x, r = sp.symbols("x r")
    s, p = 6*r/5, 3*r*r/10
    q = x*x-s*x+p
    h = 42*x**5-84*x**4+56*x**3-14*x*x+x
    i = 3*x**4-4*s*x**3+6*p*x*x
    a, b, c = [sp.Poly(sp.rem(k,q,x),x) for k in (h,i,x*i)]
    delta0 = b.nth(1)*a.nth(0)-b.nth(0)*a.nth(1)
    delta1 = c.nth(1)*a.nth(0)-c.nth(0)*a.nth(1)
    p0 = 2079*r**4-5040*r**3+4200*r*r-1400*r+150
    p1 = 378*r**4-945*r**3+840*r*r-315*r+40
    assert sp.expand(delta0+27*r**4*p0/25000) == 0
    assert sp.expand(delta1+27*r**5*p1/12500) == 0


def check(p):
    roots = tuple(v for v in range(p) if (42*v**4-84*v**3+56*v*v-14*v+1)%p == 0)
    assert len(roots) == 4

    def d(a,b):
        assert b%p
        return a*pow(b%p,-1,p)%p

    for U,V,W in permutations(roots,3):
        def ratio(t):
            A = t*t*(3*t*t-4*(U+V)*t+6*U*V)
            B = t**3*(12*t*t-15*(U+V)*t+20*U*V)
            return d(B,5*A)
        assert (V-2*U)%p and (U-2*V)%p
        err = ((V-U)*(ratio(W)-ratio(U))-(W-U)*(ratio(V)-ratio(U)))%p
        j = W*U*U+W*V*V-4*W*U*V+U*U*V+U*V*V
        assert err and err == d(-6*(U-V)*(U-W)*(V-W)*j,
            5*(U-2*V)*(2*U-V)*(6*U*V-4*(U+V)*W+3*W*W))

    for r in roots:
        a = 2079*r**4-5040*r**3+4200*r*r-1400*r+150
        b = 2*r*(378*r**4-945*r**3+840*r*r-315*r+40)
        assert a%p
        for t in (0,1,*roots):
            assert (b-a*t)%p and (10*t*t-12*r*t+3*r*r)%p
    print(f"mod {p}: 24 late-ghost cutoffs and four first-regular pole guards pass")


if __name__ == "__main__":
    verify_pole_formula()
    for p in map(int,sys.argv[1:]) if len(sys.argv)>1 else (419,719):
        check(p)
