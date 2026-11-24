#!/usr/bin/env python3
"""Independent integer check for the scaled 3+2+1 determinant; not a Lean oracle."""
from itertools import permutations
from math import prod
mod=15727
grid=[0,1069,1186,6796,7356,7876,8398,8920,9440,10000,15610]
def f(u,v,z):
 return 735*v**4*z**3 - 1260*u*v**4*z**2 + 630*u**2*v**4*z - 84*u**3*v**4 - 1960*v**3*z**4 + 2450*u*v**3*z**3 - 700*u**3*v**3*z + 140*u**4*v**3 + 1260*v**2*z**5 + 672*u*v**2*z**4 - 3885*u**2*v**2*z**3 + 2220*u**3*v**2*z**2 - 120*u**4*v**2*z - 60*u**5*v**2 - 2016*u*v*z**5 + 2688*u**2*v*z**4 - 960*u**4*v*z**2 + 240*u**5*v*z + 840*u**2*z**5 - 1680*u**3*z**4 + 1050*u**4*z**3 - 200*u**5*z**2
values=[f(*x)%mod for x in permutations(grid,3)]
assert len(values)==990 and all(values)
assert prod(values)%mod==14552
print("990/990 ordered pairwise distinct triples nonzero; product 14552 modulo 15727")
