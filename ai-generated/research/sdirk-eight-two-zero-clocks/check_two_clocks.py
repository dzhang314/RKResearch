"""Exact rational replay for the three-row test with two zero clocks.

The prior two-zero script supplies the verified rational root brackets and
interval arithmetic. This file uses the forward earliest-zero primitive,
not the prior one-dimensional chart's reverse anchor.
"""
from contextlib import redirect_stdout
from fractions import Fraction as Q
from io import StringIO
from itertools import permutations
from pathlib import Path
from runpy import run_path

with redirect_stdout(StringIO()):
    old = run_path(str(Path(__file__).resolve().parent.parent /
                       "sdirk-eight-two-zero-line" / "check_front.py"))
sites = old["sites"]
for i,j in permutations(range(4),2):
    a,b = sites[i],sites[j]
    k = a+b-2
    q = (a+b)*k-a*b+Q(9,7)
    def r(x): return x*x+k*x+q
    def J(x): return x*(x*x/3+k*x/2+q)
    g = J(a)/r(a)
    R = r(g)
    D = R+g*g
    u = (2*R-g*(2*g+k))/D
    w = 2*u
    def kap(z): return 1+2*z-z*z
    H = -2+u+4*u*u-u**3
    S = R*kap(u)-r(g*(3-u))
    T = (R*kap(w)-r(g*(1+w)))*H+4*R*u*u*(3*u-2)
    checks = (g,R,D,a-g*(1+w),S,T)
    print(i+1,j+1,"".join(f.sign() for f in checks))
