#!/usr/bin/env python3
"""Reconstruct the exact reflected profile coefficients using stdlib."""
from fractions import Fraction
from math import comb

for d in (5, 6, 7):
    g = [k*(-1)**(d-k)*comb(d,k)*comb(d+k,k)*(-1)**(d+1) for k in range(1,d+1)]
    c = [g[0]]+[g[i]-g[i-1] for i in range(1,d)]+[-g[-1]]+[0]*(7-d)
    assert len(c)==8
    checks = [sum(Fraction(a,k+i+1) for i,a in enumerate(c)) for k in range(d)]
    assert checks == [1]+[0]*(d-1)
    print("degree",d,"coefficients",c,"reflected integrals",list(map(int,checks)))
