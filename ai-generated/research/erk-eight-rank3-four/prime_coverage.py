#!/usr/bin/env python3
"""Finite-prime localization receipts for chronologies of the fixed quadrature."""
from construct import construction, qnodes, qweights
from fractions import Fraction
from itertools import permutations
from math import gcd, lcm, prod
import sympy as s

def denom(A,b):
    return lcm(*(z.denominator for row in A for z in row),
               *(z.denominator for z in b))

families=[]
for perm in permutations(range(1,5)):
    indices=(0,*perm,5)
    for dup in range(5):
        tableau=construction([qnodes[i] for i in indices],[qweights[i] for i in indices],dup)
        if not isinstance(tableau,str):
            A,b,*_=tableau
            families.append((indices,dup,denom(A,b)))
assert len(families)==120
D=lcm(*(x.denominator for x in qnodes+qweights))
common=gcd(*(d for _,_,d in families))
print("fixed quadrature-denominator primes:",s.factorint(D))
print("all chronology denominator gcd:",s.factorint(common))
assert D%common==0 or common%D==0
