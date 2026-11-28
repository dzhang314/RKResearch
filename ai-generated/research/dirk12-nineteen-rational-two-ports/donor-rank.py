#!/usr/bin/env python3
"""Exact three-port donor rank and size-seven residual decrease."""
from fractions import Fraction as Q
from probe import old_bank, lin, ev, span_basis

# Scaling the rank-debit block to give its first true size-six port clock 1
# is harmless. The two other such clocks become 7/9 and 5/9.
A,c,ports,_=old_bank(Q(1,11),Q(14,9),fa=Q(9,14),fb=Q(1,2),fc=Q(5,14))
primitive=lin(A,[v**5 for v in c])
triplet=[[primitive[i]-c[i]**6/6,A[i][3],A[i][4]] for i in (5,6,7)]
p,q=Q(3875,8019),Q(2000,3773)
assert triplet[2]==[p*x+q*y for x,y in zip(*triplet[:2],strict=True)]
assert len(span_basis(triplet))==2

# Pay the exact physical old profile separately, on all 48 size-seven trees.
A,c,ports,F=old_bank(Q(1,11),Q(6,11),fa=Q(9,14),fb=Q(1,2),fc=Q(5,14))
assert len(F)==3
for f in F:
    assert all(ev(f,c[i])==0 for i in (0,8,9))
    assert ev(f,c[7])==p*ev(f,c[5])+q*ev(f,c[6])
print("normalized donor rows")
for row in triplet:
    print(*(str(a) for a in row))
print("third donor row = (3875/8019) first + (2000/3773) second")
print("exact actual size-seven old residual rank",len(F))
