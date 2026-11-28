#!/usr/bin/env python3
"""Exact hull calculation and coefficient valuation table."""
from fractions import Fraction as Q
from math import lcm

rows = []
for j in range(1, 5):
    ds = [i+j+1 for i in range(6)]
    rows.append([lcm(*ds)//v for v in ds])

def det(a):
    if len(a)==1:
        return a[0][0]
    return sum((-1)**j*x*det([r[:j]+r[j+1:] for r in a[1:]]) for j,x in enumerate(a[0]))

A = [1,0,-70,280,-378,168]
B = [0,1,Q(-28,3),28,Q(-168,5),14]
assert all(sum(x*y for x,y in zip(r,c))==0 for r in rows for c in (A,B))
d = det([r[2:] for r in rows])
assert d
def v2(x):
    if x==0:
        return None
    q=Q(x)
    def order(k):
        k=abs(k)
        return (k&-k).bit_length()-1
    return order(q.numerator)-order(q.denominator)
assert [v2(x) for x in A]==[0,None,1,3,1,3]
assert [v2(x) for x in B]==[None,0,2,2,3,1]
print("anchored moment coefficient determinant:",d)
print("constant coefficient valuations:",[v2(x) for x in A])
print("linear coefficient valuations before v(t):",[v2(x) for x in B])
