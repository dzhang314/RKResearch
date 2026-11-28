#!/usr/bin/env python3
"""Separate exact-ring rooted replay: canonical multiset enumeration and direct cubic arithmetic."""
from functools import cache
import json
from math import prod
from pathlib import Path

data = json.loads(Path(__file__).with_name("tableau.json").read_text())
p = data["p"]
assert p == 17
assert data["base"] == [10,3,7,1] and data["orientation"] == []
m = tuple(data["base"][:3])
assert all((x**3+7*x*x+3*x+10)%p for x in range(p))
zero, one = (0,0,0), (1,0,0)
def add(a,b):
    return tuple((u+v) % p for u,v in zip(a,b))
def mul(a,b):
    c = [0]*5
    for i,u in enumerate(a):
        for j,v in enumerate(b):
            c[i+j] += u*v
    for i in (4,3):
        for j,M in enumerate(m):
            c[i-3+j] -= c[i]*M
    return tuple(t % p for t in c[:3])
def total(vals):
    z = zero
    for v in vals:
        z = add(z,v)
    return z
def mm(vals):
    z = one
    for v in vals:
        z = mul(z,v)
    return z
A = tuple(tuple(tuple(v) for v in row) for row in data["A"])
b = tuple(tuple(v) for v in data["b"])
assert len(A) == len(b) == 15 and all(len(row)==15 and all(x==zero for x in row[i+1:]) for i,row in enumerate(A))
assert all(len(v)==3 and all(0<=a<p for a in v) for row in (*A,b) for v in row)
assert A[0][0] == A[-1][-1] == zero and len({A[i][i] for i in range(15)}) > 2
assert tuple(i+1 for i,x in enumerate(b) if x==zero) == (2,3,4,5)
# Each rooted tree is a canonical tuple of its child trees. Generate
# forests by increasing child indices rather than ordering labels.
@cache
def trees(n):
    if n == 1:
        return ((),)
    catalog = [(i,t) for i in range(1,n) for t in trees(i)]
    def forests(rem,start):
        if rem == 0:
            yield ()
        for k in range(start,len(catalog)):
            w,t = catalog[k]
            if w > rem:
                break
            for tail in forests(rem-w,k):
                yield (t,)+tail
    return tuple(forests(n-1,0))
@cache
def size(t):
    return 1+sum(map(size,t))
@cache
def density(t):
    return size(t)*prod(map(density,t))
@cache
def stage(t):
    vec = tuple(incoming(u) for u in t)
    return tuple(mm(q[i] for q in vec) for i in range(15))
@cache
def incoming(t):
    return tuple(total(mul(a,z) for a,z in zip(row,stage(t))) for row in A)
def weighted(t):
    return total(mul(B,z) for B,z in zip(b,stage(t)))
counts = [len(trees(n)) for n in range(1,13)]
assert counts == [1,1,2,4,9,20,48,115,286,719,1842,4766]
for n in range(1,13):
    for t in trees(n):
        assert mul((density(t)%p,0,0),weighted(t)) == one, (n,t)
defect = add(mul((13,0,0),weighted(((),)*12)),(p-1,0,0))
assert defect == tuple(data["scaled_order13_star"]) == (11,7,12)
print("Ordinary 15-stage DIRK literal:", sum(counts), "rooted conditions; thirteenth-bush defect", defect)


assert incoming(()) == tuple(tuple(c) for c in data["c"])
print("Cubic irreducible; actual stage times, both explicit endpoint diagonals and four zero weights checked.")
