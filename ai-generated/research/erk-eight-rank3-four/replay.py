#!/usr/bin/env python3
"""Independent integer replay from the literal ERK8 rational tableau."""
from fractions import Fraction
from functools import cache
from math import lcm, prod
from pathlib import Path
import json

t = json.loads(Path(__file__).with_name("tableau.json").read_text())
rows = [list(map(Fraction,row)) for row in t["A"]]
weights = list(map(Fraction,t["b"]))
assert len(rows) == len(weights) == 11
assert [len(row) for row in rows] == list(range(11))
assert [sum(row) for row in rows] == list(map(Fraction,t["c"]))
D = lcm(*(z.denominator for row in rows for z in row),
        *(z.denominator for z in weights))
M = [tuple(int(z*D) for z in row) for row in rows]
b = tuple(int(z*D) for z in weights)

# Build the root branch multisets by adjoining the root of a smaller tree.
# This is independent of the generator's partitions of the root degree.
T = [set(), {()}]
for n in range(2,10):
    T.append({tuple(sorted(u+(v,)))
              for k in range(1,n)
              for u in T[k] for v in T[n-k]})
assert [len(T[n]) for n in range(1,10)] == [1,1,2,4,9,20,48,115,286]

@cache
def order(tree):
    return 1+sum(map(order,tree))

@cache
def factorial(tree):
    return order(tree)*prod(map(factorial,tree))

@cache
def numer(tree):
    if not tree:
        return (1,)*11
    branch, others = tree[0], tree[1:]
    x, y = numer(branch), numer(others)
    return tuple(y[i]*sum(a*u for a,u in zip(M[i],x)) for i in range(11))

def paid(tree):
    return Fraction(factorial(tree)*sum(u*v for u,v in zip(numer(tree),b)),D**order(tree))

for n in range(1,9):
    for tree in T[n]:
        assert paid(tree)==1,(n,tree,paid(tree))
bush9 = ((),)*8
defect = paid(bush9)-1
assert defect == Fraction(t["bush9_normalized_defect"]) != 0
print(f"All 200 rooted conditions through order 8 are exact; ninth-order bush defect: {defect}")
print(f"Common positive denominator: {D}")
