#!/usr/bin/env python3
"""All unordered rooted trees through 12, using literal integer-scaled stages."""
from fractions import Fraction as Q
from math import factorial, prod, gcd
import json
from pathlib import Path

P = json.loads(Path(__file__).with_name("tableau21.json").read_text())
s, p = P["stages"],P["order"]
DA, DB = P["matrix_denominator"],P["weight_denominator"]
A0, b0 = P["A"],P["b"]

def into_int(raw,d):
    x = Q(raw)*d
    assert x.denominator==1
    return x.numerator

A = tuple(tuple(into_int(v,DA) for v in row) for row in A0)
b = tuple(into_int(v,DB) for v in b0)
assert len(A)==len(b)==s==21
assert all(len(row)==s and all(a==0 for a in row[i+1:]) for i,row in enumerate(A))
assert Q(A[0][0],DA)==Q(1,2)!=Q(A[1][1],DA)==Q(1,4)
assert all(Q(sum(row),DA)==Q(c) for row,c in zip(A,P["c"],strict=True))
assert factorial(12)**P["common_factorial_exponent"]%P["common_denominator"]==0
sparse=[tuple((j,a) for j,a in enumerate(row) if a) for row in A]
def apply(u):
    return tuple(sum(a*u[j] for j,a in row) for row in sparse)

def ip(u,v):
    return sum(a*z for a,z in zip(u,v,strict=True))

orders=[1]
densities=[1]
seeds=[(1,)*s]
images=[apply(seeds[0])]
counts=[1]
def forests(remaining,start,stop):
    if remaining==0:
        yield ()
        return
    for j in range(start,stop):
        k=orders[j]
        if k>remaining: break
        for rest in forests(remaining-k,j,stop):
            yield (j,)+rest

assert ip(b,seeds[0])==DB
for n in range(2,p+1):
    stop=len(orders)
    for forest in forests(n-1,0,stop):
        e=tuple(prod(images[j][i] for j in forest) for i in range(s))
        t=n*prod(densities[j] for j in forest)
        assert t*ip(b,e)==DB*DA**(n-1), (n,forest)
        orders.append(n)
        densities.append(t)
        if n<p:
            seeds.append(e)
            images.append(apply(e))
    counts.append(len(orders)-stop)
assert counts==[1,1,2,4,9,20,48,115,286,719,1842,4766]
v=(1,)*s
for _ in range(p):v=apply(v)
tall=Q(factorial(p+1)*ip(b,v),DB*DA**p)-1
bush=Q((p+1)*ip(b,tuple(sum(row)**p for row in A)),DB*DA**p)-1
assert tall==Q(P["thirteenth_tall_defect"])==Q(-231,1024)
assert bush==Q(P["thirteenth_bush_defect"])
assert factorial(12)%abs(tall.numerator)==0
assert factorial(12)**2%tall.denominator==0
print("checked",sum(counts),"trees by order",counts)
print("A denominator",DA,"b denominator",DB,"common",P["common_denominator"],
      "divides (12!)^"+str(P["common_factorial_exponent"]))
print("next tall",tall,"next bush",bush)
