#!/usr/bin/env python3
"""Independent arithmetic only; the Lean kernel does not call Python."""
from itertools import product, combinations
from math import isqrt
H=[10001880,-952560,26460,-280,1]
def ev(h,x,p):
    v=0
    for a in h[::-1]:v=(x*v+a)%p
    return v
def poly_roots(xs):
    a=[1]
    for x in xs:
        a=[(a[i-1] if i else 0)-x*(a[i] if i<len(a) else 0) for i in range(len(a)+1)]
    return a
for p,grid in [(191,[45,57,80,98]),(353,[41,111,161,320])]:
    assert all(p%i for i in range(2,isqrt(p)+1))
    assert grid==[x for x in range(p) if ev(H,x,p)==0]
    assert [a%p for a in H]==[a%p for a in poly_roots(grid)]
    print(f"Split p={p}: {grid}; monic product and squarefreeness verified")
    if p!=191:continue
    assert all((3*h*h-4*(a+b)*h+6*a*b)%p for a,b,h in product(grid,repeat=3))
    count=0
    for d in range(3):
        for t in combinations([0]+grid,d):
            f=poly_roots(t)
            for w in grid:
                assert sum((12//(i+2))*a*w**(i+2) for i,a in enumerate(f))%p
                count+=1
    assert count==64
    print("All 64 triples including repeats and all 16 × 4 divisor first moments are nonzero")
