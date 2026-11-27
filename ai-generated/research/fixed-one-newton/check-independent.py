import json, sys
from functools import cache
from math import prod
from pathlib import Path
@cache
def trees(n):
    if n==1: return ((),)
    out=[]
    ts=[(s,t) for s in range(1,n) for t in trees(s)]
    def go(rem, i, seq):
        if not rem: out.append(tuple(seq)); return
        for j in range(i,len(ts)):
            s,t=ts[j]
            if s>rem:break
            go(rem-s,j,seq+[t])
    go(n-1,0,[])
    return tuple(out)
@cache
def size(t): return 1+sum(map(size,t))
@cache
def fact(t): return size(t)*prod(map(fact,t))
for name in sys.argv[1:]:
    d=json.loads(Path(name).read_text()); A=d['a_integer']; B=d['b_integer']; ad=d['a_denominator']; bd=d['b_denominator']; p=d['order']; n=len(A)
    assert len(B)==n and all(len(row)==n and row[i]==ad and not any(row[i+1:]) for i,row in enumerate(A))
    sparse=[[(j,a) for j,a in enumerate(row) if a] for row in A]
    @cache
    def phi(t):
        if not t: return [1]*n
        return [prod(vals) for vals in zip(*(aphi(s) for s in t))]
    @cache
    def aphi(t):
        v=phi(t)
        return [sum(a*v[j] for j,a in r) for r in sparse]
    ct=[]
    for k in range(1,p+1):
        vals=trees(k); ct.append(len(vals))
        for t in vals:
            assert fact(t)*sum(x*y for x,y in zip(B,phi(t))) == bd*ad**(k-1), (name,k,t)
    t=((),)*p
    from fractions import Fraction
    defect=Fraction(fact(t)*sum(x*y for x,y in zip(B,phi(t))),bd*ad**p)-1
    assert defect
    print(n,p,ct,sum(ct),defect,flush=True)
