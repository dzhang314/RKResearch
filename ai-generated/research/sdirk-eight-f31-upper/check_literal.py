#!/usr/bin/env python3
"""Standalone integer replay, and optional exact scalar donor match."""
from functools import lru_cache
from math import prod
from pathlib import Path
import json,re,sys
d=Path(__file__).resolve().parent
D=json.loads((d/'witness.json').read_text())
p,A,b=D['prime'],D['A'],D['b']
assert p==31 and len(b)==len(A)==11 and all(len(a)==11 for a in A)
assert all(a[i]==D['gamma'] and not any(a[i+1:]) for i,a in enumerate(A))
assert D['gamma']%p!=0

@lru_cache(None)
def size(t):
    return 1+sum(map(size,t))
@lru_cache(None)
def density(t):
    return size(t)*prod(map(density,t))
@lru_cache(None)
def stage(t):
    children=[stage(q) for q in t]
    return [prod(sum(x*y for x,y in zip(a,s)) for s in children)%p for a in A]
def value(t):return sum(x*y for x,y in zip(b,stage(t)))%p
levels=[[],[()]]
def forests(n,trees,minimum):
    if not n:
        yield ()
    else:
        for a in range(minimum,len(trees)):
            t=trees[a];k=size(t)
            if k>n:break
            for tail in forests(n-k,trees,a):yield (t,)+tail
for n in range(2,9):
    levels.append(list(forests(n-1,sum(levels[1:],[]),0)))
assert list(map(len,levels[1:]))==[1,1,2,4,9,20,48,115]
for ts in levels[1:]:
    for t in ts:
        assert value(t)*density(t)%p==1
bad=((),)*8
assert value(bad)==D['order_nine_bush']==2
assert pow(density(bad),-1,p)==D['order_nine_expected']==7
lean=d.parents[1]/'lean/RKCert/Research/SDIRKEightElevenF31.lean'
s=lean.read_text()
mat=re.search(r'def A.*?!!\[(.*?)\]',s,re.S).group(1)
assert [[int(x) for x in row.split(',')] for row in mat.split(';')]==A
assert [int(x) for x in re.search(r'def b.*?!\[(.*?)\]',s).group(1).split(',')]==b
if '--specialize' in sys.argv:
    from specialize import build
    assert any(M==A and v==b and sd==D['seed']+[D['gamma']] for M,v,sd,_ in build(p))
print('strict F31, order 8 on 11 stages: 200/200 rooted conditions; ninth bush 2 != 7')
