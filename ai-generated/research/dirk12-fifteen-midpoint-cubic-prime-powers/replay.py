#!/usr/bin/env python3
"""Newton-lift the exact DIRK12 constructor; replay every rooted condition."""
from fractions import Fraction as Q
from pathlib import Path
import json, sys
from functools import cache
from math import prod
root = Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent
real = root/'dirk12-fifteen-midpoint-real-upper'
sys.path.insert(0,str(real))
from construct import ev,support,construct
field=json.loads((root/'dirk12-fifteen-rank3-invisible-midpoint-zero-fourth-projection'/'field.json').read_text())
literal=json.loads((root/'dirk12-fifteen-f17-cubic-midpoint-upper'/'tableau.json').read_text())
assert literal['base']==[10,3,7,1] and not literal['orientation']
assert all((i**3+7*i**2+3*i+10)%17 for i in range(17))
mod=17
class E:
    def __init__(self,z):
        if isinstance(z,E): self.a=z.a
        elif isinstance(z,(list,tuple)):
            assert len(z)==3
            self.a=tuple(v%mod for v in z)
        else:
            r=Q(z); self.a=(r.numerator*pow(r.denominator,-1,mod)%mod,0,0)
    def __eq__(self,z):return self.a==E(z).a
    def __bool__(self):return any(t%17 for t in self.a)
    def __add__(self,z):return E(tuple(a+b for a,b in zip(self.a,E(z).a)))
    __radd__=__add__
    def __neg__(self):return E(tuple(-b for b in self.a))
    def __sub__(self,z):return self+-E(z)
    def __rsub__(self,z):return E(z)+-self
    def __mul__(self,z):
        term=[0]*5
        for i,a in enumerate(self.a):
            for j,b in enumerate(E(z).a):term[i+j]+=a*b
        for i in (4,3):
            for j,b in enumerate((10,3,7)):term[i-3+j]-=b*term[i]
        return E(term[:3])
    __rmul__=__mul__
    def __pow__(self,k):
        if k<0:
            assert self,('nonunit',self.a)
            k %= (17**3-1)*(mod//17)**3
        r=E(1); z=self
        while k:
            if k&1:r*=z
            k//=2
            if k:z*=z
        return r
    def __truediv__(self,z):return self*(E(z)**(-1))
    def __rtruediv__(self,z):return E(z)*(self**(-1))
    def res(self):return tuple(r%17 for r in self.a)

def lift(cs,z,k):
    z=E(z.res()); seed=z.res()
    ds=[i*a for i,a in enumerate(cs) if i]
    dr=ev(ds,z); assert dr
    for _ in range((k-1).bit_length()): z-=ev(cs,z)/ev(ds,z)
    assert ev(cs,z)==0 and z.res()==seed
    return z,dr.res()
@cache
def trees(n):
    if n==1:return ((),)
    pool=[(i,t) for i in range(1,n) for t in trees(i)]
    def forests(rem,start):
        if not rem:
            yield ();return
        for j in range(start,len(pool)):
            w,t=pool[j]
            if w>rem: break
            for tail in forests(rem-w,j):yield (t,)+tail
    return tuple(forests(n-1,0))
@cache
def size(t):return 1+sum(map(size,t))
@cache
def density(t):return size(t)*prod(map(density,t))
def replay(k):
    global mod
    mod=17**k
    a0,x0,y0,t0,f0,d0,v0=map(E,literal['midpoint'])
    a=E(Q(1,2)); assert a.res()==a0.res()
    x,dx=lift(field['x'],x0,k)
    def ex(row):return ev([Q(*r) for r in row],x)
    y,t=ex(field['y']),ex(field['t'])
    f,df=lift([ex(r) for r in field['f']],a*f0,k)
    _,s,p,_=support(a,x,y,t,f)
    d,dd=lift([p,-s,1],d0,k)
    assert (dx,df,dd)==((8,14,5),(16,4,10),(12,5,4))
    assert y.res()==y0.res() and t.res()==t0.res() and (s-d).res()==v0.res()
    A,b,c=construct(a,x,y,t,f,d,E)
    assert [[list(v.res()) for v in row] for row in A]==literal['A']
    assert [list(v.res()) for v in b]==literal['b'] and [list(v.res()) for v in c]==literal['c']
    assert all(c[i]==sum(A[i]) and all(v==0 for v in A[i][i+1:]) for i in range(15))
    assert tuple(i+1 for i,v in enumerate(b) if v==0)==(2,3,4,5)
    assert A[0][0]==A[-1][-1]==0 and len({A[i][i].res() for i in range(15)})>2
    @cache
    def stage(tree):
        src=[incoming(t) for t in tree]
        return tuple(prod(v[i] for v in src) for i in range(15))
    @cache
    def incoming(tree):
        src=stage(tree)
        return tuple(sum(v*u for v,u in zip(row,src) if v!=0) for row in A)
    def weighted(tree):return sum(v*u for v,u in zip(b,stage(tree)) if v!=0)
    count=0
    for n in range(1,13):
        for tree in trees(n):
            assert density(tree)*weighted(tree)==1,(k,tree)
            count+=1
    assert count==7813
    v=13*weighted(((),)*12)-1
    assert v and v.res()==tuple(literal['scaled_order13_star'])
    print(f'17^{k}: {count} rooted conditions; scaled order-13 bush {v.a}; residue {v.res()}',flush=True)
for k in map(int,(sys.argv[2] if len(sys.argv)>2 else '1,2,3,8,20').split(',')):
    assert k>0
    replay(k)
