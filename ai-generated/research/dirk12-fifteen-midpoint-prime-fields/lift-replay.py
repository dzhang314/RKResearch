#!/usr/bin/env python3
"""Exact base-prime Hensel ladders, without polynomial factoring dependencies."""
from fractions import Fraction as Q
from pathlib import Path
import json, runpy, sys
here=Path(__file__).resolve().parent
research=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else here.parent
sys.path.insert(0,str(research/'dirk12-fifteen-midpoint-real-upper'))
from construct import construct,ev,support
direct=runpy.run_path(str(here/'all-rooted.py'))['direct']
F=json.loads((research/'dirk12-fifteen-rank3-invisible-midpoint-zero-fourth-projection'/'field.json').read_text())
q=2; prime=2
class E:
    def __init__(self,v):
        if isinstance(v,E):self.v=v.v
        else:
            r=Q(v); self.v=r.numerator*pow(r.denominator,-1,q)%q
    def __eq__(self,v):return self.v==E(v).v
    def __bool__(self):return bool(self.v%prime)
    def __add__(self,v):return E(self.v+E(v).v)
    __radd__=__add__
    def __neg__(self):return E(-self.v)
    def __sub__(self,v):return self+-E(v)
    def __rsub__(self,v):return E(v)+-self
    def __mul__(self,v):return E(self.v*E(v).v)
    __rmul__=__mul__
    def __pow__(self,k):return E(pow(self.v,k,q))
    def __truediv__(self,v):return self*E(v)**-1
    def __rtruediv__(self,v):return E(v)*self**-1
def lift(cs,seed,k):
    z=E(seed); df=[i*E(a) for i,a in enumerate(cs) if i]
    d=ev(df,z);assert d
    for _ in range((k-1).bit_length()):z-=ev(cs,z)/ev(df,z)
    assert ev(cs,z)==0 and z.v%prime==seed
    return z,d.v%prime
def replay(lit,k):
    global q,prime
    prime=lit['p'];q=prime**k
    a=E(Q(1,2)); assert a.v%prime==lit['a']
    assert E(F['x'][-1])
    x,g1=lift(F['x'],lit['x'],k)
    def ex(row):return ev([Q(*r) for r in row],x)
    y,t=ex(F['y']),ex(F['t'])
    assert y.v%prime==lit['y'] and t.v%prime==lit['t']
    f,g2=lift([ex(r) for r in F['f']],lit['f'],k)
    _,s,p,_=support(a,x,y,t,f)
    d,g3=lift([p,-s,1],lit['d'],k)
    A,b,c=construct(a,x,y,t,f,d,E)
    dt=dict(A=[[E(z).v for z in row] for row in A],b=[E(z).v for z in b],c=[E(z).v for z in c],
            x=x.v,f=f.v,d=d.v,defect=(13*sum(w.v*pow(z.v,12,q) for z,w in zip(c,b))-1)%q)
    assert [[z%prime for z in row] for row in dt['A']]==lit['A']
    assert [z%prime for z in dt['b']]==lit['b'] and [z%prime for z in dt['c']]==lit['c']
    assert dt['defect']%prime==lit['defect']
    direct(dt,prime,k)
    return g1,g2,g3
for filename in ('witness-131-111-57-85.json','witness-149-103-41-106.json'):
    data=json.loads((here/filename).read_text())
    g=replay(data,1)
    print('successive derivative residues', g, flush=True)
    for k in (2,3,8,20):assert replay(data,k)==g
