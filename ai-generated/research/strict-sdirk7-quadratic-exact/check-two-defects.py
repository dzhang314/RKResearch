#!/usr/bin/env python3
"""Independent standard-library replay from the published rational pairs."""
from math import gcd, isqrt, lcm, prod, factorial
from fractions import Fraction as Q
from functools import cache
from pathlib import Path
import json, sys

D = 432969
P_BUSH = (-26022475375,71656598)
P_TALL = (-566828049,156338)
BUSH_DEN = 13671482834240
TALL_DEN = 957274560
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def times(x,y): return (x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def scl(k,v): return (k*v[0],k*v[1])
def sigma(xs):
    s=(0,0)
    for x in xs: s=add(s,x)
    return s
def power(x,n):
    v=(1,0)
    for _ in range(n): v=times(v,x)
    return v
def dot(x,y): return sigma(times(a,b) for a,b in zip(x,y))
def norm(v): return v[0]*v[0]-D*v[1]*v[1]
def root_eval(v,r,m):
    return sum(q.numerator*pow(q.denominator,-1,m)*r**j for j,q in enumerate(map(Q,v)))%m
def trees(n):
    layers=[()]
    @cache
    def size(t): return 1+sum(map(size,t))
    for j in range(2,n+1):
        def forest(f,lo):
            if f==0:
                yield ()
                return
            for j in range(lo,len(layers)):
                t=layers[j]; u=size(t)
                if u>f: break
                for rest in forest(f-u,j):
                    yield (t,)+rest
        nxt=list(forest(j-1,0))
        layers.extend(nxt)
    return layers
@cache
def root_size(t): return 1+sum(map(root_size,t))
@cache
def root_fac(t): return root_size(t)*prod(map(root_fac,t))

def check_mod(A,b,m):
    @cache
    def stage(t):
        parts=[tuple(sum(a*x for a,x in zip(row,stage(u)))%m for row in A) for u in t]
        return tuple(prod(part[i] for part in parts)%m for i in range(9))
    def cash(t): return root_fac(t)*sum(z*v for z,v in zip(b,stage(t)))%m
    cat=trees(7)
    assert len(cat)==85 and all(cash(t)==1 for t in cat)
    tall=()
    for i in range(7): tall=(tall,)
    assert cash(tall)%m!=1

def verify(data):
    A=[[tuple(map(Q,a)) for a in row] for row in data['A']]
    b=[tuple(map(Q,a)) for a in data['b']]
    aDen=lcm(*(p.denominator for row in A for a in row for p in a))
    bDen=lcm(*(p.denominator for a in b for p in a))
    assert aDen%11==0
    c=[sigma(row) for row in A]
    bush=scl(8,dot(b,[power(t,7) for t in c]))
    v=[(1,0)]*9
    for i in range(7): v=[dot(row,v) for row in A]
    tall=scl(factorial(8),dot(b,v))
    assert add(bush,(-1,0))==scl(Q(1,BUSH_DEN),P_BUSH)
    assert add(tall,(-1,0))==scl(Q(1,TALL_DEN),P_TALL)
    n_b,n_t=norm(P_BUSH),norm(P_TALL)
    assert (n_b,n_t)==(-1545982860640624199651,310711594906171965)
    assert 2861460114013366*(-n_b)-14237538492914339107*n_t==11
    assert gcd(n_b,n_t)==11
    m0=4217*27367649
    unit_part=11*13**2*29*248477
    assert unit_part*m0==-n_b and (aDen*bDen)**2%unit_part==0
    rt,st=100201993742,94261408269
    mixed_t=root_eval(P_TALL,rt,m0)
    for p,r,s,t in [(4217,1262,680,2000),(27367649,9030753,7225113,15478482),
                    (m0,rt,st,mixed_t)]:
        if p!=m0:
            assert all(p%d for d in range(2,isqrt(p)+1))
        assert (r*r-D)%p==0 and (2*r*s)%p==1
        assert gcd(aDen*bDen,p)==1
        assert root_eval(P_BUSH,r,p)==0 and root_eval(P_TALL,r,p)==t
        m=p
        for k in range(1,5):
            assert (r*r-D)%m==0
            aa=[[root_eval(a,r,m) for a in row] for row in A]
            bb=[root_eval(z,r,m) for z in b]
            assert all(row[i]*4%m==1 and not any(row[i+1:]) for i,row in enumerate(aa))
            check_mod(aa,bb,m)
            v=(r*r-D)//m
            r=(r-m*s*v)%(m*p)
            m*=p
    print('Both exact tree residuals, their norm combination, and the two prime and mixed-primary towers verified.')

if __name__=='__main__':
    arg=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'strict-sdirk7-quadratic'/'nine-stage-quadratic.json'
    verify(json.loads(arg.read_text()))
