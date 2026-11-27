#!/usr/bin/env python3
"""Find and exactly audit finite-prime repairs of the rational 11-stage chart."""
from fractions import Fraction
from itertools import permutations
from math import lcm
from random import Random
from pathlib import Path
import json
import sympy as sym
import construct as c
from replay import D
P=11
class Q:
    __slots__=['x']
    def __init__(self,n=0,d=1):
        if isinstance(n,Q):
            self.x=n.x
        elif isinstance(n,Fraction):
            self.x=n.numerator*pow(n.denominator,-1,P)%P
        else:
            self.x=int(n)*pow(int(d),-1,P)%P
    def __bool__(self): return self.x!=0
    def __int__(self):return self.x
    def __repr__(self):return str(self.x)
    def __add__(self,q):return Q(self.x+Q(q).x)
    __radd__=__add__
    def __neg__(self):return Q(-self.x)
    def __sub__(self,q):return self+-Q(q)
    def __rsub__(self,q):return Q(q)+-self
    def __mul__(self,q):return Q(self.x*Q(q).x)
    __rmul__=__mul__
    def __truediv__(self,q):return Q(self.x,Q(q).x)
    def __rtruediv__(self,q):return Q(q)/self
    def __pow__(self,q):return Q(pow(self.x,q,P))
    def __eq__(self,q):return self.x==Q(q).x
    def __hash__(self):return self.x

def moments(poly,k=0):
    return sum(z/(i+k+1) for i,z in enumerate(poly))

def quad(h,g):
    hull=[Q(1)]
    for a in (Q(0),Q(1),h,g):
        hull=c.poly_mul(hull,[-a,Q(1)])
    m=[moments(hull,k) for k in range(4)]
    det=m[0]*m[2]-m[1]**2
    if not det:
        return None
    s=(m[0]*m[3]-m[1]*m[2])/det
    t=(m[1]*m[3]-m[2]**2)/det
    assert all(m[k+2]-s*m[k+1]+t*m[k]==0 for k in range(2))
    disc=s*s-4*t
    if not disc:
        return None
    d=sym.sqrt_mod(int(disc),P)
    if d is None:
        return None
    u=(s+d)/2
    v=(s-d)/2
    C=(Q(0),h,g,u,v,Q(1))
    if len(set(C))!=6:
        return None
    W=tuple(moments(c.lagrange(C,j)) for j in range(6))
    if not all(W):
        return None
    assert all(sum(w*a**k for a,w in zip(C,W))==Q(1,k+1) for k in range(8))
    return C,W

def find(p):
    global P
    P=p
    c.F=Q
    rnd=Random(P)
    pairs = ((Q(h),Q(g)) for h in range(2,p) for g in range(h+1,p)) if p<90 else (
        (Q(rnd.randrange(2,p)),Q(rnd.randrange(2,p))) for _ in range(300))
    for h,g in pairs:
        if h==g:
            continue
        q=quad(h,g)
        if q is None:
            continue
        nodes,weights=q
        for perm in permutations(range(1,5)):
            js=(0,*perm,5)
            C=[nodes[j] for j in js]
            W=[weights[j] for j in js]
            res=c.construction(C,W,0,a=Q(1,4))
            if isinstance(res,str):
                continue
            A,b,x,clock,_=res
            fail,defect=c.audit(A,b)
            assert not fail, (p,fail)
            return {'p':p,'x':int(x),'clock':list(map(int,clock)),
                    'A':[[int(w) for w in row[:i]] for i,row in enumerate(A)],
                    'b':list(map(int,b)),'bush9':int(defect)}
    return None

if __name__=='__main__':
    primes=sorted(p for p in sym.factorint(D) if p>=11)
    result=[]
    for p in primes:
        found=find(p)
        if found is not None:
            result.append(found)
        print(p,'ok, x='+str(found['x']) if found else 'no chart found')
    path=Path(__file__).with_name('finite-prime-tableaux.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print("verified prime repair tableaus",len(result),"of",len(primes))
