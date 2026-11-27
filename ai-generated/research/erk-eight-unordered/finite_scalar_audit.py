#!/usr/bin/env python3
"""Audit the three four-off clean chronologies in Q[w]/(w²-3/7)."""
from fractions import Fraction as R
from itertools import permutations,product
from math import prod,gcd, isqrt
from collections import defaultdict

class K:
    def __init__(self,a=0,b=0):self.a,self.b=R(a),R(b)
    @staticmethod
    def mk(q):return q if isinstance(q,K) else K(q)
    def __add__(self,q):
        q=K.mk(q);return K(self.a+q.a,self.b+q.b)
    __radd__=__add__
    def __neg__(self):return K(-self.a,-self.b)
    def __sub__(self,q):return self+-K.mk(q)
    def __rsub__(self,q):return K.mk(q)+-self
    def __mul__(self,q):
        q=K.mk(q);return K(self.a*q.a+R(3,7)*self.b*q.b,self.a*q.b+self.b*q.a)
    __rmul__=__mul__
    def conj(self):return K(self.a,-self.b)
    def norm(self):return self.a*self.a-R(3,7)*self.b*self.b
    def __truediv__(self,q):
        q=K.mk(q);return self*q.conj()*K(1/q.norm())
    def __rtruediv__(self,q):return K.mk(q)/self
    def __pow__(self,k):return prod([self]*k,start=K(1))
    def __eq__(self,q):q=K.mk(q);return (self.a,self.b)==(q.a,q.b)
    def __repr__(self):return f'({self.a},{self.b})'

def primes(a):
    a=abs(a);t=2;s=set()
    while t*t<=a:
        if a%t==0:
            s.add(t)
            while a%t==0:a//=t
        t+=1
    if a>1:s.add(a)
    return s
S=[K(R(1,2),R(-1,2)),K(R(1,2)),K(R(1,2),R(1,2))]
exception=defaultdict(set)
for ix in ((0,1,2),(0,2,1),(1,0,2)):
    h,x,z=[S[i] for i in ix]
    E=h/4-(x+z)/3+x*z/(2*h)
    ratio=(x/3-h/4)/E
    p0=ratio*x*z+2*h*x
    p1=-ratio*(x+z)-4*x-3*h
    p2=ratio+5
    P=lambda u:p0+p1*u+p2*u**2
    nodes=[K(0),h,x,z]
    Qp=lambda u:prod((u-v for v in nodes if u!=v),start=K(1))
    C=[sum((u**r/(P(u)*Qp(u)) for u in nodes),start=K()) for r in range(5)]
    obs={
        'E':E,'p0':p0,'p2':p2,'Ph':P(h),'Px':P(x),'Pz':P(z),
        'hankel':C[1]*C[3]-C[2]**2,
        'last':C[4]-2*p0/p2*C[2],
        'double':2*z-h,
    }
    print(''.join('LCR'[i] for i in ix))
    for tag,f in obs.items():
        assert f.norm()
        # Numerator/denominator of both coordinates and nonzero norm
        # are checked; zeros at newly bad primes need a separate branch.
        bad=(primes(f.norm().numerator)|primes(f.a.denominator)|primes(f.b.denominator))-{2,3,5,7}
        for p in bad:exception[p].add(''.join('LCR'[i] for i in ix)+':'+tag)
        print(' ',tag,str(f),str(f.norm()),sorted(bad))
print('Prime/modular guards:',{p:sorted(t) for p,t in sorted(exception.items())})
for p in sorted(exception):
    sq=(3*pow(7,-1,p))%p
    for w in range(p):
        if w*w%p!=sq:continue
        nodes=[(1-w)*pow(2,-1,p)%p,pow(2,-1,p),(1+w)*pow(2,-1,p)%p]
        for ix in permutations(range(3)):
            h,x,z=[nodes[i] for i in ix]
            ee=(3*h*h-4*h*(x+z)+6*x*z)%p
            nn=(4*h*x-3*h*h)%p
            if not ee:
                print(p, tuple(nodes[i] for i in ix),'E0 k=0 if N!=0',nn)
                continue
            th=nn*pow(ee,-1,p)%p
            p0,p1,p2=(th*x*z+2*h*x)%p,(-th*(x+z)-4*x-3*h)%p,(th+5)%p
            sqr=lambda u:(p0+p1*u+p2*u*u)%p
            if any(sqr(u)==0 for u in [0,h,x,z]):
                print(p, tuple(nodes[i] for i in ix),'P at roots',(p0,sqr(h),sqr(x),sqr(z)))
                continue
            if not p2:
                print(p,tuple(nodes[i] for i in ix),'linear P',p0,p1)
                continue
            W=[pow(sqr(u)*prod((u-v) for v in [0,h,x,z] if v!=u)%p,-1,p) for u in [0,h,x,z]]
            C=[sum(w*pow(u,k,p) for w,u in zip(W,[0,h,x,z]))%p for k in range(5)]
            gate=(C[1]*C[3]-C[2]**2)*(C[4]-2*p0*pow(p2,-1,p)*C[2])%p
            if not gate:print(p,tuple(nodes[i] for i in ix),'valid quadratic guard degeneracy',C)
            if not (h-2*z)%p:print('unexpected double gate')
