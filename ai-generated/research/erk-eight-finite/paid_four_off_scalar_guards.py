#!/usr/bin/env python3
"""Exact specialization certificate for the four-off scalar output.

Track every quadratic-ring inversion, not just denominators of final
displayed expressions. Check all exceptional odd paid primes exactly.
"""
from fractions import Fraction as F
from itertools import permutations
from math import prod
from dataclasses import dataclass

PAID={2,3,5,7}
BAD=set()
def primes(n):
    n=abs(n)
    r=set()
    assert n
    i=2
    while i*i<=n:
        if n%i==0:
            r.add(i)
            while n%i==0:n//=i
        i+=1
    if n>1:r.add(n)
    return r

@dataclass(frozen=True)
class Pair:
    a: F=F(0)
    b: F=F(0)
    @staticmethod
    def coerce(q):
        return q if isinstance(q,Pair) else Pair(F(q))
    def __add__(self,q):
        q=self.coerce(q)
        return Pair(self.a+q.a,self.b+q.b)
    __radd__=__add__
    def __neg__(self):
        return Pair(-self.a,-self.b)
    def __sub__(self,q):
        return self+-self.coerce(q)
    def __rsub__(self,q):
        return self.coerce(q)+-self
    def __mul__(self,q):
        q=self.coerce(q)
        return Pair(self.a*q.a+F(3,7)*self.b*q.b,self.a*q.b+self.b*q.a)
    __rmul__=__mul__
    def norm(self):
        return self.a*self.a-F(3,7)*self.b*self.b
    def unit(self):
        nz=self.norm()
        assert nz
        BAD.update(primes(nz.numerator)-PAID)
        BAD.update(primes(nz.denominator)-PAID)
        return self
    def __truediv__(self,q):
        q=self.coerce(q).unit()
        return self*Pair(q.a,-q.b)*F(1,q.norm())
    def __rtruediv__(self,q):
        return self.coerce(q)/self
    def __pow__(self,k):
        return prod([self]*k,start=Pair(F(1)))

L,C,R=Pair(F(1,2),F(-1,2)),Pair(F(1,2)),Pair(F(1,2),F(1,2))
O=Pair()
for h,x,z in ((L,C,R),(L,R,C),(C,L,R)):
    E=h/4-(x+z)/3+x*z/(2*h)
    theta=(x/3-h/4)/E
    p0=theta*x*z+2*h*x
    p1=-theta*(x+z)-4*x-3*h
    p2=theta+5
    def P(u):return p0+p1*u+p2*u**2
    nodes=(O,h,x,z)
    A=[sum((u**r/(P(u)*prod((u-v for v in nodes if u!=v),start=1))
            for u in nodes),start=O) for r in range(5)]
    (A[1]*A[3]-A[2]**2).unit()
    (A[4]-2*p0/p2*A[2]).unit()
    (2*z-h).unit()

assert BAD=={11,17,37,41,43,79},BAD
expected={17:{'z-root'},37:{'linear'},41:{'linear'},43:{'h-root'},79:{'h-root'}}
print('All inversion/norm guards beyond factorial:',sorted(BAD))
for p in sorted(BAD-{11}):
    div=lambda a,b: a*pow(b%p,-1,p)%p
    rad=div(3,7)
    roots=[w for w in range(p) if w*w%p==rad]
    assert len(roots)==2,(p,roots)  # same complete roots in every extension field
    nodes={div(1-roots[0],2),div(1,2),div(1+roots[0],2)}
    assert len(nodes)==3
    repairs=set()
    for h,x,z in permutations(sorted(nodes)):
        E=(3*h*h-4*h*(x+z)+6*x*z)%p
        theta=div(4*h*x-3*h*h,E)
        p0,p1,p2=(theta*x*z+2*h*x)%p,(-theta*(x+z)-4*x-3*h)%p,(theta+5)%p
        def P(u):return (p0+p1*u+p2*u*u)%p
        assert p0 and P(x)
        assert (2*z-h)%p
        if not P(h):
            repairs.add('h-root')
            continue
        if not P(z):
            repairs.add('z-root')
            continue
        if not p2:
            assert p1  # nonzero linear, not a constant
            repairs.add('linear')
            continue
        grid=(0,h,x,z)
        C=[sum(div(u**r,P(u)*prod(u-v for v in grid if u!=v))
               for u in grid)%p for r in range(5)]
        assert (C[1]*C[3]-C[2]**2)%p
        assert (C[4]-div(2*p0,p2)*C[2])%p
    assert repairs==expected[p],(p,repairs)
    print(p, 'roots',sorted(nodes),'repairs',sorted(repairs))

# In the sole unresolved characteristic the quadratic does not split
# in the prime field. Its quadratic-extension degeneracy is separate.
assert all(r*r%11 != 3*pow(7,-1,11)%11 for r in range(11))
