#!/usr/bin/env python3
"""Exact scalar replay for the exceptional ERK8 characteristic.

The pair algebra is F_11[X]/(X^2-X+8), not a bounded tableau search.
Its identities therefore hold for the two q-roots in every extension.
Every fraction/inverse uses an exactly checked finite computation.
"""
from dataclasses import dataclass
from itertools import permutations
from math import prod

P=11
@dataclass(frozen=True)
class F:
    a:int=0
    b:int=0
    def __post_init__(self):
        object.__setattr__(self,'a',self.a%P)
        object.__setattr__(self,'b',self.b%P)
    @staticmethod
    def c(q):return q if isinstance(q,F) else F(q)
    def __add__(self,q):
        q=F.c(q)
        return F(self.a+q.a,self.b+q.b)
    __radd__=__add__
    def __neg__(self):return F(-self.a,-self.b)
    def __sub__(self,q):return self+-F.c(q)
    def __rsub__(self,q):return F.c(q)+-self
    def __mul__(self,q):
        q=F.c(q)
        return F(self.a*q.a+3*self.b*q.b,self.a*q.b+self.b*q.a+self.b*q.b)
    __rmul__=__mul__
    def __pow__(self,n):
        return prod([self]*n,start=F(1))
    def inv(self):
        out=[F(a,b) for a in range(P) for b in range(P) if self*F(a,b)==F(1)]
        assert len(out)==1,self
        return out[0]
    def __truediv__(self,q):return self*F.c(q).inv()
    def __rtruediv__(self,q):return F.c(q)*self.inv()
    def nz(self):return self!=F()

x=F(0,1); z=1-x; h=F(6); q=lambda t:t*t-t+8
assert [a for a in range(11) if (a*a-a+8)%11==0]==[]
assert x+z==F(1) and x*z==F(8) and q(x)==q(z)==F()
assert q(h)==F(5) and q(F(7))==F(6)
assert (3*F(7)+1)==F() and 14*F(7)**3-21*F(7)**2+9*F(7)-1==F(7)
assert 14*h**3-21*h**2+9*h-1==F() and 91*h*h-105*h+27==F()

def primitive_eval(coeff,t):
    return sum((t**(j+1)*a/(j+1) for j,a in enumerate(coeff)),start=F())

# All four noncenter quadrature orientations as literal paid arithmetic.
G=(x,h,z)
for a,b,d in permutations(G):
    if a==h:continue
    E=a/4-(b+d)/3+b*d/(2*a)
    assert E.nz()
    th=(b/3-a/4)/E
    p0=th*b*d+2*a*b
    p1=-th*(b+d)-4*b-3*a
    p2=th+5
    assert p2.nz()
    Q=lambda t:p0+p1*t+p2*t*t
    g=(F(),a,b,d)
    assert all(Q(u).nz() for u in g)
    C=[sum((u**j/(Q(u)*prod(u-v for v in g if u!=v)) for u in g),start=F())
          for j in range(5)]
    assert (C[1]*C[3]-C[2]**2).nz()
    assert (C[4]-2*p0/p2*C[2]).nz()
    assert (a-2*d).nz()

# Clean-star value in the omitted h grid, and high-off weight anchor.
for k in range(8):
    nodes=(F(),h,x,z,F(1))
    W=(5,5,4,4,5)
    assert sum(w*t**k for w,t in zip(W,nodes))==F(1)/(k+1)
cleanH=(0,6,-7,1)
assert primitive_eval(cleanH,F(1))==F()
assert primitive_eval((0,*cleanH),F(1))==F(1)

# In the first three off rows before h, X q and the sentinel polynomials.
xq=(0,8,-1,1)
sentinel=(0,-48,2,1)
assert primitive_eval(xq,x)==F(3,9) and primitive_eval(xq,z)==3+9*z
assert primitive_eval(xq,h)==F()
assert [h**j/(j) for j in (2,3,4)]==[F(7),F(6),F(5)]
assert x*(1-x)==F(8)  # N3^{-1} has zero constant when h immediately follows
assert sum(a*x**i for i,a in enumerate(sentinel))==9*(1-x)
assert primitive_eval(sentinel,x)==F(10,7)
assert ((F(10,7))/(1-x))==F(-2,1)*F(7)/2
assert (1-x)*(x-2)==F(6,2)

# Four off before h: raw residue sequence and terminal Newton coefficients.
L=[F(v) for v in (10,4,1,2,5)]
assert all(8*L[j]-L[j+1]+L[j+2]==F() for j in (0,1,2))
assert L[4]==2*8*L[2] and (L[1]*L[3]-L[2]**2).nz()
assert all(-(L[i]+L[i-1])==L[i]/i for i in (2,3,4))
assert (x+6)*(7-x)==F(6)
assert (x+1)*(x+2)==7*(7-x)  # (X+2)(X+1) has the same remainder line
assert [(F(2,1).inv()*x**j).b for j in range(4)]==[7,8,7,9]
assert (F(2,1).inv()*x**2).b==(F(2,1).inv()).b
assert F((F(2,1).inv()*x**3).b)==6*F((F(2,1).inv()).b)

# Four-off late ratio and, for the full five-off tail, the same products.
Dx=6+2*x;Dz=6+2*z
U=Dx*z*z;V=Dz*x*x
assert U==V==F(7)
assert Dx*z==5*x and Dz*x==5*z
assert Dz*x**3+Dx*z**2*(3*x-2*z)==14*(2*x-z)
assert (2*x-z).nz()
for e in (F(),F(1)): # affine in e; these two coefficients prove the identity
    G=3*(U*(x-e)+V*(z-e))*(U+V)-2*(Dx*z*(x-e)+Dz*x*(z-e))*(U*z+V*x)
    assert G==2-e

# High-off hull and the computed degree-two tail residues.
assert sum(a*x**i for i,a in enumerate(cleanH))==F(4,3)
assert (6+2*x)*(1+7*x)==F(4,3)
assert (1+7*x)*(x+2)==F(1)
b=[F(-((x+2)*(1-x)**k).b) for k in range(4)]
assert b==[F(10),F(2),F(10),F(5)] and b[3]/b[2]==F(1)/2
assert 3*(1-x)**2-(1-x)==-2*x
assert (1-F(2))/(-F(8))==F(7)

print('All characteristic-eleven scalar receipts passed in the exact quadratic algebra.')
