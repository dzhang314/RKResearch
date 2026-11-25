#!/usr/bin/env python3
"""All six symbolic Lobatto clean chronologies; no search over off nodes."""
from fractions import Fraction as F
from itertools import permutations
from math import prod

class K:
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)
    @staticmethod
    def of(x): return x if isinstance(x,K) else K(x)
    def __add__(self, o):
        o=K.of(o); return K(self.a+o.a,self.b+o.b)
    __radd__=__add__
    def __neg__(self): return K(-self.a,-self.b)
    def __sub__(self,o): return self+-K.of(o)
    def __rsub__(self,o): return K.of(o)+-self
    def __mul__(self,o):
        o=K.of(o); return K(self.a*o.a+F(3,7)*self.b*o.b,self.a*o.b+self.b*o.a)
    __rmul__=__mul__
    def inv(self):
        n=self.a*self.a-F(3,7)*self.b*self.b
        assert n
        return K(self.a/n,-self.b/n)
    def __truediv__(self,o): return self*K.of(o).inv()
    def __rtruediv__(self,o): return K.of(o)*self.inv()
    def __pow__(self,n): return prod([self]*n, start=K(1))
    def __eq__(self,o):
        o=K.of(o);return self.a==o.a and self.b==o.b
    def __repr__(self): return f"({self.a},{self.b})"

c=[K(F(1,2),F(-1,2)), K(F(1,2)), K(F(1,2),F(1,2))]
one=K(1)
for ix in permutations(range(3)):
    h,x,z=(c[i] for i in ix)
    E=h/4-(x+z)/3+x*z/(2*h)
    assert E!=0
    th=(x/3-h/4)/E
    p0,p1,p2=th*x*z+2*h*x,-th*(x+z)-4*x-3*h,th+5
    P=lambda X:p0+p1*X+p2*X**2
    Qp=lambda u:prod((u-v for v in [K(0),h,x,z] if v!=u),start=K(1))
    assert all(P(u)!=0 for u in [K(0),h,x,z]) and p2!=0
    C=[sum((u**r/(P(u)*Qp(u)) for u in [K(0),h,x,z]),start=K()) for r in range(5)]
    assert p0*h**2/2+p1*h**3/3+p2*h**4/4==0
    assert all(p2*C[j+2]+p1*C[j+1]+p0*C[j]==0 for j in range(3))
    D=C[1]*C[3]-C[2]**2
    assert D!=0
    F5=C[4]-2*p0/p2*C[2]
    F4=C[4]-2*h*C[3]+h**2*C[2]
    assert F5!=0 and F4!=0
    print("".join("LCR"[i] for i in ix),"p2",p2,"h5= C4−2p0/p2 C2",F5,"h4",F4)
print("PASS six symbolic chronologies; (a,b) means a+b·sqrt(3/7).")
