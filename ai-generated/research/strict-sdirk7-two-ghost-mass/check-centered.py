#!/usr/bin/env python3
"""Exact centered Christoffel scalar closure and primitive five-adic coefficients."""
from flint import fmpq, fmpq_poly
from fractions import Fraction
from math import prod, lcm, gcd
from flint import nmod_poly
F=fmpq_poly
x=F([0,1]); f=x**3+105*x*x+4800*x+128000
class K:
    def __init__(self,a=0,b=0,d=1):
        # flint accepts exact fmpq coefficients, not Python Fraction.
        cv=lambda t:(F([fmpq(t.numerator,t.denominator)]) if isinstance(t,Fraction) else F(t))
        self.a,self.b,self.d=map(cv,(a,b,d))
        if not self.d:raise ZeroDivisionError
        g=self.a.gcd(self.b).gcd(self.d)
        self.a=self.a//g;self.b=self.b//g;self.d=self.d//g
        sc=self.d[self.d.degree()]
        self.a=self.a/sc;self.b=self.b/sc;self.d=self.d/sc
    def __add__(self,w):
        w=w if isinstance(w,K) else K(w)
        return K(self.a*w.d+w.a*self.d,self.b*w.d+w.b*self.d,self.d*w.d)
    __radd__=__add__
    def __neg__(self):return K(-self.a,-self.b,self.d)
    def __sub__(self,w):return self+-K(w) if not isinstance(w,K) else self+-w
    def __rsub__(self,w):return -self+w
    def __mul__(self,w):
        w=w if isinstance(w,K) else K(w)
        return K(self.a*w.a+f*self.b*w.b,self.a*w.b+self.b*w.a,self.d*w.d)
    __rmul__=__mul__
    def inv(self):return K(self.a*self.d,-self.b*self.d,self.a*self.a-f*self.b*self.b)
    def __truediv__(self,w):return self*(w if isinstance(w,K) else K(w)).inv()
    def __rtruediv__(self,w):return self.inv()*w
    def __pow__(self,n):return prod([self]*n,start=K(1)) if n>=0 else self.inv()**(-n)
    def __repr__(self):return f'<{self.a}|{self.b}>/{self.d}'
    def __bool__(self):return bool(self.a or self.b)
    def __eq__(self,w):return not self-w
    def height(self):return tuple(g.degree() for g in [self.a,self.b,self.d])
    def evaluate(self,x,y):return (self.a(x)+self.b(x)*y)/self.d(x)

X=K(x);Y=K(0,1);u=3+80/X
rho=Fraction(3,5)
A=(u-3)*(2*u*u-10*u+11)
B=-5*(u-3)*(u-2)*(2*u-3)
C=10*(u-2)**2*(u-1)
m=(-B+(u-2)*80*Y/X**2)/(2*A)
assert A*m*m+B*m+C==0
v=2*u-1
M=u*u-4*u+2;T=u**3-7*u*u+10*u-2
J=4*u**3-24*u*u+39*u-17
r0=Fraction(-1,2);r1=M/2;r2=M*J/(2*T)
q0=(u-2)*(u-1)**2/T
q1=-(u-3)*(u-1)*(2*u-3)/T
q2=(u-3)*(u-2)**2/(2*T)
g=lambda w:5*w*w-10*m*w+2*m*m
L1=(g(u)/r1-g(1)/r0)/(u-1);L0=g(1)/r0-L1
assert g(v)/r2==L0+L1*v
E1=q2*(2/M-2)/3+1/M
F4=q2/3*L1
F3=q2/3*L0+(q1/2-q2)*L1+5*E1
c=-F3/F4-3*u
a,b,d=[w/m-1 for w in (1,u,v)]
f1,f2=[5*b*d/9+Fraction(1,3),5*a*d/9+Fraction(1,3)]
g1,g2=[-(b+d)/3,-(a+d)/3]
det=f1*g2-g1*f2
n=(g2/r0-g1/r1)/det
k=(f1/r1-f2/r0)/det
scale=-Fraction(4,175)/(k*(Fraction(1,5)+(a*b+a*d+b*d)/3)-n*((a+b+d)/3+5*a*b*d/9))
n,k=n*scale,k*scale
w=c/m-1
s1=-(k*w+n)/(w*w-rho);s0=k-rho+w*s1
disc=s1*s1-4*s0

# Clear the square denominator of the discriminant in the elliptic function field.
den_unit,den_factors=disc.d.factor()
assert den_unit==fmpq(1,289**2)
assert [(D.degree(),k) for D,k in den_factors]==[(3,2),(12,2)]
assert den_unit*prod((D**k for D,k in den_factors),start=F(1))==disc.d

def rootless(D,ell):
    assert all(z.denominator==1 for z in D.coeffs())
    mod=nmod_poly([int(t) for t in D.coeffs()],ell)
    assert mod.degree()==D.degree() and not mod.roots()

rootless(den_factors[0][0],19)
rootless(den_factors[1][0],7)
assert m.d==x*x-160*x-12800
assert c.d==x**3+96*x*x+3840*x+102400
rootless(m.d,7)
rootless(c.d,17)
FN=F4.a*F4.a-f*F4.b*F4.b
assert FN==FN[FN.degree()]*x**4*(x+40)**2*(x+80)**4*m.d**2*c.d
assert scale.d==x*x*(x+40)*c.d
for ell in (13,17):
    ff=nmod_poly([int(z) for z in f.coeffs()],ell)
    assert ff.gcd(ff.derivative()).degree()==0

D=lcm(*(int(t.denominator) for t in [*disc.a.coeffs(),*disc.b.coeffs()]))
NA=[int(t*D) for t in disc.a.coeffs()]; NB=[int(t*D) for t in disc.b.coeffs()]
zeta=gcd(*NA,*NB,D)
NA=[a//zeta for a in NA];NB=[b//zeta for b in NB];D//=zeta
assert D==5*2023**2 and len(NA)==31 and len(NB)==29
assert NA[-1]==42007017 and NA[-1]%5==2
assert all(t%5==0 for t in [*NA[:-1],*NB])
NA5=[a*5**i//5**30 for i,a in enumerate(NA)]
NB5=[b*5**(i+1)//5**30 for i,b in enumerate(NB)]
assert all(c*5**30==a*5**i for i,(a,c) in enumerate(zip(NA,NA5)))
assert all(c*5**30==b*5**(i+1) for i,(b,c) in enumerate(zip(NB,NB5)))
assert [i for i in range(5) if not (i**3+21*i*i+192*i+1024)%5]==[2]
assert sum(a*2**i for i,a in enumerate(NA5))%5==2

def count(p):
    return 1+sum(int(f(i))%p==j*j%p for i in range(p) for j in range(p))
assert count(13)==13 and count(17)==12
assert [m.evaluate(-16,Y0) for Y0 in (-272,272)]==[fmpq(12,13),fmpq(8,3)]
assert [c.evaluate(-16,Y0) for Y0 in (-272,272)]==[fmpq(11,5),fmpq(123,25)]
assert [disc.evaluate(-16,Y0) for Y0 in (-272,272)]==[
    fmpq(739528494915468,272467331584805),fmpq(-1295886188076,36207447941315)]

# Tie the formula replay to the literal native receipt.
from pathlib import Path
import re
native=Path(__file__).resolve().parents[2]/"lean/RKCert/Research/SDIRKSevenChristoffelCentered.lean"
source=native.read_text()
for label,coefficients in [("numA",NA),("numB",NB)]:
    pat=rf"def {label} : List ℤ :=\s*\[([^\]]+)\]"
    assert [int(a) for a in re.search(pat,source).group(1).split(",")]==coefficients

if __name__=="__main__":
    print("centered elliptic model and square denominator verified")
    print("all rational early-fourth pivots covered")
    print("primitive mod-five split obstruction: a=5a0,b=5b0, a0/d²=2,b0=0 mod5")
