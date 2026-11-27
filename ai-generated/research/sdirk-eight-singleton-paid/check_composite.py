#!/usr/bin/env python3
from resultant_data import K,QQ,as_poly,F,VF,resultant,N,PRIMES
from math import gcd,prod
from pathlib import Path
import re,sys
coef=[as_poly(resultant).get((i,),QQ.zero) for i in range(4)]
assert coef[1]==-coef[2] and coef[3]==0
assert gcd(N,2*3*5*7*prod(PRIMES))==1
def q(n):
    return int(n.numerator)*pow(int(n.denominator),-1,N)%N
Y=-q(coef[0])*pow(q(coef[1]),-1,N)%N
assert (70*Y**2-20*Y+1)%N==0
assert gcd(1-4*Y,N)==1

class E:
    def __init__(self,v=0,b=0):
        if isinstance(v,E):self.a,self.b=v.a,v.b
        elif isinstance(v,int):self.a,self.b=v%N,b%N
        else:self.a,self.b=q(v),q(b)
    def __add__(self,v):
        if isinstance(v,Pol):return NotImplemented
        v=E(v);return E(self.a+v.a,self.b+v.b)
    __radd__=__add__
    def __neg__(self):return E(-self.a,-self.b)
    def __sub__(self,v):return self+(-E(v))
    def __rsub__(self,v):return E(v)+(-self)
    def __mul__(self,v):
        if isinstance(v,Pol):return NotImplemented
        v=E(v);return E(self.a*v.a-Y*self.b*v.b,self.b*v.a+self.a*v.b+self.b*v.b)
    __rmul__=__mul__
    def __pow__(self,n):
        ret=E(1);cur=self
        if n<0:cur=1/cur;n=-n
        while n:
            if n%2:ret=ret*cur
            n//=2
            if n:cur=cur*cur
        return ret
    def __truediv__(self,v):
        v=E(v)
        d=v.norm(); c=gcd(d,N)
        if c!=1:
            print('NONUNIT FACTOR',c,'value',v,flush=True)
            raise ZeroDivisionError
        iv=pow(d,-1,N)
        return self*E((v.a+v.b)*iv,-v.b*iv)
    def __rtruediv__(self,v):return E(v)/self
    def __eq__(self,v):
        v=E(v)
        return self.a==v.a and self.b==v.b
    def __bool__(self):return bool(self.a or self.b)
    def norm(self):return (self.a*self.a+self.a*self.b+Y*self.b*self.b)%N
    def __repr__(self):return f'({self.a},{self.b})'

class Pol:
    def __init__(self,x):
        if isinstance(x,Pol):self.c=x.c[:]
        elif isinstance(x,(tuple,list)):self.c=[E(t) for t in x]
        else:self.c=[E(x)]
        while self.c and not self.c[-1]:self.c.pop()
    def __bool__(self):return bool(self.c)
    def __getitem__(self,i):
        if i<0:return self.c[i]
        return self.c[i] if i<len(self.c) else E(0)
    def __call__(self,x):
        if isinstance(x,Pol):r=Pol(0)
        else:r=E(0)
        for a in self.c[::-1]:r=r*x+a
        return r
    def __repr__(self):return f'Pol{self.c}'
    def degree(self):return len(self.c)-1
    def __add__(self,v):
        v=Pol(v);return Pol([self[i]+v[i] for i in range(max(len(self.c),len(v.c)))])
    __radd__=__add__
    def __neg__(self):return Pol([-x for x in self.c])
    def __sub__(self,v):return self+(-Pol(v))
    def __rsub__(self,v):return Pol(v)+(-self)
    def __mul__(self,v):
        v=Pol(v)
        if not self or not v:return Pol(0)
        q=[E(0) for i in range(len(self.c)+len(v.c)-1)]
        for i,a in enumerate(self.c):
            for j,b in enumerate(v.c):q[i+j]=q[i+j]+a*b
        return Pol(q)
    __rmul__=__mul__
    def __truediv__(self,n):
        if isinstance(n,Pol):raise TypeError
        return Pol([a/n for a in self.c])
    def __pow__(self,n):
        y=Pol(1)
        for i in range(n):y=y*self
        return y
    def __divmod__(self,v):
        v=Pol(v);assert v
        c=1/v[-1];r=self
        q=Pol(0)
        while r and r.degree()>=v.degree():
            z=Pol([0 for j in range(r.degree()-v.degree())]+[r[-1]*c])
            q=q+z;r=r-z*v
        return q,r
    def __floordiv__(self,v):
        q,r=divmod(self,v)
        assert not r, (self,v,r)
        return q
    def __mod__(self,v):return divmod(self,v)[1]
    def gcd(self,v):
        a,b=self,v
        while b:a,b=b,a%b
        return a/a[-1]

AA=E(0,1);x=Pol([0,1])
def valA(b):
    v=E(0)
    for t in b.to_list():v=v*AA+E(t)
    return v
def polyA(b):return Pol([valA(b.get((i,),K.zero)) for i in range(b.degree()+1)])
def sc(a):
    g=(4+35*a*(1-a))/72
    c=(1+x)*g
    L=c**3+(a-2)*c**2+(a*a-2*a+E(9)/7)*c+(a**3-2*a*a+E(9)/7*a-E(2)/7)
    p,d1,d2,d3=[L[j] for j in range(4)]
    k=1+2*x-x*x
    z1=d1-2*p+(d2+p)*x+d3*x*x
    z2=2*(d2+2*d3+p)*x**3+(3*d1-4*d2+7*d3-10*p)*x*x+(-8*d1+5*d2-6*d3+15*p)*x+4*d1-2*d2-6*p
    return g,L,p,k,z1,z2
def unit(a):
    assert gcd(a.norm(),N)==1,(a,gcd(a.norm(),N))
def gate(P,D,u,w,k,q):
    sr=(k-1)/(2*u);st=(q-1)/(2*w)
    cc=(st-sr)/(w-u);bb=sr-cc*(2+u);aa=E(1)/2-bb-cc
    ft=-(aa+bb*x+cc*x*x)+(aa*x+bb*x*x/2+cc*x**3/3)
    gt=1-(1+(x-1)/k)+bb+cc*(E(4)/3+(2*(k+1)/(3*k))*(x-1))
    V=ft*D+gt*P
    v=V//((x-1)*(x-(1+u))*(x-(1+w)))

    assert v.degree()==1
    z=-v[0]/v[1]
    for t in (P(z),D(z)):unit(t)
    return z

def main():
    G,P,p,k,K1,Q1=sc(AA)
    G1,PP,r,kk,K2,Q2=sc(1-AA)
    assert G==G1
    for t in (G,p,r,Q1[3],Q2[3]):unit(t)
    FF=polyA(F);VF0=polyA(VF)
    hh=FF.gcd(VF0)

    assert hh.degree()==1
    h=-hh[0]; h1=-h/(1+(1/G-2)*h)
    assert not FF(h) and not VF0(h)
    l,hR=p*h,r*h1
    Q=Q1.gcd(K1-l*k);QR=Q2.gcd(K2-hR*kk)

    assert Q.degree()==QR.degree()==1
    U,V=-Q[0],-QR[0]
    # Record valid scalar pivots, then no additional degree or chart assumptions.
    def reads(gap):
        u=gap;w=2*u
        H=-2+u+4*u*u-u**3
        r=2*u*(3*u-2)/H
        k=k0(u);q=k0(w)+2*r*u
        for t in (u,w,k,q, r):unit(t)
        return w,k,q
    k0=k
    w,_,s=reads(U);wo,_,so=reads(V)
    P=P(x-1);PP=PP(x-1)
    D=2*(p+l*(x-1));DR=2*(r+hR*(x-1))
    for t in (D[1],DR[1]):unit(t)
    a0=AA/G;z=1/G
    rd=-D[0]/D[1];rdr=-DR[0]/DR[1]
    for t in (P(rd),PP(rdr)):unit(t)
    x4=gate(P,D,U,w,k0(U),s)
    y4=gate(PP,DR,V,wo,k0(V),so)
    coords=[E(1),1+U,1+w,x4,z-y4,z-(1+wo),z-(1+V),z-1]
    node=Pol(1)
    for a in coords:node=node*(x-a)
    def mask(f):
        for j in (3,2,1):
            f=(f-(f(rd)/(P(rd)**j))*P**j)//D
        return sum((f[i]*(z**i/(i+1)-2*G*a0**i) for i in range(f.degree()+1)),start=E(0))
    y0,y1,y2=[mask(node*x**j) for j in range(3)]
    zz=y0*y2-y1*y1

    lhs=zz.norm()
    assert gcd(lhs,N)==1
    digits={"compositeModulus":N,"pencilConst":zz.a,"pencilLinear":zz.b,
            "forcedY":Y,"pencilNorm":lhs,"pencilNormInv":pow(lhs,-1,N)}
    li="".join(f"def {k} : ℕ := {v}\n" for k,v in digits.items())
    if "--emit" in sys.argv:
        print(li,end="")
    else:
        src=Path(__file__).resolve().parents[2]/"lean/RKCert/Research/SDIRKEightSingletonPaid.lean"
        text=src.read_text()
        for k,v in digits.items():
            assert f"def {k} : ℕ := {v}\n" in text
        print("all cofactor branches: unit masked nodal determinant")

if __name__=='__main__':
    main()
