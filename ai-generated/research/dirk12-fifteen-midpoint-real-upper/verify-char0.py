#!/usr/bin/env python3
"""All low scalar identities over the exact degree-108 subfield (python-flint)."""
from fractions import Fraction as Q
from itertools import permutations
from math import prod
from pathlib import Path
import flint as fl
import json,sys
from construct import hull,ev as horner,integ,leg,pmul as mul

class Ring:
    def __init__(self,x,f):
        self.x=fl.fmpq_poly(x)
        self.f=[self.poly([Q(*v) for v in row]) for row in f]
        self.zero=fl.fmpq_poly()
        assert self.f[-1]==fl.fmpq_poly([1]) and len(self.f)==4
    def poly(self,p):
        return fl.fmpq_poly([fl.fmpq(Q(q).numerator,Q(q).denominator) for q in p])%self.x
    def __call__(self,v):
        if isinstance(v,Tower):
            assert v.F is self
            return v
        return self.xpol([v])
    def xpol(self,p):return Tower(self,(self.poly(p),self.zero,self.zero))
    def genf(self):return Tower(self,(self.zero,self.poly([1]),self.zero))

class Tower:
    __slots__=('F','p')
    def __init__(self,F,p):self.F=F;self.p=p
    def __bool__(self):return any(bool(c) for c in self.p)
    def __eq__(self,z):return self.p==self.F(z).p
    def __add__(self,z):return Tower(self.F,tuple(a+b for a,b in zip(self.p,self.F(z).p)))
    __radd__=__add__
    def __neg__(self):return Tower(self.F,tuple(-a for a in self.p))
    def __sub__(self,z):return self+-self.F(z)
    def __rsub__(self,z):return self.F(z)+-self
    def __mul__(self,z):
        F=self.F;z=F(z)
        c=[F.zero]*5
        for i,a in enumerate(self.p):
            if a:
                for j,b in enumerate(z.p):
                    if b:c[i+j]=c[i+j]+a*b
        for i in (4,3):
            if c[i]:
                d=c[i]%F.x
                for j,b in enumerate(F.f[:-1]):
                    if b:c[i-3+j]=c[i-3+j]-d*b
        return Tower(F,tuple(a%F.x for a in c[:3]))
    __rmul__=__mul__
    def __truediv__(self,z):
        # This checker never divides by an algebraic field element.
        assert isinstance(z,(int,Q))
        return self*(1/Q(z))
    def __pow__(self,n):
        assert n>=0
        r=self.F(1);x=self
        while n:
            if n%2:r*=x
            n//=2
            if n:x*=x
        return r

def det(A):
    n=len(A)
    return sum(((-1)**sum(a>b for i,a in enumerate(p) for b in p[i+1:]))*prod(A[i][p[i]] for i in range(n))
               for p in permutations(range(n)))
def jp(p,s):return s*horner([v*Q(1,i+1) for i,v in enumerate(p)],s)

def cleared_modes(a,x,y):
    dc=2*x*y-x-3*y*y+2*y;Db=5*x*x-5*x+1
    ep=-(7*x*x-7*x+2)/1260
    P0=hull([0,1,x,y]);F0=integ(P0);F1=integ([0]+P0)
    K1=integ([0,0]+P0)-ep
    ry=-10800*(K1*jp(P0,y)-F1*jp([0]+P0,y))
    rhs=[Db*dc,dc*x**3*(15*x**3-49*x*x+55*x-20),ry]
    M=[[s*leg(j,a*s) for j in (5,6,7)] for s in (1,x,y)]
    dr=det(M)*Db*dc
    rr=[det([[rhs[i] if j==k else M[i][j] for j in range(3)] for i in range(3)]) for k in range(3)]
    dk=Db*x*leg(6,a*x)
    kx=-30*x**3*(x-1)**3
    assert dr and dk
    return dr*dk,[dk*v for v in rr],dr*kx,ep

def verify(src):
    K0=Ring(src['x'],src['f'])
    a=K0(Q(1,2));x=K0.xpol([0,1]);f=K0.genf()
    y,t=[K0.xpol([Q(*v) for v in src[k]]) for k in ('y','t')]
    X=[K0(1),x,y,t,2*f]
    Y=[1-a*z for z in X];fixed=[K0(0),K0(1)]+Y
    P=hull(fixed)
    n=[integ([0]*j+P) for j in range(5)]
    n0,n1,n2,n3,n4=n
    ab=n0*n2;bb=n1*n1
    A0=9*bb-4*ab;B1=3*bb-ab;C1=3*bb-2*ab
    D=A0*B1*C1
    assert A0 and B1 and C1 and n0 and n1 and n2 and ab-bb
    assert not B1*n3-2*n1*n2*n2
    assert not 2*A0*n2*n4-5*B1*n3*n3
    nv=n1*n2
    K=[-3*nv**3,3*nv**2*(C1+2*B1),-nv*(6*B1*C1+A0*B1),D]
    S0=mul(P,K)
    assert not integ(S0) and not integ([0]+S0)
    for j in range(4):
        assert not ((j+2)*(nv*n[j]-C1*n[j+1])-6*(ab-bb)*n[j+1])
    print("exact homogeneous support: both B12 endpoint integrals and four paid Q primitive pairings")
    M=[sum(S0[k+i+1]/(k+1) for k in range(10-i)) for i in range(10)]
    J=[K0(0),K0(0)]+[v/(i+2) for i,v in enumerate(K)]
    theta=[Q(3,20)*n1**4*n2**5*(ab-bb)*(16*ab-9*bb),
           -Q(6,5)*n0*n1**3*n2**5*(ab-bb)*C1]
    # Check the affine coefficient by pseudo-division, not by sampling roots.
    ap=-K[2];bp=K[1]
    lowM=[D*n2-ap*n1+bp*n0,D*n1-ap*n0,D*n0]
    residual=mul([-m for m in lowM],J[1:])
    for i,v in enumerate(theta):residual[i]-=v
    for i in range(len(residual)-1,2,-1):
        lead=residual[i]
        for j in range(i):residual[j]*=D
        for j,v in enumerate(K[:-1]):residual[i-3+j]-=lead*v
    assert not any(residual[:3])
    print("exact affine reverse quartic correction on all three unordered roots")
    Den,rc,k0,ep=cleared_modes(a,x,y)
    z=[]
    for p in X:
        r=p*sum(v*leg(j,a*p) for j,v in zip([5,6,7],rc))
        k=k0*p*leg(6,a*p)
        z.append((r,k))
    def read(F,j):
        rr,kk=z[j]
        q=integ([0]+F)-(ep*F[5] if len(F)==6 else 0)
        return Den*jp(F,X[j])-rr*integ(F)-kk*q
    for j,s in enumerate(X):
        Pj=hull([0]+X[:j+1])
        for deg in range(7-len(Pj)):
            assert not read([0]*deg+Pj,j),(j,deg)
    print("all first-five literal ordinal read fits through scalar input degree five")
    der=[prod(t-z0 for j,z0 in enumerate(fixed) if j!=i+2) for i,t in enumerate(Y)]
    MV=[horner(M,t) for t in Y];JV=[horner(J,t) for t in Y]
    KV=[horner(K,t) for t in Y];TF=[horner(theta,t) for t in Y]
    for i in range(4,-1,-1):
        pro=prod(der[i+1:]);Di=der[i]
        Fcard=prod(X[i]-X[j] for j in range(5) if j!=i)*X[i]
        uu=[]
        for j in range(i,5):
            right=prod(X[i]-X[k] for k in range(j+1,5))
            ex=(pro if j==i else Di*prod(der[k] for k in range(i+1,5) if k!=j))
            Qij=hull([0]+[X[k] for k in range(j+1) if k!=i])
            uu.append(a*read(Qij,j)*MV[j]*Y[j]*right*ex)
        res=KV[i]*sum(uu)-(MV[i]*JV[i]+Y[i]*TF[i])*Fcard*pro*Den
        assert not res, ('nonzero quartic gate',i)
    print("all five physical reverse quartic gates exactly zero in characteristic zero (no quotient-field inversions)")

if __name__=='__main__':
    directory=Path(__file__).parent.parent
    fpath=(Path(sys.argv[1]) if len(sys.argv)>1 else directory/
           'dirk12-fifteen-rank3-invisible-midpoint-zero-fourth-projection'/'field.json')
    verify(json.loads(fpath.read_text()))
