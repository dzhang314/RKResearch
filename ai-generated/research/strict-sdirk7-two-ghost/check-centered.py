#!/usr/bin/env python3
from flint import fmpz_mpoly_ctx,fmpz_poly,nmod_poly
from sympy import primerange
from math import prod
from fractions import Fraction
import time
P=fmpz_mpoly_ctx.get(('u','s'),'lex')
u,s=P.gens()
d=u-1;c=u+s; S=s*s
M=u*u-4*u+2;T=u**3-7*u*u+10*u-2
V=4*u**3-24*u*u+39*u-17
m0,m2,m4,m6=105,35*u*u,21*u**4,15*u**6

A=2*M*T-M*V+T
B=2*M*T*d*d
D=A*(-m4+S*m2)-B*(-m2+S*m0)
N=B*(m4-S*m2)-A*(m6-S*m4)
# Center-affine constraint solves r²=N/D.
L=(m4-S*m2)*D+(-m2+S*m0)*N
Kd=(m6-S*m4)*D+(-m4+S*m2)*N
K0=Kd-d*d*L
Kr=(m6-(d*d+S)*m4+d*d*S*m2)*D
Ks=(m6-d*d*m4)*D+(-m4+d*d*m2)*N
alpha=(M*V-T)*d
beta=M*V+T
q0=2*(u-2)*(u-1)**2
q1=-2*(u-3)*(u-1)*(2*u-3)
q2=(u-3)*(u-2)**2
G=6*q0*(c-1)+3*q1*(c*c-2*c)+2*q2*(c**3-3*c*c)
E=-6*M*q1+q2*(-8*M+4*(1-M)*(c-1))-12*T*(1-c)
fourth=4*T*d*M*G*Ks+E*Kd*(alpha+beta*s)
X=[d*d*D,N,S*D]
Pp=[-prod(X)]+[2*x*prod(x-y for j,y in enumerate(X) if j!=i) for i,x in enumerate(X)]
weights=[p*k for p,k in zip(Pp,[K0,Kd,Kr,Ks])]
cross=[prod(v for j,v in enumerate(weights) if j!=i) for i in range(4)]
L0=cross[0]+2*sum(cross[1:])
L2=2*sum(a*x for a,x in zip(cross[1:],X))
L4=2*sum(a*x*x for a,x in zip(cross[1:],X))
iso=(alpha**2*D*L0+beta**2*L2)*(alpha**2*D*L2+beta**2*L4)-4*alpha**2*beta**2*D*L2**2

def saturate(F):
    denoms=[u,d,M,T,D,N,s,*X,*Pp,*weights,alpha,*[x-y for i,x in enumerate(X) for y in X[i+1:]]]
    for w in denoms:
        while True:
            c=F.gcd(w)
            if all(i==0 for i in c.degrees()):break
            F,r=divmod(F,c)
            assert not r
    return F

def rootless(q):
    for p in primerange(2,600):
        m=nmod_poly(q.coeffs(),p)
        if m.degree()==q.degree() and not m.roots():
            return p
def one(F):
    d=F.to_dict()
    return fmpz_poly([int(d.get((i,0),0)) for i in range(int(F.degrees()[0])+1)])
if __name__=='__main__':
    Xs=saturate(fourth)
    Ys=saturate(iso)
    print('raw',fourth.degrees(),iso.degrees(),'saturated',Xs.degrees(),Ys.degrees(),flush=True)
    assert int(D(6,9))%19==17 and int(N(6,9))%19==17
    assert all(not int(F(6,9))%19 for F in (fourth,iso,Xs,Ys))
    fn=Xs.resultant(Ys,1)
    assert fn.degrees()==(114,0)
    q=one(fn)
    a,f=q.factor()
    assert q==a*prod(p**k for p,k in f)
    assert sorted(p.degree() for p,k in f)==[1,1,3,7,10,75]
    for p,k in f:
        if p.degree()==1:
            r=Fraction(-int(p[0]),int(p[1]))
            assert r in (0,3)
            print('forbidden linear root',r)
        else:
            m=rootless(p)
            assert m
            print('projectively rootless',p.degree(),k,m)
