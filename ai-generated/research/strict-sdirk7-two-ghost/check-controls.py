#!/usr/bin/env python3
from math import prod
from functools import lru_cache
from pathlib import Path
import json
from itertools import permutations
P=19
C=(6,1,9,10)

def hull(xs):
    f=[1]
    for x in xs:f=[-x*f[0]]+[f[i-1]-x*f[i] for i in range(1,len(f))]+[f[-1]]
    return f

def det(A):
    n=len(A)
    return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*
               prod(A[i][j] for i,j in enumerate(p))
               for p in permutations(range(n)))

def setup(T,m,affine):
    if affine:
        z,u,b,d2,t=T
        d=2*u-1
        Y=[z-1,b,d2,0,d,u,1]
    else:
        u,r,s,t=T
        z=2*u
        d=2*u-1
        Y=[u-r,u+r,u-s,u+s,d,u,1]
    div=lambda a,b:a*pow(b%m,-1,m)%m
    M=u*u-4*u+2
    T=u**3-7*u*u+10*u-2
    ratev=div(M*(4*u**3-24*u*u+39*u-17),2*T)
    theta=div(1,M)
    f=lambda x:div(-4+(2*theta-2)*(x-1),3)
    q0=div((u-2)*(u-1)**2,T)
    q1=div(-(u-3)*(u-1)*(2*u-3),T)
    q2=div((u-3)*(u-2)**2,2*T)
    G=lambda y:(q0*(y-1)+q1*(div(y*y,2)-y)+q2*(div(y**3,3)-y*y))%m
    E=lambda y:(-q1+q2*f(y)-theta*(1-y))%m
    I=lambda f:sum(div(v*z**j,j+1) for j,v in enumerate(f))%m
    K=[I(hull(Y[:i]+Y[i+1:])) for i in range(7)]
    inP=[div(1,prod(y-z for j,z in enumerate(Y) if i!=j)) for i,y in enumerate(Y)]
    b=[a*k%m for a,k in zip(inP,K)]
    A=-div(K[6],2); Wu=div(M*K[5],2)
    W=lambda y:div((u-y)*A+(y-1)*Wu,u-1)
    rho0,rho1,rho2=[sum(div(W(y)**2*s*y**j,k) for y,s,k in zip(Y,inP,K))%m for j in range(3)]
    D=[W(y)*s%m for y,s in zip(Y,inP)]
    U=[div(((rho2-rho1*y) if affine else (rho0*y-rho1))*W(y),k) for y,k in zip(Y,K)]
    x=z-Y[0]; y=z-Y[1]
    qg=lambda x:(2-t)*x+t-1
    qH=lambda x:(x-1)*(x-1-t)
    Jq=lambda x:div((2-t)*x*x,2)+(t-1)*x
    JH=lambda x:div(x**3,3)-div((2+t)*x*x,2)+(1+t)*x
    ratio=div(U[1],U[0])
    Fc=lambda p,J,x:J(x)-p(x)
    fw=lambda p,J:Fc(p,J,y)-ratio*Fc(p,J,x)
    C1=(W(d)-ratev*K[4])%m
    C2=(G(Y[3])*K[3]+E(Y[3])*W(Y[3]))%m
    C3=(rho0*rho2-rho1*rho1)%m
    C4=(qH(x)*fw(qg,Jq)-qg(x)*fw(qH,JH))%m
    rows=[b,[a*y for a,y in zip(b,Y)],[a*y*y for a,y in zip(b,Y)],D]
    pv=dict(qPivot=qg(x)%m,forward=(qg(x)*qH(y)-qg(y)*qH(x))%m,
       reverse=det([r[3:] for r in rows])%m,rho0=rho0,va=U[0],b=b)
    return (C1,C2,C3,C4), pv

@lru_cache(None)
def size(t):return 1+sum(map(size,t))
@lru_cache(None)
def density(t):return size(t)*prod(map(density,t))
@lru_cache(None)
def trees(n):
    if n==1:return ((),)
    pool=tuple(t for k in range(1,n) for t in trees(k))
    def pick(start,left):
        if not left:yield ()
        for j in range(start,len(pool)):
            T=pool[j]
            d=left-size(T)
            if d<0:break
            for r in pick(j,d):yield (T,)+r
    return tuple(pick(0,n-1))


def verify(A,b,m,bad):
    @lru_cache(None)
    def stage(T):
        return tuple(prod(sum(v*w for v,w in zip(row,stage(U))) for U in T)%m for row in A)
    res=lambda T:(density(T)*sum(w*v for w,v in zip(b,stage(T)))-1)%m
    checks=[T for k in range(1,8) for T in trees(k)]
    assert len(set(checks))==85 and all(res(T)==0 for T in checks)
    return res(bad)

def jac(C,affine):
    m=19**2; h,piv=setup(C,19,affine)
    assert h==(0,0,0,0)
    a,_=setup(C,m,affine)
    cols=[]
    for i in ((0,2,3,4) if affine else range(4)):
        f=list(C);f[i]+=19
        x,_=setup(f,m,affine)
        assert all((y-j)%19==0 for y,j in zip(x,a))
        cols.append([(y-j)//19%19 for y,j in zip(x,a)])
    print(list(zip(*cols)),det(cols)%19,piv)
    assert det(cols)%19==(8 if affine else 18)

if __name__=='__main__':
    freeze=lambda t:tuple(map(freeze,t))
    for label,aff,C in [('centered',False,(6,1,9,10)),('affine-zero',True,(6,9,13,16,13))]:
        j=json.loads(Path(__file__).with_name(f'f19-{label}-control.json').read_text())
        A,b=j['tableau'],j['b']
        assert verify(A,b,19,freeze(j['eighth_tree']))==(15 if aff else 9)
        jac(C,aff)
