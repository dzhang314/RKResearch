#!/usr/bin/env python3
from functools import lru_cache
from itertools import permutations
from math import prod
from pathlib import Path
import json
P=19
C=(13,9,12,5,18,8)

def hull(xs):
    Z=[1]
    for x in xs:
        Z=[-x*Z[0]]+[Z[i-1]-x*Z[i] for i in range(1,len(Z))]+[Z[-1]]
    return Z

def det(A):
    n=len(A)
    return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*
               prod(A[i][j] for i,j in enumerate(p))
               for p in permutations(range(n)))

def setup(T,m):
    z,u,a,b,c,t=T
    div=lambda a,b:a*pow(b%m,-1,m)%m
    M=u*u-4*u+2
    theta=div(1,M)
    E=u**5-11*u**4+42*u**3-62*u**2+34*u-6
    J=5*u**5-46*u**4+148*u**3-191*u**2+90*u-12
    h=div(J,E)
    v=2*u-1
    T=u**3-7*u*u+10*u-2
    rv=div(M*(4*u**3-24*u*u+39*u-17),2*T)
    ys=[a,b,c,v,u,1]
    I=lambda f:sum(div(k*z**j,j+1) for j,k in enumerate(f))%m
    Ks=[I(hull(ys[:i]+ys[i+1:])) for i in range(6)]
    ss=[div(1,prod(y-q for j,q in enumerate(ys) if i!=j)) for i,y in enumerate(ys)]
    bs=[s*k%m for s,k in zip(ss,Ks)]
    wu=(u-h)*div(M,2)*Ks[-2]
    w1=-(1-h)*div(Ks[-1],2)
    W=lambda y:div((u-y)*w1+(y-1)*wu,u-1)
    D=[div(si*W(y),y-h) for si,y in zip(ss,ys)]
    d0=div(W(h),prod(h-y for y in ys))
    vv=[div(W(y),k) for y,k in zip(ys,Ks)]
    v0=div(-sum(d*w for d,w in zip(D,vv)),d0)
    x=z-a; y=z-b
    q=lambda a:((2-t)*a+t-1)%m
    qh=lambda a:((a-1)*(a-1-t))%m
    Jq=lambda a:(div((2-t)*a*a,2)+(t-1)*a)%m
    Jh=lambda a:(div(a**3,3)-div((2+t)*a*a,2)+(1+t)*a)%m
    fg=lambda a:(Jq(a)-q(a))%m
    fh=lambda a:(Jh(a)-qh(a))%m
    ratio=div(vv[1],vv[0])
    e0=I(hull(ys))
    e1=(W(v)-(v-h)*rv*Ks[3])%m
    e2=sum(b*w*w for b,w in zip(bs,vv))%m
    e3=(qh(x)*(fg(y)-ratio*fg(x))-q(x)*(fh(y)-ratio*fh(x)))%m
    eb=lambda seq:seq[:3]+[0]+seq[3:]
    Y=ys[:3]+[h]+ys[3:]
    B=eb(bs)
    F=D[:3]+[d0]+D[3:]
    V=vv[:3]+[v0]+vv[3:]
    R=[B,[b*y for b,y in zip(B,Y)],[b*y*y for b,y in zip(B,Y)],F]
    pivots=dict(theta=theta,h=h,den=E,d0=d0,v0=v0,va=vv[0],vb=vv[1],Qa=q(x),
        qdet=q(x)*qh(y)-q(y)*qh(x),suffix=det([r[3:] for r in R]),t=t,z=z)
    return (e0,e1,e2,e3),{k:v%m for k,v in pivots.items()},(Y,B,F,V,R,q,qh,Jq,Jh,theta,x,y,vv,t,h,Ks,bs)

def jac():
    f,data,_=setup(C,P);assert f==(0,0,0,0)
    M=P*P
    a=setup(C,M)[0]
    J=[[0]*6 for _ in range(4)]
    for k in range(6):
        x=list(C); x[k]+=P
        f=setup(x,M)[0]
        for j in range(4):
            assert (f[j]-a[j])%P==0
            J[j][k]=(f[j]-a[j])//P%P
    return J,data

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


def verify(A,b,m):
    @lru_cache(None)
    def stage(T):
        return tuple(prod(sum(v*w for v,w in zip(row,stage(U))) for U in T)%m for row in A)
    res=lambda T:(density(T)*sum(w*v for w,v in zip(b,stage(T)))-1)%m
    checks=[T for k in range(1,8) for T in trees(k)]
    assert len(set(checks))==85 and all(res(T)==0 for T in checks)
    return res(tuple(() for _ in range(7)))

if __name__=="__main__":
    J,data=jac()
    assert J==[[12,5,8,9,7,0],[17,0,2,18,12,0],[7,3,11,7,12,0],[7,3,6,3,8,14]]
    assert det([[(r[0]+r[2])%P,*r[3:]] for r in J])%P==10
    assert data==dict(theta=17,h=3,den=6,d0=1,v0=15,va=1,vb=13,Qa=1,qdet=12,suffix=4,t=8,z=13)
    row=json.loads(Path(__file__).with_name("f19-arithmetic-affine.json").read_text())
    A,b=row["tableau"],row["b"]
    assert all(row[i]==3 and not any(row[i+1:]) for i,row in enumerate(A))
    assert [i+1 for i,t in enumerate(b) if not t]==[1,2,6]
    assert (13*sum(A[2]))%P==1
    assert verify(A,b,19)==8
    print("The 85 order-seven trees, eighth bush, and affine arithmetic Jacobian check exactly.")
