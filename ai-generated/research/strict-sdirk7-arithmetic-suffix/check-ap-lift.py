#!/usr/bin/env python3
"""Exact arithmetic-suffix family, Jacobian and arbitrary finite lift replay."""
from math import prod
from itertools import permutations
from functools import lru_cache
from pathlib import Path
import argparse
import json
BASE=[8,4,9,15,0]
P=19
def hull(xs):
    a=[1]
    for x in xs:
        a=[-x*a[0]]+[a[i-1]-x*a[i] for i in range(1,len(a))]+[a[-1]]
    return a
def det(M):
    return sum(((-1)**sum(i>j for k,i in enumerate(p) for j in p[k+1:]))*
               prod(M[i][j] for i,j in enumerate(p))
               for p in permutations(range(len(M))))
def setup(X,m):
    z,u,a,b,c=X
    div=lambda a,b:a*pow(b%m,-1,m)%m
    y=[a,b,c,2*u-1,u,1]
    M=u*u-4*u+2
    T=u**3-7*u*u+10*u-2
    th=div(1,M)
    f=lambda y:div(-4+(2*th-2)*(y-1),3)
    q0=(u-2)*(u-1)**2
    q1=-(u-3)*(u-1)*(2*u-3)
    q2=div((u-3)*(u-2)**2,2)
    G=lambda c:q0*(c-1)+q1*(div(c*c,2)-c)+q2*(div(c**3,3)-c*c)
    E=lambda c:-q1+q2*f(c)-T*th*(1-c)
    rates=[div(-G(c),E(c)),div(M*(4*u**3-24*u*u+39*u-17),2*T),div(M,2),div(-1,2)]
    I=lambda H:sum(div(k*z**i,i+1) for i,k in enumerate(H))%m
    K=[I(hull(y[:i]+y[i+1:])) for i in range(6)]
    s=[div(1,prod(y[i]-y[j] for j in range(6) if j!=i)) for i in range(6)]
    L=[q*k%m for q,k in zip(rates,K[2:])]
    A=L[3]-2*L[2]+L[1]
    B=L[3]-2*u*L[2]+y[3]*L[1]
    h=div(B,A)
    W=lambda t:div((u-t)*(1-h)*L[3]+(t-1)*(u-h)*L[2],u-1)
    ri=I(hull(y))
    r4=(W(c)-(c-h)*L[0])%m
    beta=[p*q%m for p,q in zip(K,s)]
    D=[div(s[i]*W(y[i]),y[i]-h) for i in range(6)]
    v=[div(W(t),k) for t,k in zip(y,K)]
    d0=div(W(h),prod(h-j for j in y))
    v0=div(-sum(d*r for d,r in zip(D,v)),d0)
    iso=sum(b*q*q for b,q in zip(beta,v))%m
    w=z-h; x=z-a; aff=div(v[0],v0)
    coeff=-(x-w)-(w*x-div(x*x,2))+div(w*w,2)*aff
    K0=x*(x-w)-(div(x**3,3)-div(w*x*x,2))+(div(w**3,3)-div(w**3,2))*aff
    eta=div(-K0,coeff)
    E0=(1-w)*(1-eta)
    tap=div(2*E0-2+w+eta,1+E0)
    x2=1+tap
    g2=(1+2*tap-tap*tap)%m
    head=det([[1,1,1],[1,x2,w],[1,g2,0]])%m
    suffix=det([beta[2:],[bb*yy for bb,yy in zip(beta[2:],y[2:])],[bb*yy*yy for bb,yy in zip(beta[2:],y[2:])],D[2:]])%m
    q=lambda x:(x-w)*(x-eta)%m
    a0=I(hull(y[2:]))
    checks = (ri,r4,iso)
    pivots = {k:x%m for k,x in dict(M=M,T=T,E=E(c),A=A,h=h,delta=d0,v0=v0,c0=a0,
                 qx=q(z-a),first=coeff,tap=tap,eta=eta,helper=1+E0,head=head,suffix=suffix).items()}
    return checks, pivots, (z,u,y,beta,D,h,v,v0,w,tap,x2,g2,q,eta,th,f)
def jac():
    base,data,_=setup(BASE,P)
    assert base==(0,0,0)
    m=P*P
    f=setup(BASE,m)[0]
    rows=[[0]*5 for _ in range(3)]
    for j in range(5):
        X=BASE.copy()
        X[j]+=P
        g=setup(X,m)[0]
        for i in range(3):
            assert (g[i]-f[i])%P==0
            rows[i][j]=(g[i]-f[i])//P%P
    return f,rows,data

def gaussian(rows,m):
    a = [[t%m for t in row] for row in rows]
    n = len(a)
    for j in range(n):
        k = next(k for k in range(j,n) if a[k][j]%P)
        a[j],a[k] = a[k],a[j]
        i = pow(a[j][j],-1,m)
        a[j] = [t*i%m for t in a[j]]
        for k in range(n):
            if k != j:
                i = a[k][j]
                a[k] = [(x-i*y)%m for x,y in zip(a[k],a[j])]
    return [row[-1] for row in a]


def lift(z,u,power):
    assert z%P==8 and u%P==4 and power>=1
    residues, J, pivots = jac()
    assert residues==(209,342,76)
    assert J==[[6,12,11,7,17],[9,14,11,16,13],[12,18,10,12,3]]
    assert pivots==dict(M=2,T=9,E=18,A=5,h=5,delta=10,v0=5,c0=7,qx=16,
                        first=6,tap=10,eta=3,helper=5,head=17,suffix=10)
    J=[row[2:] for row in J]
    assert det(J)%P==3
    X=[z,u,*BASE[2:]]
    m=P
    for _ in range(1,power):
        F=setup(X,m*P)[0]
        assert all(f%m==0 for f in F)
        d=gaussian([j+[-f//m] for j,f in zip(J,F)],P)
        X[2:]=[x+m*y for x,y in zip(X[2:],d)]
        m*=P
    assert setup(X,m)[0]==(0,0,0)
    return X,m,pivots


def build(X,m):
    chk,pivots,data = setup(X,m)
    assert chk==(0,0,0)
    z,u,y,b,D,h,v,v0,w,t,x2,g2,q,eta,theta,f=data
    div=lambda a,b:a*pow(b%m,-1,m)%m
    Jq=lambda x:(div(x**3,3)-div((w+eta)*x*x,2)+w*eta*x)%m
    xs=[(z-a)%m for a in y]
    R=[b,[r*a%m for r,a in zip(b,y)],[r*a*a%m for r,a in zip(b,y)],D]
    targets=[[(r*a)%m for r,a in zip(b,y)],[(div(r*a*a,2)-d)%m for r,a,d in zip(b,y,D)],
             [(div(r*a**3,3)+f(a)*d)%m for r,a,d in zip(b,y,D)],
             [d*(1+theta*(1-a))%m for d,a in zip(D,y)]]
    B=[[int(i==j) for j in range(6)] for i in range(6)]
    Wread=[(Jq(c)-div(Jq(w)*j,v0))%m for c,j in zip(xs,v)]
    B[1][0]=div(Wread[1]-q(xs[1]),q(xs[0]))
    for j in range(5):
        ks=list(range(max(j+1,2),6))
        rows=[[R[i][k] for k in ks]+[(targets[i][j]-R[i][j]-
                    (R[i][1]*B[1][0] if j==0 else 0))%m] for i in range(len(ks))]
        for k,val in zip(ks,gaussian(rows,m)):
            B[k][j]=val
    assert all(sum(R[i][k]*B[k][j] for k in range(6))%m==targets[i][j]
               for i in range(4) for j in range(6))
    assert all(sum(B[i][j]*q(xs[j]) for j in range(6))%m==Wread[i] for i in range(6))
    A=[[0]*9 for _ in range(9)]
    A[0][0]=1
    A[1][:2]=[t,1]
    k=div(w*w-4*w+2,2*t)
    A[2][:3]=[(w-1-k)%m,k,1]
    Ag=(A[2][0]+k*g2)%m
    for i,c in enumerate(xs):
        rhs=(c-sum(B[i]),div(c*c,2)-sum(e*xi for e,xi in zip(B[i],xs)),div(Ag*v[i],v0))
        A[i+3]=gaussian([[1,1,1,rhs[0]],[1,x2,w,rhs[1]],[1,g2,0,rhs[2]]],m)+B[i]
    return [[div(t,z) for t in row] for row in A], [0,0,0]+b


@lru_cache(None)
def size(t):
    return 1+sum(map(size,t))

@lru_cache(None)
def density(t):
    return size(t)*prod(map(density,t))

@lru_cache(None)
def trees(n):
    if n == 1:
        return ((),)
    pool=tuple(t for k in range(1,n) for t in trees(k))
    def pick(start,left):
        if left == 0:
            yield ()
        for j in range(start,len(pool)):
            t=pool[j]
            if size(t)>left:
                break
            for r in pick(j,left-size(t)):
                yield (t,)+r
    return tuple(pick(0,n-1))


def verify(A,b,m):
    @lru_cache(None)
    def stage(T):
        return tuple(prod(sum(A[i][j]*stage(U)[j] for j in range(9)) for U in T)%m
                     for i in range(9))
    residual=lambda T:(density(T)*sum(a*w for a,w in zip(b,stage(T)))-1)%m
    ordered=[T for n in range(1,8) for T in trees(n)]
    assert len(set(ordered))==len(ordered)==85
    assert all(residual(T)==0 for T in ordered)
    bush=tuple(() for _ in range(7))
    assert residual(bush)%P==5
    return residual(bush)


def verify_literal():
    j=json.loads(Path(__file__).with_name("f19-arithmetic-control.json").read_text())
    A,b=j["tableau"],j["b"]
    assert build(BASE,19)==(A,b)
    assert verify(A,b,19)==5
    diag=j["physical_diagonal"]
    assert diag==12 and all(A[i][i]==diag and not any(A[i][i+1:]) for i in range(9))
    assert b[:3]==[0,0,0] and all(b[3:])
    z=j["z"]
    ys=[z*(1-sum(row))%P for row in A]
    assert ys[3:]==[9,15,0,7,4,1] and ys[2]==5 and len(set(ys[2:]))==7
    assert ys[6]==(2*ys[7]-ys[8])%P!=(4-ys[7])%P
    assert all((x+y-z)%P for x in ys[3:6] for y in ys[3:6])


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--power",type=int,default=6)
    parser.add_argument("--z",type=int,default=27)
    parser.add_argument("--u",type=int,default=4)
    args=parser.parse_args()
    verify_literal()
    X,m,pivots=lift(args.z,args.u,args.power)
    A,b=build(X,m)
    residual=verify(A,b,m)
    print(json.dumps(dict(modulus=m,coordinates=X,pivots=pivots,all_85=True,
                          eighth_bush_residual=residual),indent=2))
